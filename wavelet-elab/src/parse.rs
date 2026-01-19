//! Parser for annotated Rust programs.
//!
//! This module parses Rust function definitions with capability annotations
//! and elaborates them to our IR. The syntax supports:
//!
//! - Region annotations: `#[cap(A: shrd @ i..N)]` or `#[cap(A: uniq @ i..N)]`
//! - Fence markers: `fence!();` between statements
//! - Const generics for array sizes: `const N: usize`
//!
//! Example:
//! ```ignore
//! #[cap(A: shrd @ i..N)]
//! fn sum<const N: usize>(i: usize, a: i32, A: &[i32; N]) -> i32 {
//!     let c = i < N;
//!     if c {
//!         let val = A[i];
//!         let j = i + 1;
//!         let new_a = a + val;
//!         sum::<N>(j, new_a, A)
//!     } else {
//!         a
//!     }
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

use syn::{self, Attribute, Expr, FnArg, ItemFn, Pat, Stmt, Type};

use crate::ir::{self, ArrayLen, FnDef, FnName, Op, Program, Signedness, Tail, Var};
use crate::logic::cap::CapPattern;
use crate::logic::region::Region;
use crate::logic::semantic::solver::Idx;

static LITERAL_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_literal_name(base: &str) -> String {
    let id = LITERAL_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{}_{}", base, id)
}

/// Context for tracking literal bindings during parsing
struct ParseContext {
    /// Statements accumulated during parsing, including literal bindings
    stmts: Vec<ir::Stmt>,
}

impl ParseContext {
    fn new() -> Self {
        ParseContext { stmts: Vec::new() }
    }

    /// Ensure a literal value is bound to a variable, creating a LetVal if needed.
    /// Returns the variable name that holds the literal.
    fn ensure_literal_bound(&mut self, val: ir::Val) -> String {
        let var_name = match &val {
            ir::Val::Int(n) => fresh_literal_name(&format!("_lit_{}", n)),
            ir::Val::Bool(b) => fresh_literal_name(&format!("_lit_{}", b)),
            ir::Val::Unit => "_unit_literal".to_string(),
        };

        self.stmts.push(ir::Stmt::LetVal {
            var: Var(var_name.clone()),
            val,
            fence: false,
        });

        var_name
    }
}

/// Parse error for the frontend.
#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error: {}", self.message)
    }
}

impl std::error::Error for ParseError {}

impl From<syn::Error> for ParseError {
    fn from(e: syn::Error) -> Self {
        ParseError {
            message: e.to_string(),
        }
    }
}

/// Capability annotation: `#[cap(A: shrd @ i..N)]`
#[derive(Debug, Clone)]
struct CapAnnotation {
    array: String,
    perm: Permission,
    region: RangeExpr,
}

#[derive(Debug, Clone)]
enum Permission {
    Shrd,
    Uniq,
}

/// Range expression: `i..N` or `i..N+1`
#[derive(Debug, Clone)]
struct RangeExpr {
    start: IndexExpr,
    end: IndexExpr,
}

/// Index expression: variable or constant or arithmetic
#[derive(Debug, Clone)]
enum IndexExpr {
    Var(String),
    Const(i64),
    Add(Box<IndexExpr>, Box<IndexExpr>),
    Sub(Box<IndexExpr>, Box<IndexExpr>),
    Mul(Box<IndexExpr>, Box<IndexExpr>),
}

impl IndexExpr {
    fn to_idx(&self) -> Idx {
        match self {
            IndexExpr::Var(v) => Idx::Var(v.clone()),
            IndexExpr::Const(n) => Idx::Const(*n),
            IndexExpr::Add(a, b) => Idx::Add(Box::new(a.to_idx()), Box::new(b.to_idx())),
            IndexExpr::Sub(a, b) => Idx::Sub(Box::new(a.to_idx()), Box::new(b.to_idx())),
            IndexExpr::Mul(a, b) => Idx::Mul(Box::new(a.to_idx()), Box::new(b.to_idx())),
        }
    }
}

/// Parse a capability annotation from attribute.
/// Returns multiple annotations if comma-separated.
fn parse_cap_annotations(attr: &Attribute) -> Result<Vec<CapAnnotation>, ParseError> {
    // Expected format: #[cap(A: shrd @ i..N)] or #[cap(A: shrd @ i..N, B: uniq @ 0..M)]
    // Also supports #[cap] with no arguments (returns empty vec)
    let meta = &attr.meta;

    // For simplicity, parse the token stream manually
    let tokens = quote::quote! { #meta }.to_string();

    // Very basic parsing - in production this should use syn's meta parsing
    // Format: cap ( A : shrd @ i .. N )
    if !tokens.starts_with("cap") {
        return Err(ParseError {
            message: "Expected cap attribute".to_string(),
        });
    }

    // Extract content between parentheses
    // If there are no parentheses (just #[cap]), return empty annotations
    let content = tokens.strip_prefix("cap").unwrap().trim();
    if content.is_empty() {
        // #[cap] with no arguments - this is valid for functions that don't use arrays
        return Ok(Vec::new());
    }

    let content = content
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .ok_or_else(|| ParseError {
            message: "Invalid cap annotation format".to_string(),
        })?;

    // Split by ',' to handle multiple annotations
    let mut annotations = Vec::new();
    for part in content.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        // Split by ':'
        let parts: Vec<&str> = part.splitn(2, ':').collect();
        if parts.len() != 2 {
            return Err(ParseError {
                message: format!("Expected 'array: permission @ range', got: {}", part),
            });
        }

        let array = parts[0].trim().to_string();

        // Split by '@'
        let rest_parts: Vec<&str> = parts[1].splitn(2, '@').collect();
        if rest_parts.len() != 2 {
            return Err(ParseError {
                message: format!("Expected 'permission @ range', got: {}", parts[1]),
            });
        }

        let perm_str = rest_parts[0].trim();
        let perm = match perm_str {
            "shrd" => Permission::Shrd,
            "uniq" => Permission::Uniq,
            _ => {
                return Err(ParseError {
                    message: format!("Unknown permission: {}", perm_str),
                });
            }
        };

        let range_str = rest_parts[1].trim();
        let region = parse_range_expr(range_str)?;

        annotations.push(CapAnnotation {
            array,
            perm,
            region,
        });
    }

    Ok(annotations)
}

/// Parse range expression like "i..N" or "0..N"
fn parse_range_expr(s: &str) -> Result<RangeExpr, ParseError> {
    let parts: Vec<&str> = s.split("..").collect();
    if parts.len() != 2 {
        return Err(ParseError {
            message: format!("Invalid range: {}", s),
        });
    }

    let start = parse_index_expr(parts[0].trim())?;
    let end = parse_index_expr(parts[1].trim())?;

    Ok(RangeExpr { start, end })
}

/// Parse index expression like "i", "10", "i+1", "N-1"
fn parse_index_expr(s: &str) -> Result<IndexExpr, ParseError> {
    // Try to parse as integer
    if let Ok(n) = s.parse::<i64>() {
        return Ok(IndexExpr::Const(n));
    }

    // Try to parse as variable
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Ok(IndexExpr::Var(s.to_string()));
    }

    // Try to parse as addition
    if let Some(pos) = s.find('+') {
        let left = parse_index_expr(s[..pos].trim())?;
        let right = parse_index_expr(s[pos + 1..].trim())?;
        return Ok(IndexExpr::Add(Box::new(left), Box::new(right)));
    }

    // Try to parse as subtraction
    if let Some(pos) = s.rfind('-') {
        // Make sure it's not a negative number
        if pos > 0 {
            let left = parse_index_expr(s[..pos].trim())?;
            let right = parse_index_expr(s[pos + 1..].trim())?;
            return Ok(IndexExpr::Sub(Box::new(left), Box::new(right)));
        }
    }

    // Try to parse as multiplication
    if let Some(pos) = s.find('*') {
        let left = parse_index_expr(s[..pos].trim())?;
        let right = parse_index_expr(s[pos + 1..].trim())?;
        return Ok(IndexExpr::Mul(Box::new(left), Box::new(right)));
    }

    Err(ParseError {
        message: format!("Cannot parse index expression: {}", s),
    })
}

fn syn_expr_to_index_expr(
    expr: &Expr,
    const_generics: &HashSet<String>,
) -> Result<IndexExpr, ParseError> {
    match expr {
        Expr::Lit(expr_lit) => {
            if let syn::Lit::Int(lit_int) = &expr_lit.lit {
                let value = lit_int.base10_parse::<i64>().map_err(|_| ParseError {
                    message: "Invalid integer literal".to_string(),
                })?;
                Ok(IndexExpr::Const(value))
            } else {
                Err(ParseError {
                    message: "Unsupported literal in array length".to_string(),
                })
            }
        }
        Expr::Path(expr_path) => {
            let ident = expr_path
                .path
                .get_ident()
                .map(|ident| ident.to_string())
                .ok_or_else(|| ParseError {
                    message: "Unsupported path in array length expression".to_string(),
                })?;
            if const_generics.contains(&ident) {
                Ok(IndexExpr::Var(ident))
            } else {
                Err(ParseError {
                    message: format!(
                        "Unsupported array length expression (unknown const generic): {}",
                        ident
                    ),
                })
            }
        }
        Expr::Binary(expr_binary) => {
            let lhs = syn_expr_to_index_expr(&expr_binary.left, const_generics)?;
            let rhs = syn_expr_to_index_expr(&expr_binary.right, const_generics)?;
            match expr_binary.op {
                syn::BinOp::Add(_) => Ok(IndexExpr::Add(Box::new(lhs), Box::new(rhs))),
                syn::BinOp::Sub(_) => Ok(IndexExpr::Sub(Box::new(lhs), Box::new(rhs))),
                syn::BinOp::Mul(_) => Ok(IndexExpr::Mul(Box::new(lhs), Box::new(rhs))),
                _ => Err(ParseError {
                    message: "Unsupported operator in array length expression".to_string(),
                }),
            }
        }
        Expr::Paren(expr_paren) => syn_expr_to_index_expr(&expr_paren.expr, const_generics),
        Expr::Group(expr_group) => syn_expr_to_index_expr(&expr_group.expr, const_generics),
        Expr::Block(expr_block) => {
            // Blocks in const-length positions are expected to contain a single expression.
            let stmts = &expr_block.block.stmts;
            if stmts.len() == 1 {
                match &stmts[0] {
                    Stmt::Expr(inner, _) => syn_expr_to_index_expr(inner, const_generics),
                    _ => Err(ParseError {
                        message: "Unsupported block form in array length expression".to_string(),
                    }),
                }
            } else {
                Err(ParseError {
                    message: "Unsupported block in array length expression".to_string(),
                })
            }
        }
        Expr::Unary(expr_unary) => {
            if matches!(expr_unary.op, syn::UnOp::Neg(_)) {
                let inner = syn_expr_to_index_expr(&expr_unary.expr, const_generics)?;
                if let IndexExpr::Const(value) = inner {
                    Ok(IndexExpr::Const(-value))
                } else {
                    Err(ParseError {
                        message: "Unsupported unary minus in array length expression".to_string(),
                    })
                }
            } else {
                Err(ParseError {
                    message: "Unsupported unary operator in array length expression".to_string(),
                })
            }
        }
        _ => Err(ParseError {
            message: "Unsupported array length expression".to_string(),
        }),
    }
}

fn parse_array_length(
    expr: &Expr,
    const_generics: &HashSet<String>,
) -> Result<ArrayLen, ParseError> {
    match expr {
        Expr::Lit(expr_lit) => {
            if let syn::Lit::Int(lit_int) = &expr_lit.lit {
                let value = lit_int.base10_parse::<usize>().map_err(|_| ParseError {
                    message: "Invalid array length".to_string(),
                })?;
                return Ok(ArrayLen::Const(value));
            }
        }
        _ => {}
    }

    let idx_expr = syn_expr_to_index_expr(expr, const_generics)?;
    let idx = idx_expr.to_idx();
    match idx {
        Idx::Const(value) if value >= 0 => Ok(ArrayLen::Const(value as usize)),
        Idx::Const(value) => Ok(ArrayLen::Expr(Idx::Const(value))),
        Idx::Var(name) => Ok(ArrayLen::Symbol(name)),
        other => Ok(ArrayLen::Expr(other)),
    }
}

/// Convert capability annotation to CapPattern
fn cap_annotation_to_pattern(
    ann: &CapAnnotation,
    array_lens: &HashMap<String, ArrayLen>,
) -> Result<CapPattern, ParseError> {
    let region = Region::from_bounded(ann.region.start.to_idx(), ann.region.end.to_idx());
    let len = lookup_array_len(array_lens, &ann.array)?;

    let cap_pattern = match ann.perm {
        Permission::Shrd => CapPattern {
            array: ann.array.clone(),
            len,
            uniq: None,
            shrd: Some(region),
        },
        Permission::Uniq => CapPattern {
            array: ann.array.clone(),
            len,
            uniq: Some(region),
            shrd: None,
        },
    };
    Ok(cap_pattern)
}

/// Parse a function definition and convert to IR.
pub fn parse_fn_def(input: &str) -> Result<FnDef, ParseError> {
    let item_fn: ItemFn = syn::parse_str(input)?;

    // Extract capability annotations
    let mut cap_annotations = Vec::new();
    for attr in &item_fn.attrs {
        if attr.path().is_ident("cap") {
            cap_annotations.extend(parse_cap_annotations(attr)?);
        }
    }

    // Extract function name
    let fn_name = FnName(item_fn.sig.ident.to_string());

    // Extract const generics for array sizes
    let mut const_generics = HashSet::new();
    let mut const_generic_names = Vec::new();
    for param in &item_fn.sig.generics.params {
        if let syn::GenericParam::Const(c) = param {
            // Use a placeholder size of 10 for all const generics
            // The actual value doesn't matter for type checking, as we use symbolic reasoning
            let name = c.ident.to_string();
            const_generics.insert(name.clone());
            const_generic_names.push(name);
        }
    }

    // Extract parameters - separate scalars and arrays
    let mut scalar_params = Vec::new();
    let mut array_params = Vec::new();

    for input in &item_fn.sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            let var_name = extract_var_name(&pat_type.pat)?;
            let ty = convert_type(&pat_type.ty, &const_generics)?;
            if matches!(ty, ir::Ty::RefShrd { .. } | ir::Ty::RefUniq { .. }) {
                array_params.push((Var(var_name), ty));
            } else {
                scalar_params.push((Var(var_name), ty));
            }
        }
    }

    // Add const generics as scalar parameters (needed for comparisons like i < N)
    for name in const_generic_names {
        scalar_params.push((Var(name), ir::Ty::Int(Signedness::Unsigned)));
    }

    // Combine: scalars first, then arrays (required by type checker)
    let mut params = scalar_params;
    params.extend(array_params);

    // Extract return type
    let return_ty = match &item_fn.sig.output {
        syn::ReturnType::Default => ir::Ty::Unit,
        syn::ReturnType::Type(_, ty) => convert_type(ty, &const_generics)?,
    };

    // Collect array variable names and their lengths for tail call reordering
    let mut array_lens: HashMap<String, ArrayLen> = HashMap::new();
    for (var, ty) in &params {
        if let ir::Ty::RefShrd { len, .. } | ir::Ty::RefUniq { len, .. } = ty {
            array_lens.insert(var.0.clone(), len.clone());
        }
    }

    // Convert capability annotations to patterns
    let mut caps = Vec::new();
    for ann in &cap_annotations {
        caps.push(cap_annotation_to_pattern(ann, &array_lens)?);
    }

    // Parse body with const generics and array metadata
    let body = parse_block(&item_fn.block, &array_lens)?;

    Ok(FnDef {
        name: fn_name,
        params,
        caps,
        returns: return_ty,
        body,
    })
}

/// Parse a source string containing one or more function definitions into a [`Program`].
///
/// Functions that are not annotated with capabilities are still included; non-function
/// items are ignored. Any parsing error from one of the functions aborts the whole
/// process and returns the corresponding [`ParseError`].
pub fn parse_program(input: &str) -> Result<Program, ParseError> {
    let file = syn::parse_file(input)?;
    let mut program = Program::new();

    for item in file.items {
        if let syn::Item::Fn(item_fn) = item {
            let tokens = quote::quote!(#item_fn).to_string();
            let fn_def = parse_fn_def(&tokens)?;
            program.add_fn(fn_def);
        }
    }

    Ok(program)
}

/// Extract variable name from pattern
fn extract_var_name(pat: &Pat) -> Result<String, ParseError> {
    match pat {
        Pat::Ident(pat_ident) => Ok(pat_ident.ident.to_string()),
        _ => Err(ParseError {
            message: "Expected simple variable pattern".to_string(),
        }),
    }
}

/// Convert syn Type to our IR Type
fn convert_type(ty: &Type, const_generics: &HashSet<String>) -> Result<ir::Ty, ParseError> {
    match ty {
        Type::Path(type_path) => {
            let ident = &type_path.path.segments.last().unwrap().ident;
            match ident.to_string().as_str() {
                "u32" | "usize" => Ok(ir::Ty::Int(Signedness::Unsigned)),
                "i32" | "isize" => Ok(ir::Ty::Int(Signedness::Signed)),
                "bool" => Ok(ir::Ty::Bool),
                _ => Err(ParseError {
                    message: format!("Unknown type: {}", ident),
                }),
            }
        }
        Type::Reference(type_ref) => {
            // &[T; N] or &mut [T; N]
            let is_mut = type_ref.mutability.is_some();

            if let Type::Array(arr) = &*type_ref.elem {
                let elem_ty = convert_type(&arr.elem, const_generics)?;

                // Extract length
                let len = parse_array_length(&arr.len, const_generics)?;

                if is_mut {
                    Ok(ir::Ty::RefUniq {
                        elem: Box::new(elem_ty),
                        len,
                    })
                } else {
                    Ok(ir::Ty::RefShrd {
                        elem: Box::new(elem_ty),
                        len,
                    })
                }
            } else {
                Err(ParseError {
                    message: "Expected array type in reference".to_string(),
                })
            }
        }
        Type::Tuple(type_tuple) => {
            if type_tuple.elems.is_empty() {
                Ok(ir::Ty::Unit)
            } else {
                Err(ParseError {
                    message: "Tuple types not supported".to_string(),
                })
            }
        }
        _ => Err(ParseError {
            message: "Unsupported type".to_string(),
        }),
    }
}

/// Parse a block into an Expr
fn parse_block(
    block: &syn::Block,
    array_lens: &HashMap<String, ArrayLen>,
) -> Result<ir::Expr, ParseError> {
    let mut ctx = ParseContext::new();
    let mut tail = None;

    for (i, stmt) in block.stmts.iter().enumerate() {
        let is_last = i == block.stmts.len() - 1;

        match stmt {
            Stmt::Local(local) => {
                // let binding
                let ir_stmt = parse_local(local, array_lens, &mut ctx)?;
                ctx.stmts.push(ir_stmt);
            }
            Stmt::Macro(macro_stmt) => {
                // Check if it's a fence macro
                if let Some(ident) = macro_stmt.mac.path.get_ident() {
                    if ident == "fence" {
                        // Mark the previous statement as fenced
                        if let Some(last_stmt) = ctx.stmts.last_mut() {
                            mark_stmt_as_fenced(last_stmt);
                        }
                    } else {
                        return Err(ParseError {
                            message: format!("Unsupported macro: {}", ident),
                        });
                    }
                } else {
                    return Err(ParseError {
                        message: "Unsupported macro".to_string(),
                    });
                }
            }
            Stmt::Expr(expr, semi) => {
                // Expression with or without semicolon
                if is_fence_marker(expr) {
                    // fence!(); - mark the previous statement as fenced
                    if let Some(last_stmt) = ctx.stmts.last_mut() {
                        mark_stmt_as_fenced(last_stmt);
                    }
                } else if semi.is_some() {
                    // Expression with semicolon - regular statement
                    let ir_stmt = parse_expr_stmt(expr, array_lens, &mut ctx)?;
                    ctx.stmts.push(ir_stmt);
                } else {
                    // Expression without semicolon - this is the tail (if last)
                    if is_last {
                        // Check if it's unit ()
                        if matches!(expr, Expr::Tuple(t) if t.elems.is_empty()) {
                            // Don't set tail, let the default unit handling below kick in
                        } else {
                            tail = Some(parse_tail_expr(expr, array_lens, &mut ctx)?);
                        }
                    } else {
                        let ir_stmt = parse_expr_stmt(expr, array_lens, &mut ctx)?;
                        ctx.stmts.push(ir_stmt);
                    }
                }
            }
            _ => {
                return Err(ParseError {
                    message: "Unsupported statement type".to_string(),
                });
            }
        }
    }

    let tail = if let Some(t) = tail {
        t
    } else {
        // No explicit tail - bind unit and return it
        let unit_var = Var("_unit_ret".to_string());
        ctx.stmts.push(ir::Stmt::LetVal {
            var: unit_var.clone(),
            val: ir::Val::Unit,
            fence: false,
        });
        Tail::RetVar(unit_var)
    };

    Ok(ir::Expr {
        stmts: ctx.stmts,
        tail,
    })
}

fn lookup_array_len(
    array_lens: &HashMap<String, ArrayLen>,
    array: &str,
) -> Result<ArrayLen, ParseError> {
    array_lens.get(array).cloned().ok_or_else(|| ParseError {
        message: format!("Unknown array variable: {}", array),
    })
}

/// Check if expression is fence!()
fn is_fence_marker(expr: &Expr) -> bool {
    if let Expr::Macro(expr_macro) = expr {
        if let Some(ident) = expr_macro.mac.path.get_ident() {
            return ident == "fence";
        }
    }
    false
}

/// Mark a statement as fenced
fn mark_stmt_as_fenced(stmt: &mut ir::Stmt) {
    match stmt {
        ir::Stmt::LetVal { fence, .. }
        | ir::Stmt::LetOp { fence, .. }
        | ir::Stmt::LetCall { fence, .. } => *fence = true,
    }
}

/// Parse a local statement (let binding)
/// Parse a local statement (let binding)
fn parse_local(
    local: &syn::Local,
    array_lens: &HashMap<String, ArrayLen>,
    ctx: &mut ParseContext,
) -> Result<ir::Stmt, ParseError> {
    let var_name = extract_var_name(&local.pat)?;

    if let Some(init) = &local.init {
        let expr = &init.expr;

        // Check what kind of expression this is
        if let Some(op_stmt) = try_parse_as_op(var_name.clone(), expr, array_lens, ctx)? {
            return Ok(op_stmt);
        }

        // Otherwise, it's a simple value binding
        if let Some(val) = try_parse_as_val(expr)? {
            return Ok(ir::Stmt::LetVal {
                var: Var(var_name),
                val,
                fence: false,
            });
        }

        // Check for cast expressions - provide a helpful error
        if let Expr::Cast(cast_expr) = expr.as_ref() {
            // Try to extract the variable name from the source for a better error message
            let source_hint = if let Expr::Path(path) = cast_expr.expr.as_ref() {
                path.path
                    .segments
                    .last()
                    .map(|s| format!(" (try using '{}' directly)", s.ident))
                    .unwrap_or_default()
            } else {
                String::new()
            };

            return Err(ParseError {
                message: format!(
                    "Standalone cast bindings like 'let {} = expr as T' are not supported. \
                     Type casts are treated as noops and only work inline in operations. \
                     Remove the cast{}.",
                    var_name, source_hint
                ),
            });
        }
    }

    Err(ParseError {
        message: format!("Cannot parse local binding: {}", var_name),
    })
}

/// Try to parse expression as an operation
fn try_parse_as_op(
    result_var: String,
    expr: &Expr,
    array_lens: &HashMap<String, ArrayLen>,
    ctx: &mut ParseContext,
) -> Result<Option<ir::Stmt>, ParseError> {
    match expr {
        Expr::Unary(unary_expr) => {
            // Unary operators: currently only support ! (not)
            match unary_expr.op {
                syn::UnOp::Not(_) => {
                    let var = extract_var_from_expr(&unary_expr.expr, ctx)?;
                    Ok(Some(ir::Stmt::LetOp {
                        vars: vec![Var(var), Var(result_var)],
                        op: Op::Not,
                        fence: false,
                    }))
                }
                _ => Ok(None),
            }
        }
        Expr::Binary(bin_expr) => {
            let left = extract_var_from_expr(&bin_expr.left, ctx)?;
            let right = extract_var_from_expr(&bin_expr.right, ctx)?;

            let op = match bin_expr.op {
                syn::BinOp::Add(_) => Op::Add,
                syn::BinOp::Sub(_) => Op::Sub,
                syn::BinOp::Mul(_) => Op::Mul,
                syn::BinOp::Div(_) => Op::Div,
                syn::BinOp::BitAnd(_) => Op::BitAnd,
                syn::BinOp::BitOr(_) => Op::BitOr,
                syn::BinOp::BitXor(_) => Op::BitXor,
                syn::BinOp::Shl(_) => Op::Shl,
                syn::BinOp::Shr(_) => Op::Shr,
                syn::BinOp::Lt(_) => Op::LessThan,
                syn::BinOp::Le(_) => Op::LessEqual,
                syn::BinOp::Eq(_) => Op::Equal,
                syn::BinOp::Ne(_) => Op::NotEqual,
                syn::BinOp::And(_) => Op::And,
                syn::BinOp::Or(_) => Op::Or,
                _ => {
                    return Ok(None);
                }
            };

            Ok(Some(ir::Stmt::LetOp {
                vars: vec![Var(left), Var(right), Var(result_var)],
                op,
                fence: false,
            }))
        }
        Expr::Index(index_expr) => {
            // Array indexing: A[i] becomes load(A, i)
            let array = extract_var_from_expr(&index_expr.expr, ctx)?;
            let index = extract_var_from_expr(&index_expr.index, ctx)?;

            let len = lookup_array_len(array_lens, &array)?;

            Ok(Some(ir::Stmt::LetOp {
                vars: vec![Var(result_var)],
                op: Op::Load {
                    array: Var(array),
                    index: Var(index),
                    len,
                },
                fence: false,
            }))
        }
        Expr::Call(call_expr) => {
            // Function call (with optional turbofish generics). Reorder arguments so
            // that scalar values precede arrays, and append const-generic parameters
            // to match the checker's expected layout.
            let (func_name, generic_args) = extract_func_name_and_generics(&call_expr.func)?;

            let mut scalar_args = Vec::new();
            let mut array_args = Vec::new();
            for arg in &call_expr.args {
                let var_name = extract_var_from_expr(arg, ctx)?;
                if array_lens.contains_key(&var_name) {
                    array_args.push(Var(var_name));
                } else {
                    scalar_args.push(Var(var_name));
                }
            }

            let mut args = scalar_args;
            args.extend(generic_args.into_iter().map(Var));
            args.extend(array_args);

            Ok(Some(ir::Stmt::LetCall {
                vars: vec![Var(result_var)],
                func: FnName(func_name),
                args,
                fence: false,
            }))
        }
        _ => Ok(None),
    }
}

/// Try to parse expression as a literal value
fn try_parse_as_val(expr: &Expr) -> Result<Option<ir::Val>, ParseError> {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            syn::Lit::Int(lit_int) => {
                let n = lit_int.base10_parse::<i64>().map_err(|_| ParseError {
                    message: "Invalid integer literal".to_string(),
                })?;
                Ok(Some(ir::Val::Int(n)))
            }
            syn::Lit::Bool(lit_bool) => Ok(Some(ir::Val::Bool(lit_bool.value))),
            _ => Ok(None),
        },
        Expr::Unary(expr_unary) => {
            if let syn::UnOp::Neg(_) = expr_unary.op {
                if let Expr::Lit(inner_lit) = &*expr_unary.expr {
                    if let syn::Lit::Int(lit_int) = &inner_lit.lit {
                        let n = lit_int.base10_parse::<i64>().map_err(|_| ParseError {
                            message: "Invalid integer literal".to_string(),
                        })?;
                        return Ok(Some(ir::Val::Int(-n)));
                    }
                }
            }
            Ok(None)
        }
        Expr::Tuple(tuple_expr) => {
            if tuple_expr.elems.is_empty() {
                Ok(Some(ir::Val::Unit))
            } else {
                Ok(None)
            }
        }
        _ => Ok(None),
    }
}

/// Parse expression as statement (e.g., assignments, function calls)
fn parse_expr_stmt(
    expr: &Expr,
    array_lens: &HashMap<String, ArrayLen>,
    ctx: &mut ParseContext,
) -> Result<ir::Stmt, ParseError> {
    // Check for function calls (including unit-returning functions)
    if let Expr::Call(call_expr) = expr {
        let (func_name, generic_args) = extract_func_name_and_generics(&call_expr.func)?;

        let mut scalar_args = Vec::new();
        let mut array_args = Vec::new();
        for arg in &call_expr.args {
            let var_name = extract_var_from_expr(arg, ctx)?;
            if array_lens.contains_key(&var_name) {
                array_args.push(Var(var_name));
            } else {
                scalar_args.push(Var(var_name));
            }
        }

        let mut args = scalar_args;
        args.extend(generic_args.into_iter().map(Var));
        args.extend(array_args);

        // Create a dummy variable for the result (may be unit)
        let result_var = Var(fresh_literal_name("_call_result"));

        return Ok(ir::Stmt::LetCall {
            vars: vec![result_var],
            func: FnName(func_name),
            args,
            fence: false,
        });
    }

    // Check for array assignment: A[i] = val
    if let Expr::Assign(assign_expr) = expr {
        if let Expr::Index(index_expr) = &*assign_expr.left {
            let array = extract_var_from_expr(&index_expr.expr, ctx)?;
            let index = extract_var_from_expr(&index_expr.index, ctx)?;

            // Check if right side is a literal - if so, we need to handle it specially
            // For now, just require it to be a variable
            let value = match &*assign_expr.right {
                Expr::Lit(_) => {
                    return Err(ParseError {
                        message: "Array assignment requires value to be bound to a variable first. Use 'let tmp = 0; A[i] = tmp;' instead of 'A[i] = 0;'".to_string(),
                    });
                }
                _ => extract_var_from_expr(&assign_expr.right, ctx)?,
            };

            let len = lookup_array_len(array_lens, &array)?;

            return Ok(ir::Stmt::LetOp {
                vars: vec![],
                op: Op::Store {
                    array: Var(array),
                    index: Var(index),
                    value: Var(value),
                    len,
                },
                fence: false,
            });
        }
        // Regular variable assignment: x = expr
        if let Expr::Path(_) = &*assign_expr.left {
            let var_name = extract_var_from_expr(&assign_expr.left, ctx)?;

            // Check if right side is an operation
            if let Some(stmt) =
                try_parse_as_op(var_name.clone(), &assign_expr.right, array_lens, ctx)?
            {
                return Ok(stmt);
            }

            // Otherwise try as value
            if let Some(val) = try_parse_as_val(&assign_expr.right)? {
                return Ok(ir::Stmt::LetVal {
                    var: Var(var_name),
                    val,
                    fence: false,
                });
            }
        }
    }

    // Check for while loops - desugar to recursive functions
    // For now, reject them as they need special handling
    if let Expr::While(_) = expr {
        return Err(ParseError {
            message: "While loops not yet supported - use recursive functions instead".to_string(),
        });
    }

    Err(ParseError {
        message: format!("Cannot parse expression as statement: {:?}", expr),
    })
}

/// Parse tail expression (if, return, tail call)
fn parse_tail_expr(
    expr: &Expr,
    array_lens: &HashMap<String, ArrayLen>,
    ctx: &mut ParseContext,
) -> Result<Tail, ParseError> {
    match expr {
        Expr::If(if_expr) => {
            let cond = extract_var_from_expr(&if_expr.cond, ctx)?;
            let then_branch = parse_block(&if_expr.then_branch, array_lens)?;

            let else_branch = if let Some((_, else_expr)) = &if_expr.else_branch {
                if let Expr::Block(block_expr) = &**else_expr {
                    parse_block(&block_expr.block, array_lens)?
                } else {
                    return Err(ParseError {
                        message: "Expected block in else branch".to_string(),
                    });
                }
            } else {
                return Err(ParseError {
                    message: "If expression must have else branch".to_string(),
                });
            };

            Ok(Tail::IfElse {
                cond: Var(cond),
                then_e: Box::new(then_branch),
                else_e: Box::new(else_branch),
            })
        }
        Expr::Call(call_expr) => {
            // Tail call - extract function name and handle turbofish generics
            let (func_name, generic_args) = extract_func_name_and_generics(&call_expr.func)?;

            // Collect regular arguments, separating scalars from arrays
            let mut scalar_args: Vec<Var> = Vec::new();
            let mut array_args: Vec<Var> = Vec::new();

            for arg in &call_expr.args {
                let var_name = extract_var_from_expr(arg, ctx)?;

                // Check if this variable is an array using the array_vars set
                if array_lens.contains_key(&var_name) {
                    array_args.push(Var(var_name));
                } else {
                    scalar_args.push(Var(var_name));
                }
            }

            // Build final args: scalars + generics + arrays
            let mut args = scalar_args;
            args.extend(generic_args.into_iter().map(Var));
            args.extend(array_args);

            Ok(Tail::TailCall {
                func: FnName(func_name),
                args,
            })
        }
        Expr::Tuple(tuple_expr) if tuple_expr.elems.is_empty() => {
            // Unit type () - should not happen since we handle empty tail in parse_block
            // But if it does, just return a dummy variable
            Ok(Tail::RetVar(Var("_unit_literal".to_string())))
        }
        Expr::Path(_) | Expr::Lit(_) => {
            // Return variable or literal
            let var_name = extract_var_from_expr(expr, ctx)?;
            Ok(Tail::RetVar(Var(var_name)))
        }
        _ => Err(ParseError {
            message: format!("Unsupported tail expression: {:?}", expr),
        }),
    }
}

/// Extract variable name from expression
fn extract_var_from_expr(expr: &Expr, ctx: &mut ParseContext) -> Result<String, ParseError> {
    match expr {
        Expr::Path(expr_path) => {
            let ident = &expr_path.path.segments.last().unwrap().ident;
            Ok(ident.to_string())
        }
        Expr::Lit(expr_lit) => {
            // For literals, create a binding and return the variable name
            match &expr_lit.lit {
                syn::Lit::Int(lit_int) => {
                    let n = lit_int.base10_parse::<i64>().map_err(|_| ParseError {
                        message: "Invalid integer literal".to_string(),
                    })?;
                    Ok(ctx.ensure_literal_bound(ir::Val::Int(n)))
                }
                syn::Lit::Bool(lit_bool) => {
                    Ok(ctx.ensure_literal_bound(ir::Val::Bool(lit_bool.value)))
                }
                _ => Err(ParseError {
                    message: "Unsupported literal in expression".to_string(),
                }),
            }
        }
        Expr::Paren(paren_expr) => extract_var_from_expr(&paren_expr.expr, ctx),
        Expr::Cast(cast_expr) => {
            // Treat cast as noop - just extract the variable being cast
            extract_var_from_expr(&cast_expr.expr, ctx)
        }
        _ => Err(ParseError {
            message: format!("Expected variable, got: {:?}", expr),
        }),
    }
}

/// Extract function name and generic arguments from call expression
/// Returns (function_name, generic_args_as_var_names)
fn extract_func_name_and_generics(expr: &Expr) -> Result<(String, Vec<String>), ParseError> {
    match expr {
        Expr::Path(expr_path) => {
            let last_segment = expr_path.path.segments.last().unwrap();
            let func_name = last_segment.ident.to_string();

            // Check for generic arguments (turbofish syntax: func::<T>)
            let generic_args = if let syn::PathArguments::AngleBracketed(ref angle_args) =
                last_segment.arguments
            {
                angle_args
                    .args
                    .iter()
                    .filter_map(|arg| {
                        // We only care about const generics like N
                        // These appear as types in the turbofish but are runtime values
                        match arg {
                            syn::GenericArgument::Type(syn::Type::Path(type_path)) => {
                                Some(type_path.path.segments.last().unwrap().ident.to_string())
                            }
                            _ => None,
                        }
                    })
                    .collect()
            } else {
                Vec::new()
            };

            Ok((func_name, generic_args))
        }
        _ => Err(ParseError {
            message: "Expected function name".to_string(),
        }),
    }
}

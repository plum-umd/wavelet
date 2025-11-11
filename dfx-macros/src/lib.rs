use proc_macro::TokenStream;
use quote::quote;
use std::sync::{Mutex, OnceLock};
use syn::{parse_macro_input, ItemFn};

/// Stored representation of a capability-annotated function.
#[derive(Clone)]
struct StoredFunction {
    name: String,
    code: String,
    order: usize,
}

type FunctionRegistry = Vec<StoredFunction>;

static FUNCTION_REGISTRY: OnceLock<Mutex<FunctionRegistry>> = OnceLock::new();

fn registry() -> &'static Mutex<FunctionRegistry> {
    FUNCTION_REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}

fn next_order(existing: &[StoredFunction]) -> usize {
    existing
        .iter()
        .map(|f| f.order)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0)
}

/// Capability annotation macro that runs dfx type checking at compile time.
/// 
/// Usage:
/// ```ignore
/// #[cap(array: shrd @ i..N)]
/// fn my_function<const N: usize>(i: usize, array: &[i32; N]) -> i32 {
///     // ...
/// }
/// ```
/// 
/// This macro will:
/// 1. Parse the capability annotations
/// 2. Run the dfx type checker on the entire program (using check_program_with_options)
/// 3. Emit a compile error if type checking fails
/// 4. Otherwise, pass through the function unchanged
#[proc_macro_attribute]
pub fn cap(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    
    // Store the original function for code generation
    let output_fn = input_fn.clone();
    
    // Convert the function to a string for dfx parsing
    let fn_string = quote! { #input_fn }.to_string();
    
    // Parse the capability annotation
    let attr_string = attr.to_string();
    
    // Reconstruct the annotated function string as dfx expects it
    let annotated_fn = format!("#[cap({})]\n{}", attr_string, fn_string);
    let fn_name = input_fn.sig.ident.to_string();
    let mut registry = registry().lock().expect("registry lock poisoned");

    let order = registry
        .iter()
        .find(|stored| stored.name == fn_name)
        .map(|stored| stored.order)
        .unwrap_or_else(|| next_order(&registry));

    let new_entry = StoredFunction {
        name: fn_name.clone(),
        code: annotated_fn.clone(),
        order,
    };

    let mut candidates: Vec<StoredFunction> = registry
        .iter()
        .filter(|stored| stored.name != fn_name)
        .cloned()
        .collect();
    candidates.push(new_entry.clone());
    candidates.sort_by(|a, b| a.order.cmp(&b.order));

    let program_source = candidates
        .iter()
        .map(|stored| stored.code.as_str())
        .collect::<Vec<_>>()
        .join("\n");

    // Run dfx type checking at compile time for all known annotated functions
    match run_dfx_check(&program_source) {
        Ok(()) => {
            if let Some(existing) = registry.iter_mut().find(|stored| stored.name == fn_name) {
                existing.code = annotated_fn;
                existing.order = order;
            } else {
                registry.push(new_entry);
                registry.sort_by(|a, b| a.order.cmp(&b.order));
            }

            TokenStream::from(quote! { #output_fn })
        }
        Err(err) => {
            // Type checking failed, emit a compile error
            let error_msg = format!("dfx type checking failed: {}", err);
            TokenStream::from(quote! {
                compile_error!(#error_msg);
                #output_fn
            })
        }
    }
}

/// Run dfx type checking on the annotated function
fn run_dfx_check(annotated_fn: &str) -> Result<(), String> {
    use dfx::{parse_program, SemanticLogic};
    use dfx::check::{CheckOptions, check_program_with_options};
    
    // Parse the function
    let program = parse_program(annotated_fn).map_err(|e| format!("Parse error: {}", e))?;
    
    if program.defs.is_empty() {
        return Err("No function definitions found".to_string());
    }
    
    // Run type checking on the entire program
    // This allows functions to call each other and enables mutual recursion
    let logic = SemanticLogic::default();
    let options = CheckOptions::default();
    
    check_program_with_options(&program, &logic, options)
        .map_err(|e| format!("{}", e))?;
    
    Ok(())
}

/// Fence macro for synchronization points
/// 
/// Usage:
/// ```ignore
/// fence!();
/// ```
#[proc_macro]
pub fn fence(_input: TokenStream) -> TokenStream {
    // The fence macro is a no-op in terms of code generation,
    // but it's recognized by the dfx parser for type checking
    TokenStream::from(quote! {
        ()
    })
}

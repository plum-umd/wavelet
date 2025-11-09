use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::ghost::json::{RawExpr, RawFn, RawProg, SyncOp, WithCall, WithSpec};

/// Rewrite a raw program so that every variable is used affinely.
/// Repeated uses are made explicit by inserting `fork` operations.
///
/// This pass assumes that the input program does not
/// have shadowing.
pub fn enforce_affine(prog: RawProg) -> RawProg {
    let names = Rc::new(RefCell::new(NameGenerator::default()));
    let fns = prog
        .fns
        .into_iter()
        .map(|func| enforce_affine_fn(func, Rc::clone(&names)))
        .collect();
    RawProg { fns }
}

fn enforce_affine_fn(func: RawFn, names: Rc<RefCell<NameGenerator>>) -> RawFn {
    let RawFn {
        name,
        params,
        outputs,
        body,
    } = func;

    let usage = compute_use_counts(&body);
    let mut affinizer = Affinizer::new(params.clone(), usage, names);
    let body = affinizer.transform_expr(body);

    RawFn {
        name,
        params,
        outputs,
        body,
    }
}

struct Affinizer {
    remaining: HashMap<String, usize>,
    pool: HashMap<String, VecDeque<String>>,
    names: Rc<RefCell<NameGenerator>>,
}

impl Affinizer {
    fn new(
        params: Vec<String>,
        remaining: HashMap<String, usize>,
        names: Rc<RefCell<NameGenerator>>,
    ) -> Self {
        let mut pool = HashMap::new();
        for param in params {
            pool.insert(param.clone(), VecDeque::from(vec![param]));
        }
        Self {
            remaining,
            pool,
            names,
        }
    }

    fn transform_expr(&mut self, expr: RawExpr) -> RawExpr {
        match expr {
            RawExpr::Ret(values) => {
                let mut ops = Vec::new();
                let new_values = values
                    .into_iter()
                    .map(|v| self.consume_var(&v, &mut ops))
                    .collect();
                wrap_ops(ops, RawExpr::Ret(new_values))
            }
            RawExpr::Tail(values) => {
                let mut ops = Vec::new();
                let new_values = values
                    .into_iter()
                    .map(|v| self.consume_var(&v, &mut ops))
                    .collect();
                wrap_ops(ops, RawExpr::Tail(new_values))
            }
            RawExpr::Op {
                op,
                args,
                rets,
                cont,
            } => {
                let mut ops = Vec::new();
                let new_args = args
                    .into_iter()
                    .map(|arg| self.consume_var(&arg, &mut ops))
                    .collect();

                for ret in &rets {
                    self.pool
                        .entry(ret.clone())
                        .or_insert_with(VecDeque::new)
                        .push_back(ret.clone());
                }

                let cont = self.transform_expr(*cont);
                ops.push(OpNode::new(op, new_args, rets));
                wrap_ops(ops, cont)
            }
            RawExpr::Br { cond, left, right } => {
                let mut ops = Vec::new();
                let cond_alias = self.consume_var(&cond, &mut ops);

                let base_pool = self.pool.clone();
                let left_usage = compute_use_counts(left.as_ref());
                let right_usage = compute_use_counts(right.as_ref());

                let left_expr = self.transform_branch(*left, base_pool.clone(), left_usage);
                let right_expr = self.transform_branch(*right, base_pool, right_usage);

                wrap_ops(
                    ops,
                    RawExpr::Br {
                        cond: cond_alias,
                        left: Box::new(left_expr),
                        right: Box::new(right_expr),
                    },
                )
            }
        }
    }

    fn transform_branch(
        &self,
        expr: RawExpr,
        pool: HashMap<String, VecDeque<String>>,
        remaining: HashMap<String, usize>,
    ) -> RawExpr {
        let mut branch = Affinizer {
            remaining,
            pool,
            names: Rc::clone(&self.names),
        };
        branch.transform_expr(expr)
    }

    fn consume_var(&mut self, var: &str, ops: &mut Vec<OpNode>) -> String {
        let remaining = *self
            .remaining
            .get(var)
            .unwrap_or_else(|| panic!("missing usage information for variable `{}`", var));

        if remaining > 1 {
            self.ensure_supply(var, remaining, ops);
        }

        let queue = self
            .pool
            .entry(var.to_string())
            .or_insert_with(|| VecDeque::from(vec![var.to_string()]));
        let alias = queue
            .pop_front()
            .unwrap_or_else(|| panic!("no available copy of `{}`", var));

        let entry = self.remaining.get_mut(var).expect("entry must exist");
        *entry -= 1;
        if *entry == 0 {
            self.pool.remove(var);
        }

        alias
    }

    fn ensure_supply(&mut self, var: &str, needed: usize, ops: &mut Vec<OpNode>) {
        let (missing, source) = {
            let queue = self
                .pool
                .entry(var.to_string())
                .or_insert_with(|| VecDeque::from(vec![var.to_string()]));

            if queue.len() >= needed {
                return;
            }

            let missing = needed - queue.len();
            let source = queue.pop_front().unwrap_or_else(|| var.to_string());
            (missing, source)
        };

        let outputs = self.fork_outputs(var, missing + 1);
        ops.push(OpNode::fork(source.clone(), outputs.clone()));

        let queue = self
            .pool
            .get_mut(var)
            .expect("queue should exist after insertion");
        for out in outputs.into_iter().rev() {
            queue.push_front(out);
        }
    }

    fn fork_outputs(&self, base: &str, total: usize) -> Vec<String> {
        let mut outputs = Vec::with_capacity(total);
        for _ in 0..total {
            outputs.push(self.fresh_name(base));
        }
        outputs
    }

    fn fresh_name(&self, base: &str) -> String {
        let mut names = self.names.borrow_mut();
        names.fresh(base)
    }
}

struct OpNode {
    op: WithCall,
    args: Vec<String>,
    rets: Vec<String>,
}

impl OpNode {
    fn new(op: WithCall, args: Vec<String>, rets: Vec<String>) -> Self {
        Self { op, args, rets }
    }

    fn fork(source: String, outputs: Vec<String>) -> Self {
        let op = WithCall::Op(WithSpec::Spec {
            ghost: false,
            op: SyncOp::Copy { n: outputs.len() },
        });
        Self {
            op,
            args: vec![source],
            rets: outputs,
        }
    }
}

fn wrap_ops(mut ops: Vec<OpNode>, tail: RawExpr) -> RawExpr {
    let mut expr = tail;
    while let Some(node) = ops.pop() {
        expr = RawExpr::Op {
            op: node.op,
            args: node.args,
            rets: node.rets,
            cont: Box::new(expr),
        };
    }
    expr
}

#[derive(Default)]
struct NameGenerator {
    counters: HashMap<String, usize>,
}

impl NameGenerator {
    fn fresh(&mut self, base: &str) -> String {
        let sanitized: String = base
            .chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect();
        let counter = self.counters.entry(sanitized.clone()).or_insert(0);
        let name = format!("{}_copy{}", sanitized, *counter);
        *counter += 1;
        name
    }
}

pub(crate) fn compute_use_counts(expr: &RawExpr) -> HashMap<String, usize> {
    match expr {
        RawExpr::Ret(values) | RawExpr::Tail(values) => {
            let mut counts = HashMap::new();
            for value in values {
                *counts.entry(value.clone()).or_default() += 1;
            }
            counts
        }
        RawExpr::Op { args, cont, .. } => {
            let mut counts = compute_use_counts(cont);
            for arg in args {
                *counts.entry(arg.clone()).or_default() += 1;
            }
            counts
        }
        RawExpr::Br { cond, left, right } => {
            let left_counts = compute_use_counts(left);
            let right_counts = compute_use_counts(right);
            let mut merged = HashMap::new();
            for (key, val) in left_counts.iter() {
                merged
                    .entry(key.clone())
                    .and_modify(|existing| {
                        if *existing < *val {
                            *existing = *val;
                        }
                    })
                    .or_insert(*val);
            }
            for (key, val) in right_counts.iter() {
                merged
                    .entry(key.clone())
                    .and_modify(|existing| {
                        if *existing < *val {
                            *existing = *val;
                        }
                    })
                    .or_insert(*val);
            }
            *merged.entry(cond.clone()).or_default() += 1;
            merged
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ghost::json::ExportError;
    use crate::ghost::lower::synthesize_ghost_program;
    use crate::parse::parse_program;
    use std::fs;
    use std::path::PathBuf;

    #[test]
    fn inserts_copy_for_duplicate_arguments() {
        let body = RawExpr::Op {
            op: WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: SyncOp::Add,
            }),
            args: vec!["x".into(), "x".into()],
            rets: vec!["y".into()],
            cont: Box::new(RawExpr::Ret(vec!["y".into()])),
        };

        let prog = RawProg {
            fns: vec![RawFn {
                name: "double".into(),
                params: vec!["x".into()],
                outputs: 1,
                body,
            }],
        };

        let affine = enforce_affine(prog);
        let func = &affine.fns[0];

        match &func.body {
            RawExpr::Op {
                op,
                args,
                rets,
                cont,
            } => {
                match op {
                    WithCall::Op(WithSpec::Spec {
                        op: SyncOp::Copy { n },
                        ..
                    }) => {
                        assert_eq!(*n, 2);
                        assert_eq!(args, &["x".to_string()]);
                        assert_eq!(rets, &["x_copy0".to_string(), "x_copy1".to_string()]);
                    }
                    other => panic!("expected fork, found {other:?}"),
                }

                match cont.as_ref() {
                    RawExpr::Op { args, .. } => {
                        assert_eq!(args.len(), 2);
                        assert_ne!(args[0], args[1]);
                        assert!(args.iter().all(|a| a.starts_with("x_copy")));
                    }
                    other => panic!("expected add op after fork, found {other:?}"),
                }
            }
            other => panic!("unexpected body shape {other:?}"),
        }
    }

    #[test]
    fn fork_numbering_is_per_base() {
        let body = RawExpr::Op {
            op: WithCall::Op(WithSpec::Spec {
                ghost: false,
                op: SyncOp::Add,
            }),
            args: vec!["a".into(), "a".into()],
            rets: vec!["a_res".into()],
            cont: Box::new(RawExpr::Op {
                op: WithCall::Op(WithSpec::Spec {
                    ghost: false,
                    op: SyncOp::Mul,
                }),
                args: vec!["b".into(), "b".into()],
                rets: vec!["b_res".into()],
                cont: Box::new(RawExpr::Ret(vec!["a_res".into(), "b_res".into()])),
            }),
        };

        let counts = compute_use_counts(&body);

        let names = Rc::new(RefCell::new(NameGenerator::default()));
        let mut affinizer = Affinizer::new(vec!["a".into(), "b".into()], counts, names);

        let expr = affinizer.transform_expr(body);

        let mut seen = HashMap::new();
        collect_copys(&expr, &mut seen);

        assert_eq!(
            seen.get("a"),
            Some(&vec!["a_copy0".into(), "a_copy1".into()])
        );
        assert_eq!(
            seen.get("b"),
            Some(&vec!["b_copy0".into(), "b_copy1".into()])
        );
    }

    fn collect_copys(expr: &RawExpr, map: &mut HashMap<String, Vec<String>>) {
        match expr {
            RawExpr::Ret(_) | RawExpr::Tail(_) => {}
            RawExpr::Op {
                op,
                args,
                rets,
                cont,
            } => {
                if let WithCall::Op(WithSpec::Spec {
                    op: SyncOp::Copy { .. },
                    ..
                }) = op
                {
                    map.insert(args[0].clone(), rets.clone());
                }
                collect_copys(cont, map);
            }
            RawExpr::Br { left, right, .. } => {
                collect_copys(left, map);
                collect_copys(right, map);
            }
        }
    }

    #[test]
    fn ensures_affine_usage_on_sum_fixture() {
        let program = parse_program(include_str!("../../tests/test_files/sum.rs"))
            .expect("sum fixture should parse");
        let ghost = synthesize_ghost_program(&program);
        let raw = RawProg::try_from(&ghost).expect("ghost to raw conversion should succeed");
        let affine = enforce_affine(raw);

        let mut total_copys = 0;
        for func in &affine.fns {
            let counts = var_usage(&func.body);
            assert!(counts.values().all(|&count| count <= 1));
            total_copys += count_copys(&func.body);
        }
        assert!(total_copys > 0, "expected at least one fork to be inserted");
    }

    #[test]
    fn enforces_affine_for_all_fixtures() {
        let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("test_files");

        for entry in fs::read_dir(&fixtures_dir).expect("fixtures directory should exist") {
            let entry = entry.expect("directory entry should be readable");
            let file_type = entry
                .file_type()
                .expect("fixture metadata should be accessible");
            if !file_type.is_file() {
                continue;
            }
            if entry.path().extension().and_then(|ext| ext.to_str()) != Some("rs") {
                continue;
            }

            let path = entry.path();

            let source = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("failed to read fixture {}: {err}", path.display()));
            let program = parse_program(&source)
                .unwrap_or_else(|err| panic!("failed to parse fixture {}: {err}", path.display()));
            let ghost = synthesize_ghost_program(&program);
            let raw = match RawProg::try_from(&ghost) {
                Ok(raw) => raw,
                Err(ExportError::Unsupported(_)) => continue,
                Err(err) => {
                    panic!(
                        "failed to serialise ghost IR for {}: {err:?}",
                        path.display()
                    )
                }
            };
            let affine = enforce_affine(raw);

            for func in &affine.fns {
                let counts = var_usage(&func.body);
                assert!(
                    counts.values().all(|&count| count <= 1),
                    "affine violation detected in function {} for fixture {}",
                    func.name,
                    path.display()
                );
            }
        }
    }

    fn var_usage(expr: &RawExpr) -> HashMap<String, usize> {
        match expr {
            RawExpr::Ret(values) | RawExpr::Tail(values) => {
                let mut counts = HashMap::new();
                for value in values {
                    *counts.entry(value.clone()).or_default() += 1;
                }
                counts
            }
            RawExpr::Op { args, cont, .. } => {
                let mut counts = var_usage(cont);
                for arg in args {
                    *counts.entry(arg.clone()).or_default() += 1;
                }
                counts
            }
            RawExpr::Br { cond, left, right } => {
                let left_counts = var_usage(left);
                let right_counts = var_usage(right);
                let mut merged = HashMap::new();
                for key in left_counts.keys().chain(right_counts.keys()) {
                    let left_val = left_counts.get(key).copied().unwrap_or(0);
                    let right_val = right_counts.get(key).copied().unwrap_or(0);
                    merged.insert(key.clone(), left_val.max(right_val));
                }
                *merged.entry(cond.clone()).or_default() += 1;
                merged
            }
        }
    }

    fn count_copys(expr: &RawExpr) -> usize {
        match expr {
            RawExpr::Ret(_) | RawExpr::Tail(_) => 0,
            RawExpr::Op { op, cont, .. } => {
                let here = matches!(
                    op,
                    WithCall::Op(WithSpec::Spec {
                        op: SyncOp::Copy { .. },
                        ..
                    })
                ) as usize;
                here + count_copys(cont)
            }
            RawExpr::Br { left, right, .. } => count_copys(left) + count_copys(right),
        }
    }
}

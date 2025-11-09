//! Tests using the parser to check annotated Rust programs

use dfx::SemanticLogic;
use dfx::check::{CheckOptions, check_fn_with_options};
use dfx::env::FnRegistry;
use dfx::ir::FnDef;
use dfx::logic::CapabilityLogic;
use dfx::parse::parse_fn_def;
use quote::quote;
use std::collections::HashMap;
use syn::{Item, parse_file};

// Define the fence macro as a no-op for parsing
#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

fn parse_fixture(code: &str) -> HashMap<String, FnDef> {
    let file = parse_file(code).expect("Failed to parse fixture file");
    file.items
        .into_iter()
        .filter_map(|item| {
            if let Item::Fn(item_fn) = item {
                let name = item_fn.sig.ident.to_string();
                let tokens = quote!(#item_fn);
                let rendered = tokens.to_string();
                let fn_def = parse_fn_def(&rendered)
                    .unwrap_or_else(|err| panic!("Failed to parse function `{}`: {:?}", name, err));
                Some((name, fn_def))
            } else {
                None
            }
        })
        .collect()
}

fn for_each_backend<F>(mut f: F)
where
    F: FnMut(&str, &dyn CapabilityLogic),
{
    let backends: Vec<(&str, Box<dyn CapabilityLogic>)> = vec![
        ("semantic", Box::new(SemanticLogic::default())),
        // ("syntactic", Box::new(SyntacticLogic::default())),
    ];

    for (name, logic) in backends {
        f(name, logic.as_ref());
    }
}

#[test]
fn test_sum_with_parser() {
    let code = include_str!("test_files/sum.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");

    // Add function to registry for recursive calls
    let mut registry = FnRegistry::default();
    registry.0.insert("sum".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_zero_out_with_parser() {
    let code = include_str!("test_files/zero_out.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");

    // Add function to registry for recursive calls
    let mut registry = FnRegistry::default();
    registry.0.insert("zero_out".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_copy_array_with_parser() {
    let code = include_str!("test_files/copy_array.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");

    // Add function to registry for recursive calls
    let mut registry = FnRegistry::default();
    registry.0.insert("copy_array".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_increment_with_parser() {
    let code = include_str!("test_files/increment.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");

    // Add function to registry for recursive calls
    let mut registry = FnRegistry::default();
    registry.0.insert("increment".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        // With fence, this should now pass - the fence prevents capability consumption
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_increment_without_fence_fails() {
    // This test verifies that without fence, the read-modify-write pattern fails
    let code = include_str!("test_files/increment_bad.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");

    // Add function to registry for recursive calls
    let mut registry = FnRegistry::default();
    registry
        .0
        .insert("increment_bad".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        println!("Result ({name}): {:?}", result);
        // This should fail due to capability mismatch
        assert!(
            result.is_err(),
            "Expected type checking to fail without fence ({name})"
        );
    });
}

#[test]
fn test_raw_with_fence() {
    let code = include_str!("test_files/raw.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("raw".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                log_solver_queries: false,
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_raw_without_fence_fails() {
    let code = include_str!("test_files/raw_no_fence.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("raw".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        assert!(
            result.is_err(),
            "Expected type checking to fail without fence ({name}), got {:?}",
            result.err()
        );
    });
}

#[test]
fn test_war_with_fence() {
    let code = include_str!("test_files/war.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("war".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_war_without_fence() {
    let code = include_str!("test_files/war_no_fence.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("war".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        assert!(
            result.is_err(),
            "Expected type checking to fail without fence ({name}), got {:?}",
            result.err()
        );
    });
}

#[test]
fn test_waw_with_fence() {
    let code = include_str!("test_files/waw.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("waw".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_waw_without_fence() {
    let code = include_str!("test_files/waw_no_fence.rs");

    let fn_def = parse_fn_def(code).expect("Failed to parse function");
    let mut registry = FnRegistry::default();
    registry.0.insert("waw".to_string(), fn_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fn_def,
            &registry,
            logic,
            CheckOptions {
                verbose: true,
                ..Default::default()
            },
        );
        assert!(
            result.is_err(),
            "Expected type checking to fail without fence ({name}), got {:?}",
            result.err()
        );
    });
}

#[test]
fn test_nn_relu_with_parser() {
    let defs = parse_fixture(include_str!("test_files/nn_relu.rs"));
    let aux_def = defs
        .get("nn_relu_aux")
        .expect("Missing nn_relu_aux in fixture")
        .clone();
    let top_def = defs
        .get("nn_relu")
        .expect("Missing nn_relu in fixture")
        .clone();

    let mut registry = FnRegistry::default();
    registry
        .0
        .insert("nn_relu_aux".to_string(), aux_def.clone());
    registry.0.insert("nn_relu".to_string(), top_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &top_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_nn_fc_with_parser() {
    let defs = parse_fixture(include_str!("test_files/nn_fc.rs"));
    let row_dot_def = defs
        .get("row_dot")
        .expect("Missing row_dot in fixture")
        .clone();
    let rec_rows_def = defs
        .get("rec_rows")
        .expect("Missing rec_rows in fixture")
        .clone();
    let fc_def = defs.get("nn_fc").expect("Missing nn_fc in fixture").clone();

    let mut registry = FnRegistry::default();
    registry
        .0
        .insert("row_dot".to_string(), row_dot_def.clone());
    registry
        .0
        .insert("rec_rows".to_string(), rec_rows_def.clone());
    registry.0.insert("nn_fc".to_string(), fc_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &fc_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

#[test]
fn test_dmv_with_parser() {
    let defs = parse_fixture(include_str!("test_files/dmv.rs"));
    let dot_def = defs
        .get("cal_dot_product")
        .expect("Missing cal_dot_product in fixture")
        .clone();
    let mv_def = defs
        .get("mv_mul")
        .expect("Missing mv_mul in fixture")
        .clone();
    let dmv_def = defs.get("dmv").expect("Missing dmv in fixture").clone();

    let mut registry = FnRegistry::default();
    registry
        .0
        .insert("cal_dot_product".to_string(), dot_def.clone());
    registry.0.insert("mv_mul".to_string(), mv_def.clone());
    registry.0.insert("dmv".to_string(), dmv_def.clone());

    for_each_backend(|name, logic| {
        let result = check_fn_with_options(
            &dmv_def,
            &registry,
            logic,
            CheckOptions {
                verbose: false,
                ..Default::default()
            },
        );
        assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
    });
}

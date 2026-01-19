//! Tests using the parser to check annotated Rust programs

use dfx::SemanticLogic;
use dfx::check::{CheckOptions, check_fn_with_options};
use dfx::env::FnRegistry;
use dfx::ir::FnDef;
use dfx::logic::syntactic::SyntacticLogic;
use dfx::parse_program;
use std::collections::HashMap;

// Define the fence macro as a no-op for parsing
#[allow(unused_macros)]
macro_rules! fence {
    ($($tt:tt)*) => {};
}

fn parse_fixture(code: &str) -> HashMap<String, FnDef> {
    let program = parse_program(code).expect("Failed to parse fixture file");
    program
        .defs
        .into_iter()
        .map(|def| {
            let key = def.name.clone().0;
            (key, def)
        })
        .collect()
}

fn parse_fn_by_name(code: &str, fn_name: &str) -> FnDef {
    let program =
        parse_program(code).unwrap_or_else(|err| panic!("Failed to parse program: {:?}", err));
    program
        .defs
        .into_iter()
        .find(|def| def.name.0 == fn_name)
        .unwrap_or_else(|| panic!("Missing function `{}` in input", fn_name))
}

macro_rules! with_backends {
    (($name:ident, $logic:ident) => $body:block) => {{
        let $name = "semantic";
        let semantic_logic = SemanticLogic::default();
        let $logic = &semantic_logic;
        $body
    }
    {
        let $name = "syntactic";
        let syntactic_logic = SyntacticLogic::default();
        let $logic = &syntactic_logic;
        $body
    }};
}

macro_rules! single_fn_parser_test_ok {
    ($test_name:ident, $file:expr, $fn_name:expr, $opts:expr) => {
        #[test]
        fn $test_name() {
            let code = include_str!($file);
            let fn_def = parse_fn_by_name(code, $fn_name);
            let mut registry = FnRegistry::default();
            registry.insert(fn_def.clone());
            let options: CheckOptions = $opts;
            with_backends!((name, logic) => {
                let result = check_fn_with_options(&fn_def, &registry, logic, options);
                assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
            });
        }
    };
}

macro_rules! single_fn_parser_test_err {
    ($test_name:ident, $file:expr, $fn_name:expr, $opts:expr, $debug:expr) => {
        #[test]
        fn $test_name() {
            let code = include_str!($file);
            let fn_def = parse_fn_by_name(code, $fn_name);
            let mut registry = FnRegistry::default();
            registry.insert(fn_def.clone());
            let options: CheckOptions = $opts;
            with_backends!((name, logic) => {
                let result = check_fn_with_options(&fn_def, &registry, logic, options);
                if $debug {
                    println!("Result ({name}): {:?}", result);
                }
                assert!(
                    result.is_err(),
                    "Expected type checking to fail ({name}), got {:?}",
                    result
                );
            });
        }
    };
}

macro_rules! parser_case {
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = ok, options = $opts:expr $(,)?) => {
        single_fn_parser_test_ok!($test_name, $file, $fn_name, $opts);
    };
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = ok $(,)?) => {
        parser_case!(
            $test_name,
            file = $file,
            fn = $fn_name,
            expect = ok,
            options = CheckOptions::default()
        );
    };
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = err, options = $opts:expr, debug = $debug:expr $(,)?) => {
        single_fn_parser_test_err!($test_name, $file, $fn_name, $opts, $debug);
    };
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = err, options = $opts:expr $(,)?) => {
        parser_case!(
            $test_name,
            file = $file,
            fn = $fn_name,
            expect = err,
            options = $opts,
            debug = false
        );
    };
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = err, debug = $debug:expr $(,)?) => {
        parser_case!(
            $test_name,
            file = $file,
            fn = $fn_name,
            expect = err,
            options = CheckOptions::default(),
            debug = $debug
        );
    };
    ($test_name:ident, file = $file:expr, fn = $fn_name:expr, expect = err $(,)?) => {
        parser_case!(
            $test_name,
            file = $file,
            fn = $fn_name,
            expect = err,
            options = CheckOptions::default(),
            debug = false
        );
    };
}

macro_rules! fixture_parser_test {
    ($test_name:ident, file = $file:expr, entry = $entry:expr, extra = [$($extra:expr),* $(,)?], options = $opts:expr, backends = [$($backend:expr),+ $(,)?] $(,)?) => {
        #[test]
        fn $test_name() {
            let defs = parse_fixture(include_str!($file));
            let mut registry = FnRegistry::default();
            let top_def = defs
                .get($entry)
                .unwrap_or_else(|| panic!("Missing {} in fixture", $entry))
                .clone();
            registry.insert(top_def.clone());
            $(
                let def = defs
                    .get($extra)
                    .unwrap_or_else(|| panic!("Missing {} in fixture", $extra))
                    .clone();
                registry.insert(def);
            )*
            let options: CheckOptions = $opts;
            let allowed_backends = [$( $backend ),+];
            with_backends!((name, logic) => {
                if allowed_backends.contains(&name) {
                    // Check extra functions
                    $(
                        let extra_def = defs.get($extra).unwrap();
                        let extra_result = check_fn_with_options(extra_def, &registry, logic, options);
                        assert!(extra_result.is_ok(), "{name} backend failed for {}: {:?}", $extra, extra_result.err());
                    )*
                    // Check entry function
                    let result = check_fn_with_options(&top_def, &registry, logic, options);
                    assert!(result.is_ok(), "{name} backend failed: {:?}", result.err());
                }
            });
        }
    };
    ($test_name:ident, file = $file:expr, entry = $entry:expr, extra = [$($extra:expr),* $(,)?], backends = [$($backend:expr),+ $(,)?] $(,)?) => {
        fixture_parser_test!(
            $test_name,
            file = $file,
            entry = $entry,
            extra = [$($extra),*],
            options = CheckOptions::default(),
            backends = [$($backend),+],
        );
    };
    ($test_name:ident, file = $file:expr, entry = $entry:expr, extra = [$($extra:expr),* $(,)?], options = $opts:expr $(,)?) => {
        fixture_parser_test!(
            $test_name,
            file = $file,
            entry = $entry,
            extra = [$($extra),*],
            options = $opts,
            backends = ["semantic", "syntactic"],
        );
    };
    ($test_name:ident, file = $file:expr, entry = $entry:expr, extra = [$($extra:expr),* $(,)?]) => {
        fixture_parser_test!(
            $test_name,
            file = $file,
            entry = $entry,
            extra = [$($extra),*],
            options = CheckOptions::default(),
            backends = ["semantic", "syntactic"],
        );
    };
}

parser_case!(
    test_sum,
    file = "test_files/sum.rs",
    fn = "sum",
    expect = ok
);

parser_case!(
    test_zero_out,
    file = "test_files/zero_out.rs",
    fn = "zero_out",
    expect = ok,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

parser_case!(
    test_copy_array,
    file = "test_files/copy_array.rs",
    fn = "copy_array",
    expect = ok,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

parser_case!(
    test_increment,
    file = "test_files/increment.rs",
    fn = "increment",
    expect = ok,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

parser_case!(
    test_increment_without_fence_fails,
    file = "test_files/increment_bad.rs",
    fn = "increment_bad",
    expect = err,
    debug = true
);

parser_case!(
    test_raw_with_fence,
    file = "test_files/raw.rs",
    fn = "raw",
    expect = ok,
    options = CheckOptions {
        verbose: true,
        log_solver_queries: false,
    }
);

parser_case!(
    test_raw_without_fence_fails,
    file = "test_files/raw_no_fence.rs",
    fn = "raw_bad",
    expect = err,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

parser_case!(
    test_war_with_fence,
    file = "test_files/war.rs",
    fn = "war",
    expect = ok
);

parser_case!(
    test_war_without_fence_fails,
    file = "test_files/war_no_fence.rs",
    fn = "war_bad",
    expect = err,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

parser_case!(
    test_waw_with_fence,
    file = "test_files/waw.rs",
    fn = "waw",
    expect = ok
);

parser_case!(
    test_waw_without_fence_fails,
    file = "test_files/waw_no_fence.rs",
    fn = "waw_bad",
    expect = err,
    options = CheckOptions {
        verbose: true,
        ..Default::default()
    }
);

fixture_parser_test!(
    test_nn_relu_with_parser,
    file = "test_files/nn_relu.rs",
    entry = "nn_relu",
    extra = ["nn_relu_aux"]
);

fixture_parser_test!(
    test_nn_fc_with_parser,
    file = "test_files/nn_fc.rs",
    entry = "nn_fc",
    extra = ["row_dot", "rec_rows", "clamp_i16"],
    options = CheckOptions {
        verbose: false,
        log_solver_queries: false,
    },
    backends = ["semantic"]
);

fixture_parser_test!(
    test_dmv_with_parser,
    file = "test_files/dmv.rs",
    entry = "dmv",
    extra = ["cal_dot_product", "mv_mul"],
    options = CheckOptions {
        verbose: false,
        log_solver_queries: false,
    },
    backends = ["semantic"],
);

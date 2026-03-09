use std::collections::HashSet;

use crate::ghost::ir::{GhostFnDef, GhostVar};
use crate::ir::Variable;

use super::context::CheckContext;
use super::perm_env::PermissionEnv;
use super::permission::PermExpr;
use super::pretty_print::{render_atom, render_ghost_function, render_perm_expr};

fn current_fn_name(ctx: &CheckContext) -> &str {
    ctx.current_fn_name
        .as_deref()
        .unwrap_or("<unknown function>")
}

pub fn trace_synthesis_function<V: Variable>(verbose: bool, def: &GhostFnDef<V>) {
    if !verbose {
        return;
    }

    println!("function {}:", def.name.0);
    println!("{}", render_ghost_function(def));
}

pub fn trace_synthesis_step(verbose: bool, label: &str) {
    if verbose {
        println!("synthesis step: {label}");
    }
}

pub fn trace_synth_bindings<'a>(
    verbose: bool,
    bindings: &PermissionEnv,
    vars: impl IntoIterator<Item = &'a GhostVar>,
) {
    if !verbose {
        return;
    }

    println!("synthesized permissions:");
    let mut seen = HashSet::new();
    for var in vars {
        if !seen.insert(var.0.as_str()) {
            continue;
        }
        if let Some(binding) = bindings.lookup(var) {
            println!("  synth {} := {}", var.0, render_perm_expr(binding));
        }
    }
    println!();
}

pub fn trace_context(ctx: &CheckContext, stage: &str) {
    if !ctx.verbose {
        return;
    }

    println!("\n=== {} :: {} ===", current_fn_name(ctx), stage);
    print_context_contents(ctx);
}

pub fn print_context_contents(ctx: &CheckContext) {
    if let Some((sync, garb)) = ctx.current_fn_entry_perms() {
        println!("Entry p_sync: {}", render_perm_expr(sync));
        println!("Entry p_garb: {}", render_perm_expr(garb));
    }

    if ctx.penv.len() == 0 {
        println!("Synthesized bindings: <empty>");
    } else {
        println!("Synthesized bindings: {}", ctx.penv.len());
    }

    let atoms: Vec<_> = ctx.phi.iter().collect();
    if atoms.is_empty() {
        println!("Φ: <empty>");
    } else {
        println!("Φ:");
        for atom in atoms {
            println!("  {}", render_atom(atom));
        }
    }

    println!();
}

pub struct ValidationTraceSnapshot {
    phi_len: usize,
}

fn capture_validation_trace(ctx: &CheckContext) -> ValidationTraceSnapshot {
    ValidationTraceSnapshot {
        phi_len: ctx.phi.atoms.len(),
    }
}

fn log_validation_step(ctx: &CheckContext, label: &str) {
    if ctx.verbose {
        println!("\n--- {} :: {label} ---", current_fn_name(ctx));
    }
}

fn print_validation_transition(ctx: &CheckContext, before: &ValidationTraceSnapshot) {
    if !ctx.verbose {
        return;
    }

    let new_atoms = &ctx.phi.atoms[before.phi_len..];
    if new_atoms.is_empty() {
        println!();
        return;
    }

    println!("  Φ:");
    for atom in new_atoms {
        println!("    {}", render_atom(atom));
    }
    println!();
}

pub fn trace_validation_step<F>(
    ctx: &mut CheckContext,
    label: impl Into<String>,
    check: F,
) -> Result<(), String>
where
    F: FnOnce(&mut CheckContext) -> Result<(), String>,
{
    let label = label.into();
    let snapshot = capture_validation_trace(ctx);
    log_validation_step(ctx, &label);
    let result = check(ctx);
    if result.is_ok() {
        print_validation_transition(ctx, &snapshot);
    }
    result
}

fn trace_obligation_start(ctx: &CheckContext, title: &str, details: &[String]) {
    if !ctx.verbose {
        return;
    }

    println!(">>> {} :: {}", current_fn_name(ctx), title);
    for detail in details {
        println!("  {}", detail);
    }
}

fn trace_obligation_success(ctx: &CheckContext) {
    if ctx.verbose {
        println!("  ✓\n");
    }
}

fn trace_obligation_failure(ctx: &CheckContext, error: &str) {
    if ctx.verbose {
        println!("  ✗ {}\n", error);
    }
}

pub fn trace_obligation<F>(
    ctx: &mut CheckContext,
    title: impl Into<String>,
    details: Vec<String>,
    check: F,
) -> Result<(), String>
where
    F: FnOnce(&mut CheckContext) -> Result<(), String>,
{
    let title = title.into();
    trace_obligation_start(ctx, &title, &details);
    match check(ctx) {
        Ok(()) => {
            trace_obligation_success(ctx);
            Ok(())
        }
        Err(err) => {
            trace_obligation_failure(ctx, &err);
            Err(err)
        }
    }
}

fn render_permission_value(label: &str, value: &PermExpr) -> String {
    format!("{}: {}", label, render_perm_expr(value))
}

#[derive(Default)]
pub struct TraceDetails {
    lines: Vec<String>,
}

impl TraceDetails {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn permission(mut self, label: impl Into<String>, value: &PermExpr) -> Self {
        self.lines
            .push(render_permission_value(&label.into(), value));
        self
    }

    pub fn line(mut self, text: impl Into<String>) -> Self {
        self.lines.push(text.into());
        self
    }

    pub fn check(self, condition: impl Into<String>) -> Self {
        self.line(format!("validate: {}", condition.into()))
    }

    pub fn finish(self) -> Vec<String> {
        self.lines
    }
}

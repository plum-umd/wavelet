//! Top-level driver for ghost permission synthesis and validation.

use crate::ghost::ir::GhostProgram;
use crate::ir::Variable;
use crate::logic::semantic::solver::SmtSolver;

use super::synthesis::synthesize_permissions;
use super::validation::validate_synthesized_program;

pub fn check_ghost_program<V: Variable>(program: &GhostProgram<V>) -> Result<(), String> {
    check_ghost_program_with_solver_and_verbose(program, SmtSolver::new(), false)
}

pub fn check_ghost_program_with_solver<V: Variable>(
    program: &GhostProgram<V>,
    solver: SmtSolver,
) -> Result<(), String> {
    check_ghost_program_with_solver_and_verbose(program, solver, false)
}

pub fn check_ghost_program_with_verbose<V: Variable>(
    program: &GhostProgram<V>,
    verbose: bool,
) -> Result<(), String> {
    check_ghost_program_with_solver_and_verbose(program, SmtSolver::new(), verbose)
}

pub fn check_ghost_program_with_solver_and_verbose<V: Variable>(
    program: &GhostProgram<V>,
    solver: SmtSolver,
    verbose: bool,
) -> Result<(), String> {
    if verbose {
        println!("=== Synthesizing ghost permissions ===\n");
    }
    let model = synthesize_permissions(program, verbose)?;

    if verbose {
        println!("\n=== Validating synthesized ghost permissions ===\n");
    }
    validate_synthesized_program(program, &model, solver, verbose)
}

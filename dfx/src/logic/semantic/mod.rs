pub mod solver;

pub use super::cap::{Cap, CapPattern, Delta};
pub use super::region::{Interval, Region};
pub use solver::{Atom, Idx, Phi, PhiSolver, SmtSolver};

use crate::logic::CapabilityLogic;

/// SMT-backed capability logic implementation.
#[derive(Default)]
pub struct SemanticLogic {
    solver: SmtSolver,
}

impl SemanticLogic {
    pub fn new() -> Self {
        Self {
            solver: SmtSolver::new(),
        }
    }

    pub fn with_solver(solver: SmtSolver) -> Self {
        Self { solver }
    }
}

impl CapabilityLogic for SemanticLogic {
    fn solver(&self) -> &dyn PhiSolver {
        &self.solver
    }

    fn cap_leq(&self, phi: &Phi, required: &Cap, available: &Cap) -> bool {
        required.leq(available, phi, &self.solver)
    }

    fn cap_diff(&self, phi: &Phi, available: &Cap, required: &Cap) -> Option<Cap> {
        available.diff(required, phi, &self.solver)
    }

    fn delta_leq(&self, phi: &Phi, required: &Delta, available: &Delta) -> bool {
        required.leq(available, phi, &self.solver)
    }

    fn delta_diff(&self, phi: &Phi, available: &Delta, required: &Delta) -> Option<Delta> {
        available.diff(required, phi, &self.solver)
    }
}

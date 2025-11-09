pub mod solver;

use super::cap::{Cap, Delta};
use super::semantic::solver::{Phi, PhiSolver};
use solver::BasicSolver;

use crate::logic::CapabilityLogic;

/// Default backend mirroring the historical syntactic reasoning.
pub struct SyntacticLogic {
    solver: BasicSolver,
}

impl SyntacticLogic {
    pub fn new() -> Self {
        Self {
            solver: BasicSolver,
        }
    }
}

impl Default for SyntacticLogic {
    fn default() -> Self {
        Self::new()
    }
}

impl CapabilityLogic for SyntacticLogic {
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

pub mod solver;
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
    type Region = super::region::Region;

    fn solver(&self) -> &<Self::Region as crate::logic::cap::RegionModel>::Solver {
        &self.solver
    }
}

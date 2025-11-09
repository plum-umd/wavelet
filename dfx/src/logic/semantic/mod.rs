pub mod region_set;
pub mod solver;

pub use super::cap::{Cap, CapPattern, Delta};
pub use super::region::{Interval, Region};
pub use region_set::{RegionSetExpr, check_equivalent, check_subset, overlaps};
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
    type Region = RegionSetExpr;

    fn solver(&self) -> &<Self::Region as crate::logic::cap::RegionModel>::Solver {
        &self.solver
    }

    fn set_query_logging(&self, enabled: bool) {
        self.solver.set_query_logging(enabled);
    }
}

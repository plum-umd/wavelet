//! Abstractions for plugging different logical backends into the type checker.
//!
//! The goal is to decouple the core type checking algorithm from the
//! particular reasoning engine that is used for regions, capabilities
//! and propositions.  A [`CapabilityLogic`] implementation packages
//! together the data structures and algorithms used to reason about
//! symbolic indices, region inclusion and capability algebra.  This
//! allows the existing syntactic reasoning to co-exist with future
//! SMT-backed implementations.

use crate::logic::cap::{Cap, Delta, RegionModel};
use crate::logic::semantic::solver::Phi;

pub mod cap;
pub mod region;
pub mod semantic;
pub mod syntactic;

/// Trait implemented by backends that provide reasoning for
/// capabilities and regions.
pub trait CapabilityLogic {
    type Region: RegionModel;

    /// Access the underlying solver for propositional reasoning.  This
    /// is exposed so that existing code that requires explicit access
    /// (for example when instantiating capability patterns) can remain
    /// unchanged while higher-level operations are routed through the
    /// backend.
    fn solver(&self) -> &<Self::Region as RegionModel>::Solver;

    /// Determine whether `required` is a sub-capability of
    /// `available` under the given proposition context.
    fn cap_leq(
        &self,
        phi: &Phi,
        required: &Cap<Self::Region>,
        available: &Cap<Self::Region>,
    ) -> bool {
        required.leq(available, phi, self.solver())
    }

    /// Compute the difference `available \ required`, returning `None`
    /// when the subtraction is not defined (for example because
    /// `required` is not a sub-capability of `available`).
    fn cap_diff(
        &self,
        phi: &Phi,
        available: &Cap<Self::Region>,
        required: &Cap<Self::Region>,
    ) -> Option<Cap<Self::Region>> {
        available.diff(required, phi, self.solver())
    }

    /// Determine whether one capability environment is contained
    /// within another.
    fn delta_leq(
        &self,
        phi: &Phi,
        required: &Delta<Self::Region>,
        available: &Delta<Self::Region>,
    ) -> bool {
        required.leq(available, phi, self.solver())
    }

    /// Compute the environment difference `available \ required`.
    fn delta_diff(
        &self,
        phi: &Phi,
        available: &Delta<Self::Region>,
        required: &Delta<Self::Region>,
    ) -> Option<Delta<Self::Region>> {
        available.diff(required, phi, self.solver())
    }

    /// Enable or disable logging of solver queries.  Backends that do
    /// not emit SMT queries can ignore this hook.
    fn set_query_logging(&self, _enabled: bool) {}
}

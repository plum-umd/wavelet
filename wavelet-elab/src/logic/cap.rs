//! Capability algebra parameterised over an abstract region model.

use std::collections::BTreeMap;
use std::fmt;

use super::region::Region;
use crate::logic::semantic::solver::{Phi, PhiSolver};

/// Trait implemented by data structures that model regions.
pub trait RegionModel: Clone + Default + std::fmt::Debug {
    /// Solver capable of reasoning about propositions for this region model.
    type Solver: PhiSolver<Region = Self>;

    /// Convert a syntactic region into this model.
    fn from_region(region: &Region) -> Self;

    /// Compute the union of two regions.
    fn union(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> Self;

    /// Compute the set difference `self \ other`.
    fn diff(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> Self;

    /// Decide whether `self ⊆ other`.
    fn is_subregion_of(&self, other: &Self, phi: &Phi, solver: &Self::Solver) -> bool;

    /// Determine whether the region is empty under the current context.
    fn is_empty(&self, phi: &Phi, solver: &Self::Solver) -> bool;

    /// Render the region for diagnostics.
    fn display(&self) -> String;

    /// Render the region using contextual simplifications from `phi`.
    fn display_with(&self, phi: &Phi, solver: &Self::Solver) -> String {
        let _ = (phi, solver);
        self.display()
    }
}

/// A capability comprising read-only (`shrd`) and read-write (`uniq`) regions.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Cap<R: RegionModel> {
    pub shrd: R,
    pub uniq: R,
}

impl<R: RegionModel> Cap<R> {
    /// Essentially:
    /// ```text
    /// c₁ ≤ c₂ := c₁.shrd ⊆ (c₂.shrd ∪ c₂.uniq) ∧ c₁.uniq ⊆ c₂.uniq
    /// ```
    pub fn leq(&self, other: &Cap<R>, phi: &Phi, solver: &R::Solver) -> bool {
        let union_shrd = other.shrd.union(&other.uniq, phi, solver);
        let shrd_ok = self.shrd.is_subregion_of(&union_shrd, phi, solver);
        let uniq_ok = self.uniq.is_subregion_of(&other.uniq, phi, solver);
        shrd_ok && uniq_ok
    }

    /// Essentially:
    /// ```text
    /// c₁ \ c₂ :=
    ///   if c₂ ≤ c₁ then
    ///     some { shrd := c₁.shrd ∪ c₂.shrd,
    ///            uniq := c₁.uniq \ (c₂.shrd ∪ c₂.uniq) }
    ///   else
    ///     none
    /// ```
    pub fn diff(&self, other: &Cap<R>, phi: &Phi, solver: &R::Solver) -> Option<Cap<R>> {
        if !other.leq(self, phi, solver) {
            return None;
        }
        let new_shrd = self.shrd.union(&other.shrd, phi, solver);
        let remove = other.shrd.union(&other.uniq, phi, solver);
        let new_uniq = self.uniq.diff(&remove, phi, solver);
        Some(Cap {
            shrd: new_shrd,
            uniq: new_uniq,
        })
    }
}

impl<R: RegionModel> fmt::Display for Cap<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let shrd = self.shrd.display();
        let uniq = self.uniq.display();
        match (shrd.as_str(), uniq.as_str()) {
            (s, u) if s == "<empty>" && u == "<empty>" => write!(f, "<empty>"),
            (s, u) if u == "<empty>" => write!(f, "shrd: {s}"),
            (s, u) if s == "<empty>" => write!(f, "uniq: {u}"),
            (s, u) => write!(f, "shrd: {s}; uniq: {u}"),
        }
    }
}

/// A mapping from array identifiers to capabilities.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Delta<R: RegionModel>(pub BTreeMap<String, Cap<R>>);

impl<R: RegionModel> Delta<R> {
    pub fn leq(&self, other: &Delta<R>, phi: &Phi, solver: &R::Solver) -> bool {
        for (name, cap1) in &self.0 {
            match other.0.get(name) {
                Some(cap2) => {
                    if !cap1.leq(cap2, phi, solver) {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    pub fn diff(&self, other: &Delta<R>, phi: &Phi, solver: &R::Solver) -> Option<Delta<R>> {
        if !other.leq(self, phi, solver) {
            return None;
        }
        let mut result = BTreeMap::new();
        for (name, cap1) in &self.0 {
            if let Some(cap2) = other.0.get(name) {
                let diff = cap1.diff(cap2, phi, solver)?;
                result.insert(name.clone(), diff);
            } else {
                result.insert(name.clone(), cap1.clone());
            }
        }
        Some(Delta(result))
    }
}

impl<R: RegionModel> fmt::Display for Delta<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "<empty>");
        }
        let mut first = true;
        write!(f, "{{")?;
        for (name, cap) in &self.0 {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}: {}", name, cap)?;
        }
        write!(f, "}}")
    }
}

/// A capability pattern appearing in a function signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapPattern {
    pub array: String,
    pub len: crate::ir::ArrayLen,
    pub uniq: Option<Region>,
    pub shrd: Option<Region>,
}

impl CapPattern {
    pub fn initialize<R: RegionModel>(&self) -> Cap<R> {
        let mut cap = Cap::<R>::default();
        if let Some(uniq) = &self.uniq {
            cap.uniq = R::from_region(uniq);
        }
        if let Some(shrd) = &self.shrd {
            cap.shrd = R::from_region(shrd);
        }
        cap
    }
}

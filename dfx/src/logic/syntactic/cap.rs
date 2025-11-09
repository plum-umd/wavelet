//! Capability algebra for the syntactic backend.

use std::collections::BTreeMap;

use super::phi::{Phi, PhiSolver};
use super::region::Region;

/// A capability comprising read-only (`shrd`) and read-write (`uniq`) regions.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Cap {
    pub shrd: Region,
    pub uniq: Region,
}

impl Cap {
    pub fn leq(&self, other: &Cap, phi: &Phi, solver: &dyn PhiSolver) -> bool {
        let union_shrd = other.shrd.union(&other.uniq, phi, solver);
        let shrd_ok = self.shrd.is_subregion_of(&union_shrd, phi, solver);
        let uniq_ok = self.uniq.is_subregion_of(&other.uniq, phi, solver);
        shrd_ok && uniq_ok
    }

    pub fn diff(&self, other: &Cap, phi: &Phi, solver: &dyn PhiSolver) -> Option<Cap> {
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

/// A mapping from array identifiers to capabilities.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Delta(pub BTreeMap<String, Cap>);

impl Delta {
    pub fn leq(&self, other: &Delta, phi: &Phi, solver: &dyn PhiSolver) -> bool {
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

    pub fn diff(&self, other: &Delta, phi: &Phi, solver: &dyn PhiSolver) -> Option<Delta> {
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

/// A capability pattern appearing in a function signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapPattern {
    pub array: String,
    pub uniq: Option<Region>,
    pub shrd: Option<Region>,
}

impl CapPattern {
    pub fn instantiate(&self, phi: &Phi, solver: &dyn PhiSolver) -> Cap {
        let mut cap = Cap::default();
        if let Some(uniq) = &self.uniq {
            cap.uniq = uniq.clone();
        }
        if let Some(shrd) = &self.shrd {
            cap.shrd = cap.shrd.union(shrd, phi, solver);
        }
        cap
    }
}

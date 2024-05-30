use crate::internal::arena::ArenaId;
use crate::internal::id::{ExpandedVar, VarId};
use crate::{PackageName, Pool, VersionSet};
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};

/// Represents a decision (i.e. an assignment to a solvable) and the level at which it was made
///
/// = 0: undecided
/// > 0: level of decision when the solvable is set to true
/// < 0: level of decision when the solvable is set to false
#[repr(transparent)]
#[derive(Copy, Clone)]
struct DecisionAndLevel(i64);

impl DecisionAndLevel {
    fn undecided() -> DecisionAndLevel {
        DecisionAndLevel(0)
    }

    fn value(self) -> Option<bool> {
        match self.0.cmp(&0) {
            Ordering::Less => Some(false),
            Ordering::Equal => None,
            Ordering::Greater => Some(true),
        }
    }

    fn level(self) -> u32 {
        self.0.unsigned_abs() as u32
    }

    fn with_value_and_level(value: bool, level: u32) -> Self {
        Self(if value { level as i64 } else { -(level as i64) })
    }
}

/// A map of the assignments to solvables.
pub(crate) struct DecisionMap {
    solvables: Vec<DecisionAndLevel>,
    variables: Vec<DecisionAndLevel>,
}

impl DecisionMap {
    pub fn new() -> Self {
        Self {
            solvables: Vec::new(),
            variables: Vec::new(),
        }
    }

    pub fn reset(&mut self, variable: VarId) {
        let (map, idx) = match variable.expand() {
            ExpandedVar::Solvable(s) => (&mut self.solvables, s.to_usize()),
            ExpandedVar::Variable(v) => (&mut self.variables, v as usize),
        };

        if idx < map.len() {
            // SAFE: because we check that the solvable id is within bounds
            unsafe { *map.get_unchecked_mut(idx) = DecisionAndLevel::undecided() };
        }
    }

    pub fn set(&mut self, variable: VarId, value: bool, level: u32) {
        let (map, idx) = match variable.expand() {
            ExpandedVar::Solvable(s) => (&mut self.solvables, s.to_usize()),
            ExpandedVar::Variable(v) => (&mut self.variables, v as usize),
        };

        if idx >= map.len() {
            map.resize_with(idx + 1, DecisionAndLevel::undecided);
        }

        // SAFE: because we ensured that vec contains at least the correct number of elements.
        unsafe {
            *map.get_unchecked_mut(idx) = DecisionAndLevel::with_value_and_level(value, level)
        };
    }

    pub fn level(&self, variable: VarId) -> u32 {
        let (map, idx) = match variable.expand() {
            ExpandedVar::Solvable(s) => (&self.solvables, s.to_usize()),
            ExpandedVar::Variable(v) => (&self.variables, v as usize),
        };

        map.get(idx).map_or(0, |d| d.level())
    }

    pub fn value(&self, variable: VarId) -> Option<bool> {
        let (map, idx) = match variable.expand() {
            ExpandedVar::Solvable(s) => (&self.solvables, s.to_usize()),
            ExpandedVar::Variable(v) => (&self.variables, v as usize),
        };

        map.get(idx).and_then(|d| d.value())
    }

    /// Returns an object that can be used to display the contents of the decision map in a human readable fashion.
    #[allow(unused)]
    pub fn display<'a, VS: VersionSet, N: PackageName + Display>(
        &'a self,
        pool: &'a Pool<VS, N>,
    ) -> DecisionMapDisplay<'a, VS, N> {
        DecisionMapDisplay { map: self, pool }
    }
}

pub struct DecisionMapDisplay<'a, VS: VersionSet, N: PackageName + Display> {
    map: &'a DecisionMap,
    pool: &'a Pool<VS, N>,
}

impl<'a, VS: VersionSet, N: PackageName + Display> Display for DecisionMapDisplay<'a, VS, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (id, solvable) in self.pool.solvables.iter() {
            write!(f, "{} := ", solvable.display(self.pool))?;
            if let Some(value) = self.map.value(id.into()) {
                writeln!(
                    f,
                    "{} (level: {})",
                    if value { "true " } else { "false" },
                    self.map.level(id.into())
                )?;
            } else {
                writeln!(f, "<undecided>")?;
            }
        }
        Ok(())
    }
}

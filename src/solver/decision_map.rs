use std::cmp::Ordering;

use crate::internal::{arena::ArenaId, id::InternalSolvableId};

/// Represents a decision (i.e. an assignment to a solvable) and the level at
/// which it was made
///
/// = 0: undecided
/// > 0: level of decision when the solvable is set to true
/// < 0: level of decision when the solvable is set to false
#[repr(transparent)]
#[derive(Copy, Clone)]
struct DecisionAndLevel(i32);

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
        self.0.unsigned_abs()
    }

    fn with_value_and_level(value: bool, level: u32) -> Self {
        debug_assert!(level <= (i32::MAX as u32), "level is too large");
        Self(if value { level as i32 } else { -(level as i32) })
    }
}

/// A map of the assignments to solvables.
pub(crate) struct DecisionMap {
    map: Vec<DecisionAndLevel>,
}

impl DecisionMap {
    pub fn new() -> Self {
        Self {
            map: Default::default(),
        }
    }

    pub fn reset(&mut self, solvable_id: InternalSolvableId) {
        let solvable_id = solvable_id.to_usize();
        if solvable_id < self.map.len() {
            // SAFE: because we check that the solvable id is within bounds
            unsafe { *self.map.get_unchecked_mut(solvable_id) = DecisionAndLevel::undecided() };
        }
    }

    pub fn set(&mut self, solvable_id: InternalSolvableId, value: bool, level: u32) {
        let solvable_id = solvable_id.to_usize();
        if solvable_id >= self.map.len() {
            self.map
                .resize_with(solvable_id + 1, DecisionAndLevel::undecided);
        }

        // SAFE: because we ensured that vec contains at least the correct number of
        // elements.
        unsafe {
            *self.map.get_unchecked_mut(solvable_id) =
                DecisionAndLevel::with_value_and_level(value, level)
        };
    }

    pub fn level(&self, solvable_id: InternalSolvableId) -> u32 {
        self.map
            .get(solvable_id.to_usize())
            .map_or(0, |d| d.level())
    }

    #[inline(always)]
    pub fn value(&self, solvable_id: InternalSolvableId) -> Option<bool> {
        self.map.get(solvable_id.to_usize()).and_then(|d| d.value())
    }
}

use std::cmp::Ordering;

use crate::internal::arena::ArenaId;
use crate::internal::id::VariableId;

/// Represents a decision (i.e. an assignment to a variable) and the level at
/// which it was made
///
/// `= 0`: undecided
/// `> 0`: level of decision when the variable is set to true
/// `< 0`: level of decision when the variable is set to false
#[repr(transparent)]
#[derive(Copy, Clone)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
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
#[derive(Default)]
#[cfg_attr(kani, derive(kani::BoundedArbitrary))]
pub(crate) struct DecisionMap {
    #[cfg_attr(kani, bounded)]
    map: Vec<DecisionAndLevel>,
}

impl DecisionMap {
    #[cfg(feature = "diagnostics")]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn reset(&mut self, variable_id: VariableId) {
        let variable_id = variable_id.to_usize();
        if variable_id < self.map.len() {
            // SAFE: because we check that the solvable id is within bounds
            unsafe { *self.map.get_unchecked_mut(variable_id) = DecisionAndLevel::undecided() };
        }
    }

    pub fn set(&mut self, variable_id: VariableId, value: bool, level: u32) {
        let variable_id = variable_id.to_usize();
        if variable_id >= self.map.len() {
            self.map
                .resize(variable_id + 1, DecisionAndLevel::undecided());
        }

        // SAFE: because we ensured that vec contains at least the correct number of
        // elements.
        unsafe {
            *self.map.get_unchecked_mut(variable_id) =
                DecisionAndLevel::with_value_and_level(value, level)
        };
    }

    pub fn level(&self, variable_id: VariableId) -> u32 {
        self.map
            .get(variable_id.to_usize())
            .map_or(0, |d| d.level())
    }

    #[inline(always)]
    pub fn value(&self, variable_id: VariableId) -> Option<bool> {
        self.map.get(variable_id.to_usize()).and_then(|d| d.value())
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    fn decision_map_reset_correct() {
        let mut decision_map: DecisionMap = kani::bounded_any::<_, 8>();
        let initial_length = decision_map.map.len();
        let variable_id: VariableId = kani::any();

        decision_map.reset(variable_id);

        assert!(decision_map.value(variable_id).is_none());
        assert_eq!(initial_length, decision_map.map.len());
    }

    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::solver(kissat)] // Faster for this check
    fn decision_map_set_correct() {
        let mut decision_map: DecisionMap = kani::bounded_any::<_, 8>();
        let initial_length = decision_map.map.len();
        let variable_id: VariableId = kani::any();
        let value: bool = kani::any();
        let level: u32 = kani::any();

        // Since vector gets extended we want to limit its maximal
        // length, otherwise we will face unwinding issues.
        kani::assume(variable_id.to_usize() < 10);

        kani::assume(level <= (i32::MAX as u32));

        decision_map.set(variable_id, value, level);

        assert!(
            (decision_map.map.len() == variable_id.to_usize() + 1)
                || (decision_map.map.len() == initial_length),
        );
        assert!(
            (level != 0 && decision_map.value(variable_id) == Some(value))
                != (level == 0 && decision_map.value(variable_id).is_none())
        );
        assert_eq!(decision_map.level(variable_id), level)
    }
}

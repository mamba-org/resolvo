use std::fmt::{Display, Formatter};

use crate::{internal::arena::ArenaId, Interner};

/// The id associated to a package name
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NameId(u32);

impl ArenaId for NameId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a generic string
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct StringId(u32);

impl ArenaId for StringId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a VersionSet.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetId(u32);

impl ArenaId for VersionSetId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to a solvable
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct SolvableId(u32);

/// Internally used id for solvables that can also represent root and null.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub(crate) struct InternalSolvableId(u32);

const INTERNAL_SOLVABLE_NULL: u32 = u32::MAX;
const INTERNAL_SOLVABLE_ROOT: u32 = 0;

impl InternalSolvableId {
    /// Returns the id of the "root" solvable. This is a special solvable that
    /// is always present when solving.
    pub const fn root() -> Self {
        Self(0)
    }

    /// Returns if this id represents the root solvable.
    pub const fn is_root(self) -> bool {
        self.0 == 0
    }

    pub const fn null() -> Self {
        Self(u32::MAX)
    }

    pub const fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    pub const fn as_solvable(self) -> Option<SolvableId> {
        match self.0 {
            INTERNAL_SOLVABLE_NULL | INTERNAL_SOLVABLE_ROOT => None,
            x => Some(SolvableId(x - 1)),
        }
    }

    pub fn display<I: Interner>(self, interner: &I) -> impl std::fmt::Display + '_ {
        DisplayInternalSolvable { interner, id: self }
    }
}

pub struct DisplayInternalSolvable<'i, I: Interner> {
    interner: &'i I,
    id: InternalSolvableId,
}

impl<'i, I: Interner> Display for DisplayInternalSolvable<'i, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.id.0 {
            INTERNAL_SOLVABLE_ROOT => write!(f, "<root>"),
            INTERNAL_SOLVABLE_NULL => write!(f, "<null>"),
            x => {
                write!(f, "{}", self.interner.display_solvable(SolvableId(x - 1)))
            }
        }
    }
}

impl From<SolvableId> for InternalSolvableId {
    fn from(value: SolvableId) -> Self {
        Self(value.0 + 1)
    }
}

impl TryFrom<InternalSolvableId> for SolvableId {
    type Error = ();

    fn try_from(value: InternalSolvableId) -> Result<Self, Self::Error> {
        value.as_solvable().ok_or(())
    }
}

impl ArenaId for InternalSolvableId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl ArenaId for SolvableId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl From<SolvableId> for u32 {
    fn from(value: SolvableId) -> Self {
        value.0
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Debug, Hash)]
pub(crate) struct ClauseId(u32);

impl ClauseId {
    /// There is a guarentee that ClauseId(0) will always be
    /// "Clause::InstallRoot". This assumption is verified by the solver.
    pub(crate) fn install_root() -> Self {
        Self(0)
    }

    pub(crate) fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    pub(crate) fn null() -> ClauseId {
        ClauseId(u32::MAX)
    }
}

impl ArenaId for ClauseId {
    fn from_usize(x: usize) -> Self {
        assert!(x < u32::MAX as usize, "clause id too big");
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct LearntClauseId(u32);

impl ArenaId for LearntClauseId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of Candidates
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CandidatesId(u32);

impl ArenaId for CandidatesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of PackageRequirements
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DependenciesId(u32);

impl ArenaId for DependenciesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

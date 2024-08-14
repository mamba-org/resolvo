use std::fmt::{Display, Formatter};

use crate::{internal::arena::ArenaId, Interner};

/// The id associated to a package name
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NameId(pub u32);

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
pub struct StringId(pub u32);

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
pub struct VersionSetId(pub u32);

impl ArenaId for VersionSetId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a union (logical OR) of two or more version sets.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetUnionId(pub u32);

impl ArenaId for VersionSetUnionId {
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
pub struct SolvableId(pub u32);

/// Internally used id for solvables that can also represent root and null.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub(crate) struct InternalSolvableId(u32);

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

    pub const fn as_solvable(self) -> Option<SolvableId> {
        match self.0 {
            INTERNAL_SOLVABLE_ROOT => None,
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

/// A variable in the SAT problem. A variable either references a solvable, or
/// an intermediate variable.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct VarId(u32);

const VARIABLE_VAR_MASK: u32 = 1 << 31;

impl From<InternalSolvableId> for VarId {
    fn from(solvable_id: InternalSolvableId) -> Self {
        debug_assert!(solvable_id.0 < VARIABLE_VAR_MASK);
        VarId(solvable_id.0)
    }
}

impl From<SolvableId> for VarId {
    fn from(solvable_id: SolvableId) -> Self {
        InternalSolvableId::from(solvable_id).into()
    }
}

impl VarId {
    /// Returns the null variable id. This is used to represent the absence
    /// of a variable.
    pub fn null() -> VarId {
        VarId(u32::MAX)
    }

    /// Returns true if this variable id is null.
    pub fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    /// Returns true if this variable represents the root solvable
    pub fn is_root(&self) -> bool {
        self.0 == INTERNAL_SOLVABLE_ROOT
    }

    /// Returns the solvable id if this variable references a solvable.
    pub fn solvable_id(self) -> Option<InternalSolvableId> {
        self.is_solvable().then_some(InternalSolvableId(self.0))
    }

    /// Construct a new variable id from a variable id.
    pub fn var(var: u32) -> Self {
        debug_assert!(var < VARIABLE_VAR_MASK);
        VarId(var | VARIABLE_VAR_MASK)
    }

    /// Returns true if this variable id references a solvable.
    #[inline]
    pub fn is_solvable(self) -> bool {
        self.0 & VARIABLE_VAR_MASK == 0
    }

    /// Returns an [`ExpandedVar`] that represents the variable. This makes it
    /// easier to match on the content of this instance.
    pub fn expand(self) -> ExpandedVar {
        if self.is_solvable() {
            ExpandedVar::Solvable(InternalSolvableId(self.0))
        } else {
            ExpandedVar::Variable(self.0 & !VARIABLE_VAR_MASK)
        }
    }

    /// Returns an object that enables formatting the solvable.
    pub fn display<I: Interner>(self, interner: &I) -> DisplayVarId<'_, I> {
        DisplayVarId {
            interner,
            var_id: self,
        }
    }
}

pub struct DisplayVarId<'i, I: Interner> {
    interner: &'i I,
    var_id: VarId,
}

impl<'i, I: Interner> Display for DisplayVarId<'i, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.var_id.expand() {
            ExpandedVar::Solvable(s) => write!(f, "{}", s.display(self.interner)),
            ExpandedVar::Variable(v) => write!(f, "var#{}", v),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ExpandedVar {
    Solvable(InternalSolvableId),
    Variable(u32),
}

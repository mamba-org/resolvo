mod slice;
mod string;
mod vector;

use std::{ffi::c_void, fmt::Display, ptr::NonNull};

use resolvo::{KnownDependencies, SolverCache};

use crate::{slice::Slice, string::String, vector::Vector};

/// A unique identifier for a single solvable or candidate of a package. These ids should not be
/// random but rather monotonic increasing. Although it is fine to have gaps, resolvo will
/// allocate some memory based on the maximum id.
/// cbindgen:derive-eq
/// cbindgen:derive-neq
#[repr(C)]
#[derive(Copy, Clone)]
pub struct SolvableId {
    id: u32,
}

impl From<resolvo::SolvableId> for SolvableId {
    fn from(id: resolvo::SolvableId) -> Self {
        Self { id: id.0 }
    }
}

impl From<SolvableId> for resolvo::SolvableId {
    fn from(id: SolvableId) -> Self {
        Self(id.id)
    }
}

/// A unique identifier for a single version set. A version set describes a
/// set of versions.
/// cbindgen:derive-eq
/// cbindgen:derive-neq
#[repr(C)]
#[derive(Copy, Clone)]
pub struct VersionSetId {
    id: u32,
}

impl From<resolvo::VersionSetId> for VersionSetId {
    fn from(id: resolvo::VersionSetId) -> Self {
        Self { id: id.0 }
    }
}

impl From<VersionSetId> for resolvo::VersionSetId {
    fn from(id: VersionSetId) -> Self {
        Self(id.id)
    }
}

/// A unique identifier for a single package name. Resolvo will only select
/// one candidate for each unique name.
/// cbindgen:derive-eq
/// cbindgen:derive-neq
#[repr(C)]
#[derive(Copy, Clone)]
pub struct NameId {
    id: u32,
}

impl From<resolvo::NameId> for NameId {
    fn from(id: resolvo::NameId) -> Self {
        Self { id: id.0 }
    }
}

impl From<NameId> for resolvo::NameId {
    fn from(id: NameId) -> Self {
        Self(id.id)
    }
}

/// The string id is a unique identifier for a string.
/// cbindgen:derive-eq
/// cbindgen:derive-neq
#[repr(C)]
#[derive(Copy, Clone)]
pub struct StringId {
    id: u32,
}

impl From<resolvo::StringId> for StringId {
    fn from(id: resolvo::StringId) -> Self {
        Self { id: id.0 }
    }
}

impl From<StringId> for resolvo::StringId {
    fn from(id: StringId) -> Self {
        Self(id.id)
    }
}

#[derive(Default)]
#[repr(C)]
pub struct Dependencies {
    /// A pointer to the first element of a list of requirements. Requirements
    /// defines which packages should be installed alongside the depending
    /// package and the constraints applied to the package.
    pub requirements: Vector<VersionSetId>,

    /// Defines additional constraints on packages that may or may not be part
    /// of the solution. Different from `requirements`, packages in this set
    /// are not necessarily included in the solution. Only when one or more
    /// packages list the package in their `requirements` is the
    /// package also added to the solution.
    ///
    /// This is often useful to use for optional dependencies.
    pub constrains: Vector<VersionSetId>,
}

#[repr(C)]
pub struct ExcludedSolvable {
    /// The id of the solvable that is excluded from the solver.
    pub solvable: SolvableId,

    /// A string that provides more information about why the solvable is
    /// excluded (e.g. an error message).
    pub reason: StringId,
}

#[repr(C)]
pub struct Candidates {
    /// A list of all solvables for the package.
    pub candidates: Vector<SolvableId>,

    /// Optionally a pointer to the id of the solvable that is favored over
    /// other solvables. The solver will first attempt to solve for the
    /// specified solvable but will fall back to other candidates if no solution
    /// could be found otherwise.
    ///
    /// The same behavior can be achieved by sorting this candidate to the top
    /// using the [`resolvo::DependencyProvider::sort_candidates`] function but
    /// using this method provides better error messages to the user.
    pub favored: *const SolvableId,

    /// If specified this is the Id of the only solvable that can be selected.
    /// Although it would also be possible to simply return a single
    /// candidate using this field provides better error messages to the
    /// user.
    pub locked: *const SolvableId,

    /// A hint to the solver that the dependencies of some of the solvables are
    /// also directly available. This allows the solver to request the
    /// dependencies of these solvables immediately. Having the dependency
    /// information available might make the solver much faster because it
    /// has more information available up-front which provides the solver with a
    /// more complete picture of the entire problem space. However, it might
    /// also be the case that the solver doesnt actually need this
    /// information to form a solution. In general though, if the
    /// dependencies can easily be provided one should provide them up-front.
    pub hint_dependencies_available: Vector<SolvableId>,

    /// A list of solvables that are available but have been excluded from the
    /// solver. For example, a package might be excluded from the solver
    /// because it is not compatible with the runtime. The solver will not
    /// consider these solvables when forming a solution but will use
    /// them in the error message if no solution could be found.
    pub excluded: Vector<ExcludedSolvable>,
}

impl Default for Candidates {
    fn default() -> Self {
        Self {
            candidates: Vector::default(),
            favored: std::ptr::null(),
            locked: std::ptr::null(),
            hint_dependencies_available: Vector::default(),
            excluded: Vector::default(),
        }
    }
}

/// The dependency provider is a struct that is passed to the solver which
/// implements the ecosystem specific logic to resolve dependencies.
#[repr(C)]
pub struct DependencyProvider {
    /// The data pointer is a pointer that is passed to each of the functions.
    pub data: *mut c_void,

    /// Returns a user-friendly string representation of the specified solvable.
    ///
    /// When formatting the solvable, it should it include both the name of
    /// the package and any other identifying properties.
    pub display_solvable:
        unsafe extern "C" fn(data: *mut c_void, solvable: SolvableId, result: NonNull<String>),

    /// Returns a user-friendly string representation of the name of the
    /// specified solvable.
    pub display_solvable_name:
        unsafe extern "C" fn(data: *mut c_void, solvable: SolvableId, result: NonNull<String>),

    /// Returns a string representation of multiple solvables merged together.
    ///
    /// When formatting the solvables, both the name of the packages and any
    /// other identifying properties should be included.
    pub display_merged_solvables: unsafe extern "C" fn(
        data: *mut c_void,
        solvable: Slice<SolvableId>,
        result: NonNull<String>,
    ),

    /// Returns an object that can be used to display the given name in a
    /// user-friendly way.
    pub display_name:
        unsafe extern "C" fn(data: *mut c_void, name: NameId, result: NonNull<String>),

    /// Returns a user-friendly string representation of the specified version
    /// set.
    ///
    /// The name of the package should *not* be included in the display. Where
    /// appropriate, this information is added.
    pub display_version_set:
        unsafe extern "C" fn(data: *mut c_void, version_set: VersionSetId, result: NonNull<String>),

    /// Returns the string representation of the specified string.
    pub display_string:
        unsafe extern "C" fn(data: *mut c_void, string: StringId, result: NonNull<String>),

    /// Returns the name of the package that the specified version set is
    /// associated with.
    pub version_set_name:
        unsafe extern "C" fn(data: *mut c_void, version_set_id: VersionSetId) -> NameId,

    /// Returns the name of the package for the given solvable.
    pub solvable_name: unsafe extern "C" fn(data: *mut c_void, solvable_id: SolvableId) -> NameId,

    /// Obtains a list of solvables that should be considered when a package
    /// with the given name is requested.
    pub get_candidates:
        unsafe extern "C" fn(data: *mut c_void, package: NameId, candidates: NonNull<Candidates>),

    /// Sort the specified solvables based on which solvable to try first. The
    /// solver will iteratively try to select the highest version. If a
    /// conflict is found with the highest version the next version is
    /// tried. This continues until a solution is found.
    pub sort_candidates: unsafe extern "C" fn(data: *mut c_void, solvables: Slice<SolvableId>),

    /// Given a set of solvables, return the candidates that match the given
    /// version set or if `inverse` is true, the candidates that do *not* match
    /// the version set.
    pub filter_candidates: unsafe extern "C" fn(
        data: *mut c_void,
        candidates: Slice<SolvableId>,
        version_set_id: VersionSetId,
        inverse: bool,
        filtered: NonNull<Vector<SolvableId>>,
    ),

    /// Returns the dependencies for the specified solvable.
    pub get_dependencies: unsafe extern "C" fn(
        data: *mut c_void,
        solvable: SolvableId,
        dependencies: NonNull<Dependencies>,
    ),
}

impl<'d> resolvo::Interner for &'d DependencyProvider {
    fn display_solvable(&self, solvable: resolvo::SolvableId) -> impl Display + '_ {
        let mut result = String::default();
        unsafe { (self.display_solvable)(self.data, solvable.into(), NonNull::from(&mut result)) }
        result
    }

    fn display_solvable_name(&self, solvable: resolvo::SolvableId) -> impl Display + '_ {
        let mut result = String::default();
        unsafe {
            (self.display_solvable_name)(self.data, solvable.into(), NonNull::from(&mut result))
        }
        result
    }

    fn display_merged_solvables(&self, solvables: &[resolvo::SolvableId]) -> impl Display + '_ {
        let mut result = String::default();
        unsafe {
            (self.display_merged_solvables)(
                self.data,
                Slice::from_slice(std::mem::transmute(solvables)),
                NonNull::from(&mut result),
            )
        }
        result
    }

    fn display_name(&self, name: resolvo::NameId) -> impl Display + '_ {
        let mut result = String::default();
        unsafe { (self.display_name)(self.data, name.into(), NonNull::from(&mut result)) }
        result
    }

    fn display_version_set(&self, version_set: resolvo::VersionSetId) -> impl Display + '_ {
        let mut result = String::default();
        unsafe {
            (self.display_version_set)(self.data, version_set.into(), NonNull::from(&mut result))
        }
        result
    }

    fn display_string(&self, string_id: resolvo::StringId) -> impl Display + '_ {
        let mut result = String::default();
        unsafe { (self.display_string)(self.data, string_id.into(), NonNull::from(&mut result)) }
        result
    }

    fn version_set_name(&self, version_set: resolvo::VersionSetId) -> resolvo::NameId {
        unsafe { (self.version_set_name)(self.data, version_set.into()) }.into()
    }

    fn solvable_name(&self, solvable: resolvo::SolvableId) -> resolvo::NameId {
        unsafe { (self.solvable_name)(self.data, solvable.into()) }.into()
    }
}

impl<'d> resolvo::DependencyProvider for &'d DependencyProvider {
    async fn filter_candidates(
        &self,
        candidates: &[resolvo::SolvableId],
        version_set: resolvo::VersionSetId,
        inverse: bool,
    ) -> Vec<resolvo::SolvableId> {
        let mut result = Vector::default();
        unsafe {
            (self.filter_candidates)(
                self.data,
                Slice::from_slice(std::mem::transmute(candidates)),
                version_set.into(),
                inverse,
                NonNull::from(&mut result),
            )
        };
        result.into_iter().map(Into::into).collect()
    }

    async fn get_candidates(&self, name: resolvo::NameId) -> Option<resolvo::Candidates> {
        let mut candidates = Candidates {
            candidates: Vector::default(),
            favored: std::ptr::null(),
            locked: std::ptr::null(),
            hint_dependencies_available: Vector::default(),
            excluded: Vector::default(),
        };
        unsafe { (self.get_candidates)(self.data, name.into(), NonNull::from(&mut candidates)) };

        unsafe {
            Some(resolvo::Candidates {
                candidates: candidates.candidates.into_iter().map(Into::into).collect(),
                favored: candidates.favored.as_ref().copied().map(Into::into),
                locked: candidates.locked.as_ref().copied().map(Into::into),
                hint_dependencies_available: candidates
                    .hint_dependencies_available
                    .into_iter()
                    .map(Into::into)
                    .collect(),
                excluded: candidates
                    .excluded
                    .into_iter()
                    .map(|excluded| (excluded.solvable.into(), excluded.reason.into()))
                    .collect(),
            })
        }
    }

    async fn sort_candidates(
        &self,
        _solver: &SolverCache<Self>,
        solvables: &mut [resolvo::SolvableId],
    ) {
        unsafe {
            (self.sort_candidates)(self.data, Slice::from_slice(std::mem::transmute(solvables)))
        }
    }

    async fn get_dependencies(&self, solvable: resolvo::SolvableId) -> resolvo::Dependencies {
        let mut dependencies = Dependencies::default();
        unsafe {
            (self.get_dependencies)(self.data, solvable.into(), NonNull::from(&mut dependencies))
        };

        resolvo::Dependencies::Known(KnownDependencies {
            requirements: dependencies
                .requirements
                .into_iter()
                .map(Into::into)
                .collect(),
            constrains: dependencies
                .constrains
                .into_iter()
                .map(Into::into)
                .collect(),
        })
    }
}

#[no_mangle]
#[allow(unused)]
pub extern "C" fn resolvo_solve(
    provider: &DependencyProvider,
    requirements: Slice<VersionSetId>,
    constraints: Slice<VersionSetId>,
    error: &mut String,
    result: &mut Vector<SolvableId>,
) -> bool {
    let requirements = requirements
        .into_iter()
        .copied()
        .map(Into::into)
        .collect::<Vec<_>>();
    let constraints = constraints
        .into_iter()
        .copied()
        .map(Into::into)
        .collect::<Vec<_>>();

    let mut solver = resolvo::Solver::new(provider);
    match solver.solve(requirements, constraints) {
        Ok(solution) => {
            *result = solution.into_iter().map(Into::into).collect();
            true
        }
        Err(resolvo::UnsolvableOrCancelled::Unsolvable(problem)) => {
            *error = problem.display_user_friendly(&solver).to_string().into();
            false
        }
        Err(resolvo::UnsolvableOrCancelled::Cancelled(cancelled)) => {
            *error = String::from("cancelled");
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_layout_compatiblity() {
        assert_eq!(
            std::mem::size_of::<resolvo::SolvableId>(),
            std::mem::size_of::<SolvableId>()
        );
        assert_eq!(
            std::mem::size_of::<resolvo::VersionSetId>(),
            std::mem::size_of::<VersionSetId>()
        );
        assert_eq!(
            std::mem::size_of::<resolvo::NameId>(),
            std::mem::size_of::<NameId>()
        );
        assert_eq!(
            std::mem::size_of::<resolvo::StringId>(),
            std::mem::size_of::<StringId>()
        );

        assert_eq!(
            std::mem::align_of::<resolvo::SolvableId>(),
            std::mem::align_of::<SolvableId>()
        );
        assert_eq!(
            std::mem::align_of::<resolvo::VersionSetId>(),
            std::mem::align_of::<VersionSetId>()
        );
        assert_eq!(
            std::mem::align_of::<resolvo::NameId>(),
            std::mem::align_of::<NameId>()
        );
        assert_eq!(
            std::mem::align_of::<resolvo::StringId>(),
            std::mem::align_of::<StringId>()
        );
    }
}

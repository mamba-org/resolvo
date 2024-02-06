//! Implements a SAT solver for dependency resolution based on the CDCL algorithm (conflict-driven
//! clause learning)
//!
//! The CDCL algorithm is masterly explained in [An Extensible
//! SAT-solver](http://minisat.se/downloads/MiniSat.pdf). Regarding the data structures used, we
//! mostly follow the approach taken by [libsolv](https://github.com/openSUSE/libsolv). The code of
//! libsolv is, however, very low level C, so if you are looking for an introduction to CDCL, you
//! are encouraged to look at the paper instead or to keep reading through this codebase and its
//! comments.

#![deny(missing_docs)]

pub(crate) mod internal;
mod pool;
pub mod problem;
pub mod range;
mod solvable;
mod solver;

use itertools::Itertools;

pub use internal::{
    id::{NameId, SolvableId, StringId, VersionSetId},
    mapping::Mapping,
};
pub use pool::Pool;
pub use solvable::Solvable;
pub use solver::{Solver, SolverCache, UnsolvableOrCancelled};
use std::{
    any::Any,
    fmt::{Debug, Display},
    hash::Hash,
    rc::Rc,
};

/// The solver is based around the fact that for for every package name we are trying to find a
/// single variant. Variants are grouped by their respective package name. A package name is
/// anything that we can compare and hash for uniqueness checks.
///
/// For most implementations a package name can simply be a String. But in some more advanced cases
/// like when a single package can have additive features it can make sense to create a custom type.
///
/// A blanket trait implementation is provided for any type that implements [`Eq`] and [`Hash`].
pub trait PackageName: Eq + Hash {}

impl<N: Eq + Hash> PackageName for N {}

/// A [`VersionSet`] is describes a set of "versions". The trait defines whether a given version
/// is part of the set or not.
///
/// One could implement [`VersionSet`] for [`std::ops::Range<u32>`] where the implementation
/// returns `true` if a given `u32` is part of the range or not.
pub trait VersionSet: Debug + Display + Clone + Eq + Hash {
    /// The element type that is included in the set.
    type V: Display + Ord;

    /// Evaluate membership of a version in this set.
    fn contains(&self, v: &Self::V) -> bool;
}

/// Defines implementation specific behavior for the solver and a way for the solver to access the
/// packages that are available in the system.
pub trait DependencyProvider<VS: VersionSet, N: PackageName = String>: Sized {
    /// Returns the [`Pool`] that is used to allocate the Ids returned from this instance
    fn pool(&self) -> Rc<Pool<VS, N>>;

    /// Sort the specified solvables based on which solvable to try first. The solver will
    /// iteratively try to select the highest version. If a conflict is found with the highest
    /// version the next version is tried. This continues until a solution is found.
    ///
    /// # Async
    ///
    /// The returned future will be awaited by a tokio runtime blocking the main thread. You are
    /// free to use other runtimes in your implementation, as long as the runtime-specific code runs
    /// in threads controlled by that runtime (and _not_ in the main thread). For instance, you can
    /// use `async_std::task::spawn` to spawn a new task, use `async_std::io` inside the task to
    /// retrieve necessary information from the network, and `await` the returned task handle.

    #[allow(async_fn_in_trait)]
    async fn sort_candidates(
        &self,
        solver: &SolverCache<VS, N, Self>,
        solvables: &mut [SolvableId],
    );

    /// Obtains a list of solvables that should be considered when a package with the given name is
    /// requested.
    ///
    /// # Async
    ///
    /// The returned future will be awaited by a tokio runtime blocking the main thread. You are
    /// free to use other runtimes in your implementation, as long as the runtime-specific code runs
    /// in threads controlled by that runtime (and _not_ in the main thread). For instance, you can
    /// use `async_std::task::spawn` to spawn a new task, use `async_std::io` inside the task to
    /// retrieve necessary information from the network, and `await` the returned task handle.
    #[allow(async_fn_in_trait)]
    async fn get_candidates(&self, name: NameId) -> Option<Candidates>;

    /// Returns the dependencies for the specified solvable.
    ///
    /// # Async
    ///
    /// The returned future will be awaited by a tokio runtime blocking the main thread. You are
    /// free to use other runtimes in your implementation, as long as the runtime-specific code runs
    /// in threads controlled by that runtime (and _not_ in the main thread). For instance, you can
    /// use `async_std::task::spawn` to spawn a new task, use `async_std::io` inside the task to
    /// retrieve necessary information from the network, and `await` the returned task handle.
    #[allow(async_fn_in_trait)]
    async fn get_dependencies(&self, solvable: SolvableId) -> Dependencies;

    /// Whether the solver should stop the dependency resolution algorithm.
    ///
    /// This method gets called at the beginning of each unit propagation round and before
    /// potentially blocking operations (like [Self::get_dependencies] and [Self::get_candidates]).
    /// If it returns `Some(...)`, the solver will stop and return
    /// [UnsolvableOrCancelled::Cancelled].
    fn should_cancel_with_value(&self) -> Option<Box<dyn Any>> {
        None
    }
}

/// A list of candidate solvables for a specific package. This is returned from
/// [`DependencyProvider::get_candidates`].
#[derive(Default, Clone, Debug)]
pub struct Candidates {
    /// A list of all solvables for the package.
    pub candidates: Vec<SolvableId>,

    /// Optionally the id of the solvable that is favored over other solvables. The solver will
    /// first attempt to solve for the specified solvable but will fall back to other candidates if
    /// no solution could be found otherwise.
    ///
    /// The same behavior can be achieved by sorting this candidate to the top using the
    /// [`DependencyProvider::sort_candidates`] function but using this method provides better
    /// error messages to the user.
    pub favored: Option<SolvableId>,

    /// If specified this is the Id of the only solvable that can be selected. Although it would
    /// also be possible to simply return a single candidate using this field provides better error
    /// messages to the user.
    pub locked: Option<SolvableId>,

    /// A hint to the solver that the dependencies of some of the solvables are also directly
    /// available. This allows the solver to request the dependencies of these solvables
    /// immediately. Having the dependency information available might make the solver much faster
    /// because it has more information available up-front which provides the solver with a more
    /// complete picture of the entire problem space. However, it might also be the case that the
    /// solver doesnt actually need this information to form a solution. In general though, if the
    /// dependencies can easily be provided one should provide them up-front.
    pub hint_dependencies_available: Vec<SolvableId>,

    /// A list of solvables that are available but have been excluded from the solver. For example,
    /// a package might be excluded from the solver because it is not compatible with the
    /// runtime. The solver will not consider these solvables when forming a solution but will use
    /// them in the error message if no solution could be found.
    pub excluded: Vec<(SolvableId, StringId)>,
}

/// Holds information about the dependencies of a package.
pub enum Dependencies {
    /// The dependencies are known.
    Known(KnownDependencies),
    /// The dependencies are unknown, so the parent solvable should be excluded from the solution.
    ///
    /// The string provides more information about why the dependencies are unknown (e.g. an error
    /// message).
    Unknown(StringId),
}

/// Holds information about the dependencies of a package when they are known.
#[derive(Default, Clone, Debug)]
pub struct KnownDependencies {
    /// Defines which packages should be installed alongside the depending package and the
    /// constraints applied to the package.
    pub requirements: Vec<VersionSetId>,

    /// Defines additional constraints on packages that may or may not be part of the solution.
    /// Different from `requirements`, packages in this set are not necessarily included in the
    /// solution. Only when one or more packages list the package in their `requirements` is the
    /// package also added to the solution.
    ///
    /// This is often useful to use for optional dependencies.
    pub constrains: Vec<VersionSetId>,
}

/// Defines how merged candidates should be displayed.
pub trait SolvableDisplay<VS: VersionSet, Name: PackageName = String> {
    /// A method that is used to display multiple solvables in a user friendly way.
    /// For example the conda provider should only display the versions (not build strings etc.)
    /// and merges multiple solvables into one line.
    fn display_candidates(&self, pool: &Pool<VS, Name>, candidates: &[SolvableId]) -> String;
}

/// Display merged candidates on single line with `|` as separator.
pub struct DefaultSolvableDisplay;

impl<VS: VersionSet, Name: Hash + Eq> SolvableDisplay<VS, Name> for DefaultSolvableDisplay
where
    VS::V: Ord,
{
    fn display_candidates(
        &self,
        pool: &Pool<VS, Name>,
        merged_candidates: &[SolvableId],
    ) -> String {
        merged_candidates
            .iter()
            .map(|&id| &pool.resolve_solvable(id).inner)
            .sorted()
            .map(|s| s.to_string())
            .join(" | ")
    }
}

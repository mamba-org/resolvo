use std::{any::Any, cell::RefCell, rc::Rc};

use ahash::HashMap;
use bitvec::vec::BitVec;
use elsa::FrozenMap;
use event_listener::Event;

use crate::{
    internal::{
        arena::{Arena, ArenaId},
        frozen_copy_map::FrozenCopyMap,
        id::{CandidatesId, DependenciesId},
    },
    Candidates, Dependencies, DependencyProvider, NameId, SolvableId, VersionSetId,
};

/// Keeps a cache of previously computed and/or requested information about
/// solvables and version sets.
pub struct SolverCache<D: DependencyProvider> {
    provider: D,

    /// A mapping from package name to a list of candidates.
    candidates: Arena<CandidatesId, Candidates>,
    package_name_to_candidates: FrozenCopyMap<NameId, CandidatesId>,
    package_name_to_candidates_in_flight: RefCell<HashMap<NameId, Rc<Event>>>,

    /// A mapping of `VersionSetId` to the candidates that match that set.
    version_set_candidates: FrozenMap<VersionSetId, Vec<SolvableId>, ahash::RandomState>,

    /// A mapping of `VersionSetId` to the candidates that do not match that set
    /// (only candidates of the package indicated by the version set are
    /// included).
    version_set_inverse_candidates: FrozenMap<VersionSetId, Vec<SolvableId>, ahash::RandomState>,

    /// A mapping of `VersionSetId` to a sorted list of candidates that match
    /// that set.
    pub(crate) version_set_to_sorted_candidates:
        FrozenMap<VersionSetId, Vec<SolvableId>, ahash::RandomState>,

    /// A mapping from a solvable to a list of dependencies
    solvable_dependencies: Arena<DependenciesId, Dependencies>,
    solvable_to_dependencies: FrozenCopyMap<SolvableId, DependenciesId>,

    /// A mapping that indicates that the dependencies for a particular solvable
    /// can cheaply be retrieved from the dependency provider. This
    /// information is provided by the DependencyProvider when the
    /// candidates for a package are requested.
    hint_dependencies_available: RefCell<BitVec>,
}

impl<D: DependencyProvider> SolverCache<D> {
    /// Constructs a new instance from a provider.
    pub fn new(provider: D) -> Self {
        Self {
            provider,

            candidates: Default::default(),
            package_name_to_candidates: Default::default(),
            package_name_to_candidates_in_flight: Default::default(),
            version_set_candidates: Default::default(),
            version_set_inverse_candidates: Default::default(),
            version_set_to_sorted_candidates: Default::default(),
            solvable_dependencies: Default::default(),
            solvable_to_dependencies: Default::default(),
            hint_dependencies_available: Default::default(),
        }
    }

    /// Returns the [`DependencyProvider`] used by this cache.
    pub fn provider(&self) -> &D {
        &self.provider
    }

    /// Returns the candidates for the package with the given name. This will
    /// either ask the [`DependencyProvider`] for the entries or a cached
    /// value.
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    pub async fn get_or_cache_candidates(
        &self,
        package_name: NameId,
    ) -> Result<&Candidates, Box<dyn Any>> {
        // If we already have the candidates for this package cached we can simply
        // return
        let candidates_id = match self.package_name_to_candidates.get_copy(&package_name) {
            Some(id) => id,
            None => {
                // Since getting the candidates from the provider is a potentially blocking
                // operation, we want to check beforehand whether we should cancel the solving
                // process
                if let Some(value) = self.provider.should_cancel_with_value() {
                    return Err(value);
                }

                // Check if there is an in-flight request
                let in_flight_request = self
                    .package_name_to_candidates_in_flight
                    .borrow()
                    .get(&package_name)
                    .cloned();
                match in_flight_request {
                    Some(in_flight) => {
                        // Found an in-flight request, wait for that request to finish and return
                        // the computed result.
                        in_flight.listen().await;
                        self.package_name_to_candidates
                            .get_copy(&package_name)
                            .expect("after waiting for a request the result should be available")
                    }
                    None => {
                        // Prepare an in-flight notifier for other requests coming in.
                        self.package_name_to_candidates_in_flight
                            .borrow_mut()
                            .insert(package_name, Rc::new(Event::new()));

                        // Otherwise we have to get them from the DependencyProvider
                        let candidates = self
                            .provider
                            .get_candidates(package_name)
                            .await
                            .unwrap_or_default();

                        // Store information about which solvables dependency information is easy to
                        // retrieve.
                        {
                            let mut hint_dependencies_available =
                                self.hint_dependencies_available.borrow_mut();
                            for hint_candidate in candidates.hint_dependencies_available.iter() {
                                let idx = hint_candidate.to_usize();
                                if hint_dependencies_available.len() <= idx {
                                    hint_dependencies_available.resize(idx + 1, false);
                                }
                                hint_dependencies_available.set(idx, true)
                            }
                        }

                        // Allocate an ID so we can refer to the candidates from everywhere
                        let candidates_id = self.candidates.alloc(candidates);
                        self.package_name_to_candidates
                            .insert_copy(package_name, candidates_id);

                        // Remove the in-flight request now that we inserted the result and notify
                        // any waiters
                        let notifier = self
                            .package_name_to_candidates_in_flight
                            .borrow_mut()
                            .remove(&package_name)
                            .expect("notifier should be there");
                        notifier.notify(usize::MAX);

                        candidates_id
                    }
                }
            }
        };

        // Returns a reference from the arena
        Ok(&self.candidates[candidates_id])
    }

    /// Returns the candidates of a package that match the specified version
    /// set.
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    pub async fn get_or_cache_matching_candidates(
        &self,
        version_set_id: VersionSetId,
    ) -> Result<&[SolvableId], Box<dyn Any>> {
        match self.version_set_candidates.get(&version_set_id) {
            Some(candidates) => Ok(candidates),
            None => {
                let package_name = self.provider.version_set_name(version_set_id);
                let candidates = self.get_or_cache_candidates(package_name).await?;

                let matching_candidates = self
                    .provider
                    .filter_candidates(&candidates.candidates, version_set_id, false)
                    .await;

                Ok(self
                    .version_set_candidates
                    .insert(version_set_id, matching_candidates))
            }
        }
    }

    /// Returns the candidates that do *not* match the specified requirement.
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    pub async fn get_or_cache_non_matching_candidates(
        &self,
        version_set_id: VersionSetId,
    ) -> Result<&[SolvableId], Box<dyn Any>> {
        match self.version_set_inverse_candidates.get(&version_set_id) {
            Some(candidates) => Ok(candidates),
            None => {
                let package_name = self.provider.version_set_name(version_set_id);
                let candidates = self.get_or_cache_candidates(package_name).await?;

                let matching_candidates = self
                    .provider
                    .filter_candidates(&candidates.candidates, version_set_id, true)
                    .await
                    .into_iter()
                    .map(Into::into)
                    .collect();

                Ok(self
                    .version_set_inverse_candidates
                    .insert(version_set_id, matching_candidates))
            }
        }
    }

    /// Returns the candidates for the package with the given name similar to
    /// [`Self::get_or_cache_candidates`] sorted from highest to lowest.
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    pub async fn get_or_cache_sorted_candidates(
        &self,
        version_set_id: VersionSetId,
    ) -> Result<&[SolvableId], Box<dyn Any>> {
        match self.version_set_to_sorted_candidates.get(&version_set_id) {
            Some(candidates) => Ok(candidates),
            None => {
                let package_name = self.provider.version_set_name(version_set_id);
                let matching_candidates = self
                    .get_or_cache_matching_candidates(version_set_id)
                    .await?;
                let candidates = self.get_or_cache_candidates(package_name).await?;

                // Sort all the candidates in order in which they should be tried by the solver.
                let mut sorted_candidates = Vec::new();
                sorted_candidates.extend_from_slice(matching_candidates);
                self.provider
                    .sort_candidates(self, &mut sorted_candidates)
                    .await;

                // If we have a solvable that we favor, we sort that to the front. This ensures
                // that the version that is favored is picked first.
                if let Some(favored_id) = candidates.favored {
                    if let Some(pos) = sorted_candidates.iter().position(|&s| s == favored_id) {
                        // Move the element at `pos` to the front of the array
                        sorted_candidates[0..=pos].rotate_right(1);
                    }
                }

                Ok(self
                    .version_set_to_sorted_candidates
                    .insert(version_set_id, sorted_candidates))
            }
        }
    }

    /// Returns the dependencies of a solvable. Requests the solvables from the
    /// [`DependencyProvider`] if they are not known yet.
    ///
    /// If the provider has requested the solving process to be cancelled, the
    /// cancellation value will be returned as an `Err(...)`.
    pub async fn get_or_cache_dependencies(
        &self,
        solvable_id: SolvableId,
    ) -> Result<&Dependencies, Box<dyn Any>> {
        let dependencies_id = match self.solvable_to_dependencies.get_copy(&solvable_id) {
            Some(id) => id,
            None => {
                // Since getting the dependencies from the provider is a potentially blocking
                // operation, we want to check beforehand whether we should cancel the solving
                // process
                if let Some(value) = self.provider.should_cancel_with_value() {
                    return Err(value);
                }

                let dependencies = self.provider.get_dependencies(solvable_id).await;
                let dependencies_id = self.solvable_dependencies.alloc(dependencies);
                self.solvable_to_dependencies
                    .insert_copy(solvable_id, dependencies_id);
                dependencies_id
            }
        };

        Ok(&self.solvable_dependencies[dependencies_id])
    }

    /// Returns true if the dependencies for the given solvable are "cheaply"
    /// available. This means either the dependency provider indicated that
    /// the dependencies for a solvable are available or the dependencies
    /// have already been requested.
    pub fn are_dependencies_available_for(&self, solvable: SolvableId) -> bool {
        if self.solvable_to_dependencies.get_copy(&solvable).is_some() {
            true
        } else {
            let solvable_idx = solvable.to_usize();
            let hint_dependencies_available = self.hint_dependencies_available.borrow();
            let value = hint_dependencies_available
                .get(solvable_idx)
                .as_deref()
                .copied();
            value.unwrap_or(false)
        }
    }
}

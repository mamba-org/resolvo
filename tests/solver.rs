use std::{
    any::Any,
    borrow::Borrow,
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::{Debug, Display, Formatter},
    io::{stderr, Write},
    num::ParseIntError,
    rc::Rc,
    str::FromStr,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    time::Duration,
};

use ahash::HashMap;
use indexmap::IndexMap;
use insta::assert_snapshot;
use itertools::Itertools;
use resolvo::{
    snapshot::{DependencySnapshot, SnapshotProvider},
    utils::Pool,
    Candidates, Dependencies, DependencyProvider, Interner, KnownDependencies, NameId, Problem,
    Requirement, SolvableId, Solver, SolverCache, StringId, UnsolvableOrCancelled, VersionSetId,
    VersionSetUnionId,
};
use tracing_test::traced_test;
use version_ranges::Ranges;

// Let's define our own packaging version system and dependency specification.
// This is a very simple version system, where a package is identified by a name
// and a version in which the version is just an integer. The version is a range
// so can be noted as 0..2 or something of the sorts, we also support constrains
// which means it should not use that package version this is also represented
// with a range.
//
// You can also use just a single number for a range like `package 0` which
// means the range from 0..1 (excluding the end)
//
// Lets call the tuples of (Name, Version) a `Pack` and the tuples of (Name,
// Ranges<u32>) a `Spec`
//
// We also need to create a custom provider that tells us how to sort the
// candidates. This is unique to each packaging ecosystem. Let's call our
// ecosystem 'BundleBox' so that how we call the provider as well.

/// This is `Pack` which is a unique version and name in our bespoke packaging
/// system
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
struct Pack {
    version: u32,
    unknown_deps: bool,
    cancel_during_get_dependencies: bool,
}

impl Pack {
    fn new(version: u32) -> Pack {
        Pack {
            version,
            unknown_deps: false,
            cancel_during_get_dependencies: false,
        }
    }

    fn with_unknown_deps(mut self) -> Pack {
        self.unknown_deps = true;
        self
    }

    fn cancel_during_get_dependencies(mut self) -> Pack {
        self.cancel_during_get_dependencies = true;
        self
    }

    fn offset(&self, version_offset: i32) -> Pack {
        let mut pack = *self;
        pack.version = pack.version.wrapping_add_signed(version_offset);
        pack
    }
}

impl From<u32> for Pack {
    fn from(value: u32) -> Self {
        Pack::new(value)
    }
}

impl From<i32> for Pack {
    fn from(value: i32) -> Self {
        Pack::new(value as u32)
    }
}

impl Display for Pack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.version)
    }
}

impl FromStr for Pack {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        u32::from_str(s).map(Pack::new)
    }
}

/// We can use this to see if a `Pack` is contained in a range of package
/// versions or a `Spec`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Spec {
    name: String,
    versions: Ranges<Pack>,
}

impl Spec {
    pub fn new(name: String, versions: Ranges<Pack>) -> Self {
        Self { name, versions }
    }

    pub fn parse_union(
        spec: &str,
    ) -> impl Iterator<Item = Result<Self, <Self as FromStr>::Err>> + '_ {
        spec.split('|')
            .map(str::trim)
            .map(|dep| Spec::from_str(dep))
    }
}

impl FromStr for Spec {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let split = s.split(' ').collect::<Vec<_>>();
        let name = split
            .first()
            .expect("spec does not have a name")
            .to_string();

        fn version_range(s: Option<&&str>) -> Ranges<Pack> {
            if let Some(s) = s {
                let (start, end) = s
                    .split_once("..")
                    .map_or((*s, None), |(start, end)| (start, Some(end)));
                let start: Pack = start.parse().unwrap();
                let end = end
                    .map(FromStr::from_str)
                    .transpose()
                    .unwrap()
                    .unwrap_or(start.offset(1));
                Ranges::between(start, end)
            } else {
                Ranges::full()
            }
        }

        let versions = version_range(split.get(1));

        Ok(Spec::new(name, versions))
    }
}

/// This provides sorting functionality for our `BundleBox` packaging system
#[derive(Default)]
struct BundleBoxProvider {
    pool: Pool<Ranges<Pack>>,
    packages: IndexMap<String, IndexMap<Pack, BundleBoxPackageDependencies>>,
    favored: HashMap<String, Pack>,
    locked: HashMap<String, Pack>,
    excluded: HashMap<String, HashMap<Pack, String>>,
    cancel_solving: Cell<bool>,
    // TODO: simplify?
    concurrent_requests: Arc<AtomicUsize>,
    concurrent_requests_max: Rc<Cell<usize>>,
    sleep_before_return: bool,

    // A mapping of packages that we have requested candidates for. This way we can keep track of
    // duplicate requests.
    requested_candidates: RefCell<HashSet<NameId>>,
    requested_dependencies: RefCell<HashSet<SolvableId>>,
    interned_solvables: RefCell<HashMap<(NameId, Pack), SolvableId>>,
}

#[derive(Debug, Clone)]
struct BundleBoxPackageDependencies {
    dependencies: Vec<Vec<Spec>>,
    constrains: Vec<Spec>,
}

impl BundleBoxProvider {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn package_name(&self, name: &str) -> NameId {
        self.pool
            .lookup_package_name(&name.to_string())
            .expect("package missing")
    }

    pub fn requirements<R: From<VersionSetId>>(&self, requirements: &[&str]) -> Vec<R> {
        requirements
            .iter()
            .map(|dep| Spec::from_str(dep).unwrap())
            .map(|spec| self.intern_version_set(&spec))
            .map(From::from)
            .collect()
    }

    pub fn parse_requirements(&self, requirements: &[&str]) -> Vec<Requirement> {
        requirements
            .iter()
            .map(|deps| {
                let specs = Spec::parse_union(deps).map(Result::unwrap);
                self.intern_version_set_union(specs).into()
            })
            .collect()
    }

    pub fn intern_version_set(&self, spec: &Spec) -> VersionSetId {
        let dep_name = self.pool.intern_package_name(&spec.name);
        self.pool
            .intern_version_set(dep_name, spec.versions.clone())
    }

    pub fn intern_version_set_union(
        &self,
        specs: impl IntoIterator<Item = impl Borrow<Spec>>,
    ) -> VersionSetUnionId {
        let mut specs = specs
            .into_iter()
            .map(|spec| self.intern_version_set(spec.borrow()));
        self.pool
            .intern_version_set_union(specs.next().unwrap(), specs)
    }

    pub fn from_packages(packages: &[(&str, u32, Vec<&str>)]) -> Self {
        let mut result = Self::new();
        for (name, version, deps) in packages {
            result.add_package(name, Pack::new(*version), deps, &[]);
        }
        result
    }

    pub fn set_favored(&mut self, package_name: &str, version: u32) {
        self.favored
            .insert(package_name.to_owned(), Pack::new(version));
    }

    pub fn exclude(&mut self, package_name: &str, version: u32, reason: impl Into<String>) {
        self.excluded
            .entry(package_name.to_owned())
            .or_default()
            .insert(Pack::new(version), reason.into());
    }

    pub fn set_locked(&mut self, package_name: &str, version: u32) {
        self.locked
            .insert(package_name.to_owned(), Pack::new(version));
    }

    pub fn add_package(
        &mut self,
        package_name: &str,
        package_version: Pack,
        dependencies: &[&str],
        constrains: &[&str],
    ) {
        self.pool.intern_package_name(package_name);

        let dependencies = dependencies
            .iter()
            .map(|dep| Spec::parse_union(dep).collect())
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let constrains = constrains
            .iter()
            .map(|dep| Spec::from_str(dep))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        self.packages
            .entry(package_name.to_owned())
            .or_default()
            .insert(
                package_version,
                BundleBoxPackageDependencies {
                    dependencies,
                    constrains,
                },
            );
    }

    // Sends a value from the dependency provider to the solver, introducing a
    // minimal delay to force concurrency to be used (unless there is no async
    // runtime available)
    async fn maybe_delay<T: Send + 'static>(&self, value: T) -> T {
        if self.sleep_before_return {
            tokio::time::sleep(Duration::from_millis(10)).await;
            self.concurrent_requests.fetch_sub(1, Ordering::SeqCst);
            value
        } else {
            value
        }
    }

    pub fn into_snapshot(self) -> DependencySnapshot {
        let name_ids = self
            .packages
            .keys()
            .filter_map(|name| self.pool.lookup_package_name(name))
            .collect::<Vec<_>>();
        DependencySnapshot::from_provider(self, name_ids, [], []).unwrap()
    }

    pub fn intern_solvable(&self, name_id: NameId, pack: Pack) -> SolvableId {
        *self
            .interned_solvables
            .borrow_mut()
            .entry((name_id, pack))
            .or_insert_with_key(|&(name_id, pack)| self.pool.intern_solvable(name_id, pack))
    }

    pub fn solvable_id(&self, name: impl Into<String>, version: impl Into<Pack>) -> SolvableId {
        self.intern_solvable(self.pool.intern_package_name(name.into()), version.into())
    }
}

impl Interner for BundleBoxProvider {
    fn display_solvable(&self, solvable: SolvableId) -> impl Display + '_ {
        let solvable = self.pool.resolve_solvable(solvable);
        format!("{}={}", self.display_name(solvable.name), solvable.record)
    }

    fn display_merged_solvables(&self, solvables: &[SolvableId]) -> impl Display + '_ {
        if solvables.is_empty() {
            return "".to_string();
        }

        let name = self.display_name(self.pool.resolve_solvable(solvables[0]).name);
        let versions = solvables
            .iter()
            .map(|&s| self.pool.resolve_solvable(s).record.version)
            .sorted();
        format!("{name} {}", versions.format(" | "))
    }

    fn display_name(&self, name: NameId) -> impl Display + '_ {
        self.pool.resolve_package_name(name).clone()
    }

    fn display_version_set(&self, version_set: VersionSetId) -> impl Display + '_ {
        self.pool.resolve_version_set(version_set).clone()
    }

    fn display_string(&self, string_id: StringId) -> impl Display + '_ {
        self.pool.resolve_string(string_id).to_owned()
    }

    fn version_set_name(&self, version_set: VersionSetId) -> NameId {
        self.pool.resolve_version_set_package_name(version_set)
    }

    fn solvable_name(&self, solvable: SolvableId) -> NameId {
        self.pool.resolve_solvable(solvable).name
    }
    fn version_sets_in_union(
        &self,
        version_set_union: VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId> {
        self.pool.resolve_version_set_union(version_set_union)
    }
}

impl DependencyProvider for BundleBoxProvider {
    async fn filter_candidates(
        &self,
        candidates: &[SolvableId],
        version_set: VersionSetId,
        inverse: bool,
    ) -> Vec<SolvableId> {
        let range = self.pool.resolve_version_set(version_set);
        candidates
            .iter()
            .copied()
            .filter(|s| range.contains(&self.pool.resolve_solvable(*s).record) == !inverse)
            .collect()
    }

    async fn sort_candidates(&self, _solver: &SolverCache<Self>, solvables: &mut [SolvableId]) {
        solvables.sort_by(|a, b| {
            let a = self.pool.resolve_solvable(*a).record;
            let b = self.pool.resolve_solvable(*b).record;
            // We want to sort with highest version on top
            b.version.cmp(&a.version)
        });
    }

    async fn get_candidates(&self, name: NameId) -> Option<Candidates> {
        let concurrent_requests = self.concurrent_requests.fetch_add(1, Ordering::SeqCst);
        self.concurrent_requests_max.set(
            self.concurrent_requests_max
                .get()
                .max(concurrent_requests + 1),
        );

        assert!(
            self.requested_candidates.borrow_mut().insert(name),
            "duplicate get_candidates request"
        );

        let package_name = self.pool.resolve_package_name(name);
        let Some(package) = self.packages.get(package_name) else {
            return self.maybe_delay(None).await;
        };

        let mut candidates = Candidates {
            candidates: Vec::with_capacity(package.len()),
            ..Candidates::default()
        };
        let favor = self.favored.get(package_name);
        let locked = self.locked.get(package_name);
        let excluded = self.excluded.get(package_name);
        for pack in package.keys() {
            let solvable = self.intern_solvable(name, *pack);
            candidates.candidates.push(solvable);
            if Some(pack) == favor {
                candidates.favored = Some(solvable);
            }
            if Some(pack) == locked {
                candidates.locked = Some(solvable);
            }
            if let Some(excluded) = excluded.and_then(|d| d.get(pack)) {
                candidates
                    .excluded
                    .push((solvable, self.pool.intern_string(excluded)));
            }
        }

        self.maybe_delay(Some(candidates)).await
    }

    async fn get_dependencies(&self, solvable: SolvableId) -> Dependencies {
        tracing::info!(
            "get dependencies for {}",
            self.pool
                .resolve_solvable(solvable)
                .name
                .display(&self.pool)
        );

        let concurrent_requests = self.concurrent_requests.fetch_add(1, Ordering::SeqCst);
        self.concurrent_requests_max.set(
            self.concurrent_requests_max
                .get()
                .max(concurrent_requests + 1),
        );

        assert!(
            self.requested_dependencies.borrow_mut().insert(solvable),
            "duplicate get_dependencies request"
        );

        let candidate = self.pool.resolve_solvable(solvable);
        let package_name = self.pool.resolve_package_name(candidate.name);
        let pack = candidate.record;

        if pack.cancel_during_get_dependencies {
            self.cancel_solving.set(true);
            let reason = self.pool.intern_string("cancelled");
            return self.maybe_delay(Dependencies::Unknown(reason)).await;
        }

        if pack.unknown_deps {
            let reason = self.pool.intern_string("could not retrieve deps");
            return self.maybe_delay(Dependencies::Unknown(reason)).await;
        }

        let Some(deps) = self.packages.get(package_name).and_then(|v| v.get(&pack)) else {
            return self
                .maybe_delay(Dependencies::Known(Default::default()))
                .await;
        };

        let mut result = KnownDependencies {
            requirements: Vec::with_capacity(deps.dependencies.len()),
            constrains: Vec::with_capacity(deps.constrains.len()),
        };
        for req in &deps.dependencies {
            let mut remaining_req_specs = req.iter();

            let first = remaining_req_specs
                .next()
                .expect("Dependency spec must have at least one constraint");

            let first_name = self.pool.intern_package_name(&first.name);
            let first_version_set = self
                .pool
                .intern_version_set(first_name, first.versions.clone());

            let requirement = if remaining_req_specs.len() == 0 {
                first_version_set.into()
            } else {
                let other_version_sets = remaining_req_specs.map(|spec| {
                    self.pool.intern_version_set(
                        self.pool.intern_package_name(&spec.name),
                        spec.versions.clone(),
                    )
                });

                self.pool
                    .intern_version_set_union(first_version_set, other_version_sets)
                    .into()
            };

            result.requirements.push(requirement);
        }

        for req in &deps.constrains {
            let dep_name = self.pool.intern_package_name(&req.name);
            let dep_spec = self.pool.intern_version_set(dep_name, req.versions.clone());
            result.constrains.push(dep_spec);
        }

        self.maybe_delay(Dependencies::Known(result)).await
    }

    fn should_cancel_with_value(&self) -> Option<Box<dyn Any>> {
        if self.cancel_solving.get() {
            Some(Box::new("cancelled!".to_string()))
        } else {
            None
        }
    }
}

/// Create a string from a [`Transaction`]
fn transaction_to_string(interner: &impl Interner, solvables: &Vec<SolvableId>) -> String {
    use std::fmt::Write;
    let mut buf = String::new();
    for solvable in solvables
        .iter()
        .copied()
        .map(|s| interner.display_solvable(s).to_string())
        .sorted()
    {
        writeln!(buf, "{solvable}").unwrap();
    }

    buf
}

/// Unsat so that we can view the conflict
fn solve_unsat(provider: BundleBoxProvider, specs: &[&str]) -> String {
    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    match solver.solve(problem) {
        Ok(_) => panic!("expected unsat, but a solution was found"),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

/// Solve the problem and returns either a solution represented as a string or
/// an error string.
fn solve_snapshot(mut provider: BundleBoxProvider, specs: &[&str]) -> String {
    // The test dependency provider requires time support for sleeping
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .build()
        .unwrap();

    provider.sleep_before_return = true;

    let requirements = provider.parse_requirements(specs);
    let mut solver = Solver::new(provider).with_runtime(runtime);
    let problem = Problem::new().requirements(requirements);
    match solver.solve(problem) {
        Ok(solvables) => transaction_to_string(solver.provider(), &solvables),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

/// Test whether we can select a version, this is the most basic operation
#[test]
fn test_unit_propagation_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 1);
}

/// Test if we can also select a nested version
#[test]
fn test_unit_propagation_nested() {
    let provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1u32, vec!["efgh"]),
        ("efgh", 4u32, vec![]),
        ("dummy", 6u32, vec![]),
    ]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 2);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 1);

    let solvable = pool.resolve_solvable(solved[1]);

    assert_eq!(pool.resolve_package_name(solvable.name), "efgh");
    assert_eq!(solvable.record.version, 4);
}

/// Test if we can resolve multiple versions at once
#[test]
fn test_resolve_multiple() {
    let provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1, vec![]),
        ("asdf", 2, vec![]),
        ("efgh", 4, vec![]),
        ("efgh", 5, vec![]),
    ]);
    let requirements = provider.requirements(&["asdf", "efgh"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let mut solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 2);
    solved.sort_by_key(|&s| pool.resolve_package_name(pool.resolve_solvable(s).name));

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 2);

    let solvable = pool.resolve_solvable(solved[1]);

    assert_eq!(pool.resolve_package_name(solvable.name), "efgh");
    assert_eq!(solvable.record.version, 5);
}

#[test]
fn test_resolve_with_concurrent_metadata_fetching() {
    let provider = BundleBoxProvider::from_packages(&[
        ("parent", 4, vec!["child1", "child2"]),
        ("child1", 3, vec![]),
        ("child2", 2, vec![]),
    ]);

    let max_concurrent_requests = provider.concurrent_requests_max.clone();

    let result = solve_snapshot(provider, &["parent"]);
    insta::assert_snapshot!(result);

    assert_eq!(2, max_concurrent_requests.get());
}

/// In case of a conflict the version should not be selected with the conflict
#[test]
fn test_resolve_with_conflict() {
    let provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec!["conflicting 1"]),
        ("asdf", 3, vec!["conflicting 0"]),
        ("efgh", 7, vec!["conflicting 0"]),
        ("efgh", 6, vec!["conflicting 0"]),
        ("conflicting", 1, vec![]),
        ("conflicting", 0, vec![]),
    ]);
    let result = solve_snapshot(provider, &["asdf", "efgh"]);
    insta::assert_snapshot!(result);
}

/// The non-existing package should not be selected
#[test]
#[traced_test]
fn test_resolve_with_nonexisting() {
    let provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec!["b"]),
        ("asdf", 3, vec![]),
        ("b", 1, vec!["idontexist"]),
    ]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 3);
}

#[test]
#[traced_test]
fn test_resolve_with_nested_deps() {
    let provider = BundleBoxProvider::from_packages(&[
        (
            "apache-airflow",
            3,
            vec!["opentelemetry-api 2..4", "opentelemetry-exporter-otlp"],
        ),
        (
            "apache-airflow",
            2,
            vec!["opentelemetry-api 2..4", "opentelemetry-exporter-otlp"],
        ),
        ("apache-airflow", 1, vec![]),
        ("opentelemetry-api", 3, vec!["opentelemetry-sdk"]),
        ("opentelemetry-api", 2, vec![]),
        ("opentelemetry-api", 1, vec![]),
        ("opentelemetry-exporter-otlp", 1, vec!["opentelemetry-grpc"]),
        ("opentelemetry-grpc", 1, vec!["opentelemetry-api 1"]),
    ]);
    let requirements = provider.requirements(&["apache-airflow"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "apache-airflow");
    assert_eq!(solvable.record.version, 1);
}

#[test]
#[traced_test]
fn test_resolve_with_unknown_deps() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package(
        "opentelemetry-api",
        Pack::new(3).with_unknown_deps(),
        &[],
        &[],
    );
    provider.add_package("opentelemetry-api", Pack::new(2), &[], &[]);
    let requirements = provider.requirements(&["opentelemetry-api"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(
        pool.resolve_package_name(solvable.name),
        "opentelemetry-api"
    );
    assert_eq!(solvable.record.version, 2);
}

#[test]
#[traced_test]
fn test_resolve_and_cancel() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package(
        "opentelemetry-api",
        Pack::new(3).with_unknown_deps(),
        &[],
        &[],
    );
    provider.add_package(
        "opentelemetry-api",
        Pack::new(2).cancel_during_get_dependencies(),
        &[],
        &[],
    );
    let error = solve_unsat(provider, &["opentelemetry-api"]);
    insta::assert_snapshot!(error);
}

/// Locking a specific package version in this case a lower version namely `3`
/// should result in the higher package not being considered
#[test]
fn test_resolve_locked_top_level() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("asdf", 4, vec![]), ("asdf", 3, vec![])]);
    provider.set_locked("asdf", 3);

    let requirements = provider.requirements(&["asdf"]);

    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable_id = solved[0];
    assert_eq!(pool.resolve_solvable(solvable_id).record.version, 3);
}

/// Should ignore lock when it is not a top level package and a newer version
/// exists without it
#[test]
fn test_resolve_ignored_locked_top_level() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec![]),
        ("asdf", 3, vec!["fgh"]),
        ("fgh", 1, vec![]),
    ]);

    provider.set_locked("fgh", 1);

    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 4);
}

/// Test checks if favoring without a conflict results in a package upgrade
#[test]
fn test_resolve_favor_without_conflict() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("a", 2, vec![]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
    ]);
    provider.set_favored("a", 1);
    provider.set_favored("b", 1);

    // Already installed: A=1; B=1
    let result = solve_snapshot(provider, &["a", "b 2"]);
    insta::assert_snapshot!(result, @r###"
        a=1
        b=2
        "###);
}

#[test]
fn test_resolve_favor_with_conflict() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["c 1"]),
        ("a", 2, vec![]),
        ("b", 1, vec!["c 1"]),
        ("b", 2, vec!["c 2"]),
        ("c", 1, vec![]),
        ("c", 2, vec![]),
    ]);
    provider.set_favored("a", 1);
    provider.set_favored("b", 1);
    provider.set_favored("c", 1);

    let result = solve_snapshot(provider, &["a", "b 2"]);
    insta::assert_snapshot!(result, @r###"
        a=2
        b=2
        c=2
        "###);
}

#[test]
fn test_resolve_cyclic() {
    let provider =
        BundleBoxProvider::from_packages(&[("a", 2, vec!["b 0..10"]), ("b", 5, vec!["a 2..4"])]);
    let requirements = provider.requirements(&["a 0..100"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=2
        b=5
        "###);
}

#[test]
fn test_resolve_union_requirements() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("b", 1, vec![]),
        ("c", 1, vec!["a"]),
        ("d", 1, vec!["b"]),
        ("e", 1, vec!["a | b"]),
    ]);

    // Make d conflict with a=1
    provider.add_package("f", 1.into(), &["b"], &["a 2"]);

    let result = solve_snapshot(provider, &["c | d", "e", "f"]);
    assert_snapshot!(result, @r###"
        b=1
        d=1
        e=1
        f=1
        "###);
}

#[test]
fn test_unsat_locked_and_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1, vec!["c 2"]),
        ("c", 2, vec![]),
        ("c", 1, vec![]),
    ]);
    provider.set_locked("c", 1);
    insta::assert_snapshot!(solve_snapshot(provider, &["asdf"]));
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_no_candidates_for_child_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec!["c 2"]), ("c", 1, vec![])]);
    let error = solve_unsat(provider, &["asdf"]);
    insta::assert_snapshot!(error);
}

//
#[test]
fn test_unsat_no_candidates_for_child_2() {
    let provider = BundleBoxProvider::from_packages(&[("a", 41, vec!["B 0..20"])]);
    let error = solve_unsat(provider, &["a 0..1000"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_missing_top_level_dep_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    let error = solve_unsat(provider, &["fghj"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_missing_top_level_dep_2() {
    let provider = BundleBoxProvider::from_packages(&[("a", 41, vec!["b 15"]), ("b", 15, vec![])]);
    let error = solve_unsat(provider, &["a 41", "b 14"]);
    insta::assert_snapshot!(error);
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_after_backtracking() {
    let provider = BundleBoxProvider::from_packages(&[
        ("b", 7, vec!["d 1"]),
        ("b", 6, vec!["d 1"]),
        ("c", 1, vec!["d 2"]),
        ("c", 2, vec!["d 2"]),
        ("d", 2, vec![]),
        ("d", 1, vec![]),
        ("e", 1, vec![]),
        ("e", 2, vec![]),
    ]);

    let error = solve_unsat(provider, &["b", "c", "e"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_incompatible_root_requirements() {
    let provider = BundleBoxProvider::from_packages(&[("a", 2, vec![]), ("a", 5, vec![])]);
    let error = solve_unsat(provider, &["a 0..4", "a 5..10"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_bluesky_conflict() {
    let provider = BundleBoxProvider::from_packages(&[
        ("suitcase-utils", 54, vec![]),
        ("suitcase-utils", 53, vec![]),
        (
            "bluesky-widgets",
            42,
            vec![
                "bluesky-live 0..10",
                "numpy 0..10",
                "python 0..10",
                "suitcase-utils 0..54",
            ],
        ),
        ("bluesky-live", 1, vec![]),
        ("numpy", 1, vec![]),
        ("python", 1, vec![]),
    ]);
    let error = solve_unsat(
        provider,
        &["bluesky-widgets 0..100", "suitcase-utils 54..100"],
    );
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_pubgrub_article() {
    // Taken from the pubgrub article: https://nex3.medium.com/pubgrub-2fb6470504f
    let provider = BundleBoxProvider::from_packages(&[
        ("menu", 15, vec!["dropdown 2..3"]),
        ("menu", 10, vec!["dropdown 1..2"]),
        ("dropdown", 2, vec!["icons 2"]),
        ("dropdown", 1, vec!["intl 3"]),
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
    ]);
    let error = solve_unsat(provider, &["menu", "icons 1", "intl 5"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_applies_graph_compression() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b"]),
        ("a", 9, vec!["b"]),
        ("b", 100, vec!["c 0..100"]),
        ("b", 42, vec!["c 0..100"]),
        ("c", 103, vec![]),
        ("c", 101, vec![]),
        ("c", 100, vec![]),
        ("c", 99, vec![]),
    ]);
    let error = solve_unsat(provider, &["a", "c 101..104"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_constrains() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("a", 9, vec!["b 50..100"]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);

    provider.add_package("c", 10.into(), &[], &["b 0..50"]);
    provider.add_package("c", 8.into(), &[], &["b 0..50"]);
    let error = solve_unsat(provider, &["a", "c"]);
    insta::assert_snapshot!(error);
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_constrains_2() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b"]),
        ("a", 2, vec!["b"]),
        ("b", 1, vec!["c 1"]),
        ("b", 2, vec!["c 2"]),
    ]);

    provider.add_package("c", 1.into(), &[], &["a 3"]);
    provider.add_package("c", 2.into(), &[], &["a 3"]);
    let error = solve_unsat(provider, &["a"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_missing_dep() {
    let provider = BundleBoxProvider::from_packages(&[("a", 2, vec!["missing"]), ("a", 1, vec![])]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[tracing_test::traced_test]
fn test_no_backtracking() {
    let provider = BundleBoxProvider::from_packages(&[
        ("quetz-server", 2, vec!["pydantic 10..20"]),
        ("quetz-server", 1, vec!["pydantic 0..10"]),
        ("pydantic", 1, vec![]),
        ("pydantic", 2, vec![]),
        ("pydantic", 3, vec![]),
        ("pydantic", 4, vec![]),
        ("pydantic", 5, vec![]),
        ("pydantic", 6, vec![]),
        ("pydantic", 7, vec![]),
        ("pydantic", 8, vec![]),
        ("pydantic", 9, vec![]),
        ("pydantic", 10, vec![]),
        ("pydantic", 11, vec![]),
        ("pydantic", 12, vec![]),
        ("pydantic", 13, vec![]),
        ("pydantic", 14, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(
        provider,
        &["quetz-server", "pydantic 0..10"]
    ));
}

#[test]
#[tracing_test::traced_test]
fn test_incremental_crash() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 3, vec!["missing"]),
        ("a", 2, vec!["missing"]),
        ("a", 1, vec!["b"]),
        ("b", 2, vec!["a 2..4"]),
        ("b", 1, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[traced_test]
fn test_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 2, vec!["b"]),
        ("a", 1, vec!["c"]),
        ("b", 1, vec![]),
        ("c", 1, vec![]),
    ]);
    provider.exclude("b", 1, "it is externally excluded");
    provider.exclude("c", 1, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_merge_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![]), ("a", 2, vec![])]);
    provider.exclude("a", 1, "it is externally excluded");
    provider.exclude("a", 2, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[traced_test]
fn test_merge_installable() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("a", 2, vec![]),
        ("a", 3, vec![]),
        ("a", 4, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a 0..3", "a 3..5"]));
}

#[test]
fn test_root_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![])]);
    provider.exclude("a", 1, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_constraints() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("c", 1, vec![]),
    ]);
    let requirements = provider.requirements(&["a 0..10"]);
    let constraints = provider.requirements(&["b 1..2", "c"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=1
        b=1
        "###);
}

#[test]
fn test_solve_with_additional() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("c", 1, vec![]),
        ("d", 1, vec![]),
        ("e", 1, vec!["d"]),
        ("locked", 1, vec![]),
        ("locked", 2, vec![]),
    ]);

    provider.set_locked("locked", 2);

    let requirements = provider.requirements(&["a 0..10"]);
    let constraints = provider.requirements(&["b 1..2", "c"]);

    let extra_solvables = [
        provider.solvable_id("b", 2),
        provider.solvable_id("c", 1),
        provider.solvable_id("e", 1),
        // Does not obey the locked clause since it has not been requested
        // in a version set by another solvable
        provider.solvable_id("locked", 1),
        provider.solvable_id("unknown-deps", Pack::new(1).with_unknown_deps()),
    ];

    let mut solver = Solver::new(provider);

    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints)
        .soft_requirements(extra_solvables);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
        a=1
        b=1
        c=1
        d=1
        e=1
        locked=1
        "###);
}

#[test]
fn test_solve_with_additional_with_constrains() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("b", 3, vec![]),
        ("c", 1, vec![]),
        ("d", 1, vec!["f"]),
        ("e", 1, vec!["c"]),
    ]);

    provider.add_package("f", 1.into(), &[], &["c 2..3"]);
    provider.add_package("g", 1.into(), &[], &["b 2..3"]);
    provider.add_package("h", 1.into(), &[], &["b 1..2"]);
    provider.add_package("i", 1.into(), &[], &[]);
    provider.add_package("j", 1.into(), &["i"], &[]);
    provider.add_package("k", 1.into(), &["i"], &[]);
    provider.add_package("l", 1.into(), &["j", "k"], &[]);

    let requirements = provider.requirements(&["a 0..10", "e"]);
    let constraints = provider.requirements(&["b 1..2", "c", "k 2..3"]);

    let extra_solvables = [
        provider.solvable_id("d", 1),
        provider.solvable_id("g", 1),
        provider.solvable_id("h", 1),
        provider.solvable_id("j", 1),
        provider.solvable_id("l", 1),
        provider.solvable_id("k", 1),
    ];

    let mut solver = Solver::new(provider);

    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints)
        .soft_requirements(extra_solvables);

    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
        a=1
        b=1
        c=1
        e=1
        h=1
        i=1
        j=1
        "###);
}

#[test]
fn test_snapshot() {
    let provider = BundleBoxProvider::from_packages(&[
        ("menu", 15, vec!["dropdown 2..3"]),
        ("menu", 10, vec!["dropdown 1..2"]),
        ("dropdown", 2, vec!["icons 2"]),
        ("dropdown", 1, vec!["intl 3"]),
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
    ]);

    let menu_name_id = provider.package_name("menu");

    let snapshot = provider.into_snapshot();

    #[cfg(feature = "serde")]
    serialize_snapshot(&snapshot, "snapshot_pubgrub_menu.json");

    let mut snapshot_provider = snapshot.provider();

    let menu_req = snapshot_provider.add_package_requirement(menu_name_id, "*");

    assert_snapshot!(solve_for_snapshot(snapshot_provider, &[menu_req], &[]));
}

#[test]
fn test_snapshot_union_requirements() {
    let provider = BundleBoxProvider::from_packages(&[
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
        ("union", 1, vec!["icons 2 | intl"]),
    ]);

    let intl_name_id = provider.package_name("intl");
    let union_name_id = provider.package_name("union");

    let snapshot = provider.into_snapshot();

    let mut snapshot_provider = snapshot.provider();

    let intl_req = snapshot_provider.add_package_requirement(intl_name_id, "*");
    let union_req = snapshot_provider.add_package_requirement(union_name_id, "*");

    assert_snapshot!(solve_for_snapshot(
        snapshot_provider,
        &[intl_req, union_req],
        &[]
    ));
}

#[test]
fn test_root_constraints() {
    let provider =
        BundleBoxProvider::from_packages(&[("icons", 1, vec![]), ("union", 1, vec!["icons"])]);

    let union_name_id = provider.package_name("union");

    let snapshot = provider.into_snapshot();

    let mut snapshot_provider = snapshot.provider();

    let union_req = snapshot_provider.add_package_requirement(union_name_id, "*");
    let union_constraint = snapshot_provider.add_package_requirement(union_name_id, "5");

    assert_snapshot!(solve_for_snapshot(
        snapshot_provider,
        &[union_req],
        &[union_constraint]
    ));
}

#[test]
fn test_explicit_root_requirements() {
    let provider = BundleBoxProvider::from_packages(&[
        // `a` depends transitively on `b`
        ("a", 1, vec!["b"]),
        // `b` depends on `c`, but the highest version of `b` constrains `c` to `<2`.
        ("b", 1, vec!["c"]),
        ("b", 2, vec!["c 1..2"]),
        // `c` has more versions than `b`, so the heuristic will most likely pick `b` first.
        ("c", 1, vec![]),
        ("c", 2, vec![]),
        ("c", 3, vec![]),
        ("c", 4, vec![]),
        ("c", 5, vec![]),
    ]);

    // We require both `a` and `c` explicitly. The expected outcome will be that we
    // get the highest versions of `a` and `c` and a lower version of `b`.
    let requirements = provider.requirements(&["a", "c"]);

    let mut solver = Solver::new(provider);
    let problem = Problem::default().requirements(requirements);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    b=1
    c=5
    "###);
}

#[cfg(feature = "serde")]
fn serialize_snapshot(snapshot: &DependencySnapshot, destination: impl AsRef<std::path::Path>) {
    let file = std::io::BufWriter::new(std::fs::File::create(destination.as_ref()).unwrap());
    serde_json::to_writer_pretty(file, snapshot).unwrap()
}

fn solve_for_snapshot(
    provider: SnapshotProvider,
    root_reqs: &[VersionSetId],
    root_constraints: &[VersionSetId],
) -> String {
    let mut solver = Solver::new(provider);
    let problem = Problem::new()
        .requirements(root_reqs.iter().copied().map(Into::into).collect())
        .constraints(root_constraints.iter().copied().map(Into::into).collect());
    match solver.solve(problem) {
        Ok(solvables) => transaction_to_string(solver.provider(), &solvables),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

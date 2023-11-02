use indexmap::IndexMap;
use itertools::Itertools;
use resolvo::{
    range::Range, Candidates, DefaultSolvableDisplay, Dependencies, DependencyProvider, NameId,
    Pool, SolvableId, Solver, SolverCache, VersionSet, VersionSetId,
};
use std::{
    collections::HashMap,
    fmt::{Debug, Display, Formatter},
    io::stderr,
    io::Write,
    num::ParseIntError,
    str::FromStr,
};
use tracing_test::traced_test;

// Let's define our own packaging version system and dependency specification.
// This is a very simple version system, where a package is identified by a name and a version
// in which the version is just an integer. The version is a range so can be noted as 0..2
// or something of the sorts, we also support constrains which means it should not use that
// package version this is also represented with a range.
//
// You can also use just a single number for a range like `package 0` which means the range from 0..1 (excluding the end)
//
// Lets call the tuples of (Name, Version) a `Pack` and the tuples of (Name, Range<u32>) a `Spec`
//
// We also need to create a custom provider that tells us how to sort the candidates. This is unique to each
// packaging ecosystem. Let's call our ecosystem 'BundleBox' so that how we call the provider as well.

/// This is `Pack` which is a unique version and name in our bespoke packaging system
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
#[repr(transparent)]
struct Pack(u32);

impl From<u32> for Pack {
    fn from(value: u32) -> Self {
        Pack(value)
    }
}

impl From<i32> for Pack {
    fn from(value: i32) -> Self {
        Pack(value as u32)
    }
}

impl Display for Pack {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl FromStr for Pack {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        u32::from_str(s).map(Self)
    }
}

/// We can use this to see if a `Pack` is contained in a range of package versions or a `Spec`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Spec {
    name: String,
    versions: Range<Pack>,
}

impl Spec {
    pub fn new(name: String, versions: Range<Pack>) -> Self {
        Self { name, versions }
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

        fn version_range(s: Option<&&str>) -> Range<Pack> {
            if let Some(s) = s {
                let (start, end) = s
                    .split_once("..")
                    .map_or((*s, None), |(start, end)| (start, Some(end)));
                let start: Pack = start.parse().unwrap();
                let end = end
                    .map(FromStr::from_str)
                    .transpose()
                    .unwrap()
                    .unwrap_or(Pack(start.0 + 1));
                Range::between(start, end)
            } else {
                Range::full()
            }
        }

        let versions = version_range(split.get(1));

        Ok(Spec::new(name, versions))
    }
}

/// This provides sorting functionality for our `BundleBox` packaging system
#[derive(Default)]
struct BundleBoxProvider {
    pool: Pool<Range<Pack>>,
    packages: IndexMap<String, IndexMap<Pack, BundleBoxPackageDependencies>>,
    favored: HashMap<String, Pack>,
    locked: HashMap<String, Pack>,
    disabled: HashMap<String, HashMap<Pack, String>>,
}

struct BundleBoxPackageDependencies {
    dependencies: Vec<Spec>,
    constrains: Vec<Spec>,
}

impl BundleBoxProvider {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn requirements(&self, requirements: &[&str]) -> Vec<VersionSetId> {
        requirements
            .into_iter()
            .map(|dep| Spec::from_str(dep).unwrap())
            .map(|spec| {
                let dep_name = self.pool.intern_package_name(&spec.name);
                self.pool
                    .intern_version_set(dep_name, spec.versions.clone())
            })
            .collect()
    }

    pub fn from_packages(packages: &[(&str, u32, Vec<&str>)]) -> Self {
        let mut result = Self::new();
        for (name, version, deps) in packages {
            result.add_package(name, Pack(*version), deps, &[]);
        }
        result
    }

    pub fn set_favored(&mut self, package_name: &str, version: u32) {
        self.favored.insert(package_name.to_owned(), Pack(version));
    }

    pub fn set_disabled(&mut self, package_name: &str, version: u32, reason: impl Into<String>) {
        self.disabled
            .entry(package_name.to_owned())
            .or_default()
            .insert(Pack(version), reason.into());
    }

    pub fn set_locked(&mut self, package_name: &str, version: u32) {
        self.locked.insert(package_name.to_owned(), Pack(version));
    }

    pub fn add_package(
        &mut self,
        package_name: &str,
        package_version: Pack,
        dependencies: &[&str],
        constrains: &[&str],
    ) {
        let dependencies = dependencies
            .into_iter()
            .map(|dep| Spec::from_str(dep))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        let constrains = constrains
            .into_iter()
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
}

impl DependencyProvider<Range<Pack>> for BundleBoxProvider {
    fn pool(&self) -> &Pool<Range<Pack>> {
        &self.pool
    }

    fn sort_candidates(
        &self,
        _solver: &SolverCache<Range<Pack>, String, Self>,
        solvables: &mut [SolvableId],
    ) {
        solvables.sort_by(|a, b| {
            let a = self.pool.resolve_solvable(*a).inner();
            let b = self.pool.resolve_solvable(*b).inner();
            // We want to sort with highest version on top
            b.0.cmp(&a.0)
        });
    }

    fn get_candidates(&self, name: NameId) -> Option<Candidates> {
        let package_name = self.pool.resolve_package_name(name);
        let package = self.packages.get(package_name)?;

        let mut candidates = Candidates {
            candidates: Vec::with_capacity(package.len()),
            ..Candidates::default()
        };
        let favor = self.favored.get(package_name);
        let locked = self.locked.get(package_name);
        let disabled = self.disabled.get(package_name);
        for pack in package.keys() {
            let solvable = self.pool.intern_solvable(name, *pack);
            candidates.candidates.push(solvable);
            if Some(pack) == favor {
                candidates.favored = Some(solvable);
            }
            if Some(pack) == locked {
                candidates.locked = Some(solvable);
            }
            if let Some(disabled) = disabled.and_then(|d| d.get(pack)) {
                candidates
                    .disabled
                    .push((solvable, self.pool.intern_string(disabled)));
            }
        }

        Some(candidates)
    }

    fn get_dependencies(&self, solvable: SolvableId) -> Dependencies {
        let candidate = self.pool.resolve_solvable(solvable);
        let package_name = self.pool.resolve_package_name(candidate.name_id());
        let pack = candidate.inner();
        let Some(deps) = self.packages.get(package_name).and_then(|v| v.get(pack)) else {
            return Default::default();
        };

        let mut result = Dependencies {
            requirements: Vec::with_capacity(deps.dependencies.len()),
            constrains: Vec::with_capacity(deps.constrains.len()),
        };
        for req in &deps.dependencies {
            let dep_name = self.pool.intern_package_name(&req.name);
            let dep_spec = self.pool.intern_version_set(dep_name, req.versions.clone());
            result.requirements.push(dep_spec);
        }

        for req in &deps.constrains {
            let dep_name = self.pool.intern_package_name(&req.name);
            let dep_spec = self.pool.intern_version_set(dep_name, req.versions.clone());
            result.constrains.push(dep_spec);
        }

        result
    }
}

/// Create a string from a [`Transaction`]
fn transaction_to_string<VS: VersionSet>(pool: &Pool<VS>, solvables: &Vec<SolvableId>) -> String {
    use std::fmt::Write;
    let mut buf = String::new();
    for solvable in solvables
        .iter()
        .copied()
        .map(|s| s.display(pool).to_string())
        .sorted()
    {
        writeln!(buf, "{solvable}").unwrap();
    }

    buf
}

/// Unsat so that we can view the problem
fn solve_unsat(provider: BundleBoxProvider, specs: &[&str]) -> String {
    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider);
    match solver.solve(requirements) {
        Ok(_) => panic!("expected unsat, but a solution was found"),
        Err(problem) => {
            // Write the problem graphviz to stderr
            let graph = problem.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph.graphviz(&mut output, solver.pool(), true).unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            problem
                .display_user_friendly(&solver, &DefaultSolvableDisplay)
                .to_string()
        }
    }
}

/// Solve the problem and returns either a solution represented as a string or an error string.
fn solve_snapshot(provider: BundleBoxProvider, specs: &[&str]) -> String {
    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider);
    match solver.solve(requirements) {
        Ok(solvables) => transaction_to_string(solver.pool(), &solvables),
        Err(problem) => {
            // Write the problem graphviz to stderr
            let graph = problem.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph.graphviz(&mut output, solver.pool(), true).unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            problem
                .display_user_friendly(&solver, &DefaultSolvableDisplay)
                .to_string()
        }
    }
}

/// Test whether we can select a version, this is the most basic operation
#[test]
fn test_unit_propagation_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    let root_requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let solved = solver.solve(root_requirements).unwrap();

    assert_eq!(solved.len(), 1);
    let solvable = solver.pool().resolve_solvable(solved[0]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "asdf"
    );
    assert_eq!(solvable.inner().0, 1);
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
    let solved = solver.solve(requirements).unwrap();

    assert_eq!(solved.len(), 2);

    let solvable = solver.pool().resolve_solvable(solved[0]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "asdf"
    );
    assert_eq!(solvable.inner().0, 1);

    let solvable = solver.pool().resolve_solvable(solved[1]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "efgh"
    );
    assert_eq!(solvable.inner().0, 4);
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
    let solved = solver.solve(requirements).unwrap();

    assert_eq!(solved.len(), 2);

    let solvable = solver.pool().resolve_solvable(solved[0]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "asdf"
    );
    assert_eq!(solvable.inner().0, 2);

    let solvable = solver.pool().resolve_solvable(solved[1]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "efgh"
    );
    assert_eq!(solvable.inner().0, 5);
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
    let requirements = provider.requirements(&["asdf", "efgh"]);
    let mut solver = Solver::new(provider);
    let solved = solver.solve(requirements);
    let solved = match solved {
        Ok(solved) => transaction_to_string(solver.pool(), &solved),
        Err(p) => panic!(
            "{}",
            p.display_user_friendly(&solver, &DefaultSolvableDisplay)
        ),
    };
    insta::assert_snapshot!(solved);
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
    let solved = solver.solve(requirements).unwrap();

    assert_eq!(solved.len(), 1);

    let solvable = solver.pool().resolve_solvable(solved[0]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "asdf"
    );
    assert_eq!(solvable.inner().0, 3);
}

/// Locking a specific package version in this case a lower version namely `3` should result
/// in the higher package not being considered
#[test]
fn test_resolve_locked_top_level() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("asdf", 4, vec![]), ("asdf", 3, vec![])]);
    provider.set_locked("asdf", 3);

    let requirements = provider.requirements(&["asdf"]);

    let mut solver = Solver::new(provider);
    let solved = solver.solve(requirements).unwrap();

    assert_eq!(solved.len(), 1);
    let solvable_id = solved[0];
    assert_eq!(solver.pool().resolve_solvable(solvable_id).inner().0, 3);
}

/// Should ignore lock when it is not a top level package and a newer version exists without it
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
    let solved = solver.solve(requirements).unwrap();

    assert_eq!(solved.len(), 1);
    let solvable = solver.pool().resolve_solvable(solved[0]);

    assert_eq!(
        solver.pool().resolve_package_name(solvable.name_id()),
        "asdf"
    );
    assert_eq!(solvable.inner().0, 4);
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

    let requirements = provider.requirements(&["a", "b 2"]);

    // Already installed: A=1; B=1
    let mut solver = Solver::new(provider);
    let solved = solver.solve(requirements);
    let solved = match solved {
        Ok(solved) => solved,
        Err(p) => panic!(
            "{}",
            p.display_user_friendly(&solver, &DefaultSolvableDisplay)
        ),
    };

    let result = transaction_to_string(&solver.pool(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=1
        b=2
        "###);
}

//
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

    let requirements = provider.requirements(&["a", "b 2"]);

    let mut solver = Solver::new(provider);
    let solved = solver.solve(requirements);
    let solved = match solved {
        Ok(solved) => solved,
        Err(p) => panic!(
            "{}",
            p.display_user_friendly(&solver, &DefaultSolvableDisplay)
        ),
    };

    let result = transaction_to_string(&solver.pool(), &solved);
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
    let solved = solver.solve(requirements).unwrap();

    let result = transaction_to_string(&solver.pool(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=2
        b=5
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

//
#[test]
fn test_unsat_constrains() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("a", 9, vec!["b 50..100"]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);

    provider.add_package("c", 10.into(), &vec![], &vec!["b 0..50"]);
    provider.add_package("c", 8.into(), &vec![], &vec!["b 0..50"]);
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

    provider.add_package("c", 1.into(), &vec![], &vec!["a 3"]);
    provider.add_package("c", 2.into(), &vec![], &vec!["a 3"]);
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
fn test_disabled() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 2, vec!["b"]),
        ("a", 1, vec!["c"]),
        ("b", 1, vec![]),
        ("c", 1, vec![]),
    ]);
    provider.set_disabled("b", 1, "it is externally disabled");
    provider.set_disabled("c", 1, "it is externally disabled");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_merge_disabled() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("a", 2, vec![]),
    ]);
    provider.set_disabled("a", 1, "it is externally disabled");
    provider.set_disabled("a", 2, "it is externally disabled");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_root_disabled() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
    ]);
    provider.set_disabled("a", 1, "it is externally disabled");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

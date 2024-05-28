//! Types to examine why a problem was unsatisfiable, and to report the causes to the user.

use std::collections::{HashSet};
use ahash::HashMap;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::rc::Rc;

use itertools::Itertools;
use petgraph::graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex};
use petgraph::visit::{Bfs, DfsPostOrder, EdgeRef};
use petgraph::Direction;

use crate::{
    internal::id::{ClauseId, SolvableId, StringId, VersionSetId},
    pool::Pool,
    runtime::AsyncRuntime,
    solver::{clause::Clause, Solver},
    DependencyProvider, PackageName, SolvableDisplay, VersionSet,
};

/// Represents the cause of the solver being unable to find a solution
#[derive(Debug)]
pub struct Problem {
    /// The clauses involved in an unsatisfiable conflict
    clauses: Vec<ClauseId>,
}

impl Problem {
    pub(crate) fn default() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    pub(crate) fn add_clause(&mut self, clause_id: ClauseId) {
        if !self.clauses.contains(&clause_id) {
            self.clauses.push(clause_id);
        }
    }

    /// Generates a graph representation of the problem (see [`ProblemGraph`] for details)
    pub fn graph<VS: VersionSet, N: PackageName, D: DependencyProvider<VS, N>, RT: AsyncRuntime>(
        &self,
        solver: &Solver<VS, N, D, RT>,
    ) -> ProblemGraph {
        let mut graph = DiGraph::<ProblemNode, ProblemEdge>::default();
        let mut nodes: HashMap<SolvableId, NodeIndex> = HashMap::default();
        let mut excluded_nodes: HashMap<StringId, NodeIndex> = HashMap::default();

        let root_node = Self::add_node(&mut graph, &mut nodes, SolvableId::root());
        let unresolved_node = graph.add_node(ProblemNode::UnresolvedDependency);

        for clause_id in &self.clauses {
            let clause = &solver.clauses.borrow()[*clause_id].kind;
            match clause {
                Clause::InstallRoot => (),
                Clause::Excluded(solvable, reason) => {
                    tracing::info!("{solvable:?} is excluded");
                    let package_node = Self::add_node(&mut graph, &mut nodes, *solvable);
                    let excluded_node = excluded_nodes
                        .entry(*reason)
                        .or_insert_with(|| graph.add_node(ProblemNode::Excluded(*reason)));

                    graph.add_edge(
                        package_node,
                        *excluded_node,
                        ProblemEdge::Conflict(ConflictCause::Excluded),
                    );
                }
                Clause::Learnt(..) => unreachable!(),
                &Clause::Requires(package_id, version_set_id) => {
                    let package_node = Self::add_node(&mut graph, &mut nodes, package_id);

                    let candidates = solver.async_runtime.block_on(solver.cache.get_or_cache_sorted_candidates(version_set_id)).unwrap_or_else(|_| {
                        unreachable!("The version set was used in the solver, so it must have been cached. Therefore cancellation is impossible here and we cannot get an `Err(...)`")
                    });
                    if candidates.is_empty() {
                        tracing::info!(
                            "{package_id:?} requires {version_set_id:?}, which has no candidates"
                        );
                        graph.add_edge(
                            package_node,
                            unresolved_node,
                            ProblemEdge::Requires(version_set_id),
                        );
                    } else {
                        for &candidate_id in candidates {
                            tracing::info!("{package_id:?} requires {candidate_id:?}");

                            let candidate_node =
                                Self::add_node(&mut graph, &mut nodes, candidate_id);
                            graph.add_edge(
                                package_node,
                                candidate_node,
                                ProblemEdge::Requires(version_set_id),
                            );
                        }
                    }
                }
                &Clause::Lock(locked, forbidden) => {
                    let node2_id = Self::add_node(&mut graph, &mut nodes, forbidden);
                    let conflict = ConflictCause::Locked(locked);
                    graph.add_edge(root_node, node2_id, ProblemEdge::Conflict(conflict));
                }
                &Clause::ForbidMultipleInstances(instance1_id, instance2_id) => {
                    let node1_id = Self::add_node(&mut graph, &mut nodes, instance1_id);
                    let node2_id = Self::add_node(&mut graph, &mut nodes, instance2_id);

                    let conflict = ConflictCause::ForbidMultipleInstances;
                    graph.add_edge(node1_id, node2_id, ProblemEdge::Conflict(conflict));
                }
                &Clause::Constrains(package_id, dep_id, version_set_id) => {
                    let package_node = Self::add_node(&mut graph, &mut nodes, package_id);
                    let dep_node = Self::add_node(&mut graph, &mut nodes, dep_id);

                    graph.add_edge(
                        package_node,
                        dep_node,
                        ProblemEdge::Conflict(ConflictCause::Constrains(version_set_id)),
                    );
                }
            }
        }

        let unresolved_node = if graph
            .edges_directed(unresolved_node, Direction::Incoming)
            .next()
            .is_none()
        {
            graph.remove_node(unresolved_node);
            None
        } else {
            Some(unresolved_node)
        };

        // Sanity check: all nodes are reachable from root
        let mut visited_nodes = HashSet::new();
        let mut bfs = Bfs::new(&graph, root_node);
        while let Some(nx) = bfs.next(&graph) {
            visited_nodes.insert(nx);
        }
        assert_eq!(graph.node_count(), visited_nodes.len());

        ProblemGraph {
            graph,
            root_node,
            unresolved_node,
        }
    }

    fn add_node(
        graph: &mut DiGraph<ProblemNode, ProblemEdge>,
        nodes: &mut HashMap<SolvableId, NodeIndex>,
        solvable_id: SolvableId,
    ) -> NodeIndex {
        *nodes
            .entry(solvable_id)
            .or_insert_with(|| graph.add_node(ProblemNode::Solvable(solvable_id)))
    }

    /// Display a user-friendly error explaining the problem
    pub fn display_user_friendly<
        'a,
        VS: VersionSet,
        N: PackageName + Display,
        D: DependencyProvider<VS, N>,
        M: SolvableDisplay<VS, N>,
        RT: AsyncRuntime,
    >(
        &self,
        solver: &'a Solver<VS, N, D, RT>,
        pool: Rc<Pool<VS, N>>,
        merged_solvable_display: &'a M,
    ) -> DisplayUnsat<'a, VS, N, M> {
        let graph = self.graph(solver);
        DisplayUnsat::new(graph, pool, merged_solvable_display)
    }
}

/// A node in the graph representation of a [`Problem`]
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ProblemNode {
    /// Node corresponding to a solvable
    Solvable(SolvableId),
    /// Node representing a dependency without candidates
    UnresolvedDependency,
    /// Node representing an exclude reason
    Excluded(StringId),
}

impl ProblemNode {
    fn solvable_id(self) -> SolvableId {
        match self {
            ProblemNode::Solvable(solvable_id) => solvable_id,
            ProblemNode::UnresolvedDependency => {
                panic!("expected solvable node, found unresolved dependency")
            }
            ProblemNode::Excluded(_) => {
                panic!("expected solvable node, found excluded node")
            }
        }
    }
}

/// An edge in the graph representation of a [`Problem`]
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ProblemEdge {
    /// The target node is a candidate for the dependency specified by the version set
    Requires(VersionSetId),
    /// The target node is involved in a conflict, caused by `ConflictCause`
    Conflict(ConflictCause),
}

impl ProblemEdge {
    fn try_requires(self) -> Option<VersionSetId> {
        match self {
            ProblemEdge::Requires(match_spec_id) => Some(match_spec_id),
            ProblemEdge::Conflict(_) => None,
        }
    }

    fn requires(self) -> VersionSetId {
        match self {
            ProblemEdge::Requires(match_spec_id) => match_spec_id,
            ProblemEdge::Conflict(_) => panic!("expected requires edge, found conflict"),
        }
    }
}

/// Conflict causes
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ConflictCause {
    /// The solvable is locked
    Locked(SolvableId),
    /// The target node is constrained by the specified version set
    Constrains(VersionSetId),
    /// It is forbidden to install multiple instances of the same dependency
    ForbidMultipleInstances,
    /// The node was excluded
    Excluded,
}

/// Represents a node that has been merged with others
///
/// Merging is done to simplify error messages, and happens when a group of nodes satisfies the
/// following criteria:
///
/// - They all have the same name
/// - They all have the same predecessor nodes
/// - They all have the same successor nodes
pub(crate) struct MergedProblemNode {
    pub ids: Vec<SolvableId>,
}

/// Graph representation of [`Problem`]
///
/// The root of the graph is the "root solvable". Note that not all the solvable's requirements are
/// included in the graph, only those that are directly or indirectly involved in the conflict. See
/// [`ProblemNode`] and [`ProblemEdge`] for the kinds of nodes and edges that make up the graph.
pub struct ProblemGraph {
    graph: DiGraph<ProblemNode, ProblemEdge>,
    root_node: NodeIndex,
    unresolved_node: Option<NodeIndex>,
}

impl ProblemGraph {
    /// Writes a graphviz graph that represents this instance to the specified output.
    pub fn graphviz<VS: VersionSet>(
        &self,
        f: &mut impl std::io::Write,
        pool: &Pool<VS>,
        simplify: bool,
    ) -> Result<(), std::io::Error> {
        let graph = &self.graph;

        let merged_nodes = if simplify {
            self.simplify(pool)
        } else {
            HashMap::default()
        };

        write!(f, "digraph {{")?;
        for nx in graph.node_indices() {
            let id = match graph.node_weight(nx).as_ref().unwrap() {
                ProblemNode::Solvable(id) => *id,
                _ => continue,
            };

            // If this is a merged node, skip it unless it is the first one in the group
            if let Some(merged) = merged_nodes.get(&id) {
                if id != merged.ids[0] {
                    continue;
                }
            }

            let solvable = pool.resolve_internal_solvable(id);
            let mut added_edges = HashSet::new();
            for edge in graph.edges_directed(nx, Direction::Outgoing) {
                let target = *graph.node_weight(edge.target()).unwrap();

                let color = match edge.weight() {
                    ProblemEdge::Requires(_) if target != ProblemNode::UnresolvedDependency => {
                        "black"
                    }
                    _ => "red",
                };

                let label = match edge.weight() {
                    ProblemEdge::Requires(version_set_id)
                    | ProblemEdge::Conflict(ConflictCause::Constrains(version_set_id)) => {
                        pool.resolve_version_set(*version_set_id).to_string()
                    }
                    ProblemEdge::Conflict(ConflictCause::ForbidMultipleInstances)
                    | ProblemEdge::Conflict(ConflictCause::Locked(_)) => {
                        "already installed".to_string()
                    }
                    ProblemEdge::Conflict(ConflictCause::Excluded) => "excluded".to_string(),
                };

                let target = match target {
                    ProblemNode::Solvable(mut solvable_2) => {
                        // If the target node has been merged, replace it by the first id in the group
                        if let Some(merged) = merged_nodes.get(&solvable_2) {
                            solvable_2 = merged.ids[0];

                            // Skip the edge if we would be adding a duplicate
                            if !added_edges.insert(solvable_2) {
                                continue;
                            }
                        }

                        solvable_2.display(pool).to_string()
                    }
                    ProblemNode::UnresolvedDependency => "unresolved".to_string(),
                    ProblemNode::Excluded(reason) => {
                        format!("reason: {}", pool.resolve_string(reason))
                    }
                };

                write!(
                    f,
                    "\"{}\" -> \"{}\"[color={color}, label=\"{label}\"];",
                    solvable.display(pool),
                    target
                )?;
            }
        }
        write!(f, "}}")
    }

    /// Simplifies and collapses nodes so that these can be considered the same candidate
    fn simplify<VS: VersionSet, N: PackageName>(
        &self,
        pool: &Pool<VS, N>,
    ) -> HashMap<SolvableId, Rc<MergedProblemNode>> {
        let graph = &self.graph;

        // Gather information about nodes that can be merged
        let mut maybe_merge = HashMap::default();
        for node_id in graph.node_indices() {
            let candidate = match graph[node_id] {
                ProblemNode::UnresolvedDependency | ProblemNode::Excluded(_) => continue,
                ProblemNode::Solvable(solvable_id) => {
                    if solvable_id.is_root() {
                        continue;
                    } else {
                        solvable_id
                    }
                }
            };

            let predecessors: Vec<_> = graph
                .edges_directed(node_id, Direction::Incoming)
                .map(|e| e.source())
                .sorted_unstable()
                .collect();
            let successors: Vec<_> = graph
                .edges(node_id)
                .map(|e| e.target())
                .sorted_unstable()
                .collect();

            let name = pool.resolve_solvable(candidate).name;

            let entry = maybe_merge
                .entry((name, predecessors, successors))
                .or_insert(Vec::new());

            entry.push((node_id, candidate));
        }

        let mut merged_candidates = HashMap::default();
        for m in maybe_merge.into_values() {
            if m.len() > 1 {
                let m = Rc::new(MergedProblemNode {
                    ids: m.into_iter().map(|(_, snd)| snd).collect(),
                });
                for &id in &m.ids {
                    merged_candidates.insert(id, m.clone());
                }
            }
        }

        merged_candidates
    }

    fn get_installable_set(&self) -> HashSet<NodeIndex> {
        let mut installable = HashSet::new();

        // Definition: a package is installable if it does not have any outgoing conflicting edges
        // and if each of its dependencies has at least one installable option.

        // Algorithm: propagate installability bottom-up
        let mut dfs = DfsPostOrder::new(&self.graph, self.root_node);
        'outer_loop: while let Some(nx) = dfs.next(&self.graph) {
            if self.unresolved_node == Some(nx) {
                // The unresolved node isn't installable
                continue;
            }

            // Determine any incoming "exclude" edges to the node. This would indicate that the
            // node is disabled for external reasons.
            let excluding_edges = self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .any(|e| matches!(e.weight(), ProblemEdge::Conflict(ConflictCause::Excluded)));
            if excluding_edges {
                // Nodes with incoming disabling edges aren't installable
                continue;
            }

            let outgoing_conflicts = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .any(|e| matches!(e.weight(), ProblemEdge::Conflict(_)));
            if outgoing_conflicts {
                // Nodes with outgoing conflicts aren't installable
                continue;
            }

            // Edges grouped by dependency
            let dependencies = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|e| match e.weight() {
                    ProblemEdge::Requires(version_set_id) => (version_set_id, e.target()),
                    ProblemEdge::Conflict(_) => unreachable!(),
                })
                .chunk_by(|(&version_set_id, _)| version_set_id);

            for (_, mut deps) in &dependencies {
                if deps.all(|(_, target)| !installable.contains(&target)) {
                    // No installable options for this dep
                    continue 'outer_loop;
                }
            }

            // The package is installable!
            installable.insert(nx);
        }

        installable
    }

    fn get_missing_set(&self) -> HashSet<NodeIndex> {
        // Definition: a package is missing if it is not involved in any conflicts, yet it is not
        // installable

        let mut missing = HashSet::new();
        match self.unresolved_node {
            None => return missing,
            Some(nx) => missing.insert(nx),
        };

        // Algorithm: propagate missing bottom-up
        let mut dfs = DfsPostOrder::new(&self.graph, self.root_node);
        while let Some(nx) = dfs.next(&self.graph) {
            let outgoing_conflicts = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .any(|e| matches!(e.weight(), ProblemEdge::Conflict(_)));
            if outgoing_conflicts {
                // Nodes with outgoing conflicts aren't missing
                continue;
            }

            // Edges grouped by dependency
            let dependencies = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|e| match e.weight() {
                    ProblemEdge::Requires(version_set_id) => (version_set_id, e.target()),
                    ProblemEdge::Conflict(_) => unreachable!(),
                })
                .chunk_by(|(&version_set_id, _)| version_set_id);

            // Missing if at least one dependency is missing
            if dependencies
                .into_iter()
                .any(|(_, mut deps)| deps.all(|(_, target)| missing.contains(&target)))
            {
                missing.insert(nx);
            }
        }

        missing
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum ChildOrder {
    HasRemainingSiblings,
    Last,
}

struct Indenter {
    levels: Vec<ChildOrder>,
    top_level_indent: bool,
}

impl Indenter {
    fn new(top_level_indent: bool) -> Self {
        Self {
            levels: Vec::new(),
            top_level_indent,
        }
    }

    fn is_at_top_level(&self) -> bool {
        self.levels.len() == 1
    }

    fn push_level(&self) -> Self {
        self.push_level_with_order(ChildOrder::HasRemainingSiblings)
    }

    fn push_level_with_order(&self, order: ChildOrder) -> Self {
        let mut levels = self.levels.clone();
        levels.push(order);
        Self {
            levels,
            top_level_indent: self.top_level_indent,
        }
    }

    fn set_last(&mut self) {
        *self.levels.last_mut().unwrap() = ChildOrder::Last;
    }

    fn get_indent(&self) -> String {
        assert!(!self.levels.is_empty());

        let mut s = String::new();

        let deepest_level = self.levels.len() - 1;

        for (level, &order) in self.levels.iter().enumerate() {
            if level == 0 && !self.top_level_indent {
                // Skip
                continue;
            }

            let is_at_deepest_level = level == deepest_level;

            let tree_prefix = match (is_at_deepest_level, order) {
                (true, ChildOrder::HasRemainingSiblings) => "├─",
                (true, ChildOrder::Last) => "└─",
                (false, ChildOrder::HasRemainingSiblings) => "│ ",
                (false, ChildOrder::Last) => "  ",
            };

            // TODO: are these the right characters? Alternatives: https://en.wikipedia.org/wiki/Box-drawing_character or look at mamba

            s.push_str(tree_prefix);
            s.push(' ');
        }

        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_indenter_without_top_level_indent() {
        let indenter = Indenter::new(false);

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "└─ ");
    }

    #[test]
    fn test_indenter_with_multiple_siblings() {
        let indenter = Indenter::new(true);

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "└─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::HasRemainingSiblings);
        assert_eq!(indenter.get_indent(), "   ├─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "   │  └─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "   │     └─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::HasRemainingSiblings);
        assert_eq!(indenter.get_indent(), "   │        ├─ ");
    }
}

/// A struct implementing [`fmt::Display`] that generates a user-friendly representation of a
/// problem graph
pub struct DisplayUnsat<'pool, VS: VersionSet, N: PackageName + Display, M: SolvableDisplay<VS, N>>
{
    graph: ProblemGraph,
    merged_candidates: HashMap<SolvableId, Rc<MergedProblemNode>>,
    installable_set: HashSet<NodeIndex>,
    missing_set: HashSet<NodeIndex>,
    pool: Rc<Pool<VS, N>>,
    merged_solvable_display: &'pool M,
}

impl<'pool, VS: VersionSet, N: PackageName + Display, M: SolvableDisplay<VS, N>>
    DisplayUnsat<'pool, VS, N, M>
{
    pub(crate) fn new(
        graph: ProblemGraph,
        pool: Rc<Pool<VS, N>>,
        merged_solvable_display: &'pool M,
    ) -> Self {
        let merged_candidates = graph.simplify(&pool);
        let installable_set = graph.get_installable_set();
        let missing_set = graph.get_missing_set();

        Self {
            graph,
            merged_candidates,
            installable_set,
            missing_set,
            pool,
            merged_solvable_display,
        }
    }

    fn fmt_graph(
        &self,
        f: &mut Formatter<'_>,
        top_level_edges: &[EdgeReference<'_, ProblemEdge>],
        top_level_indent: bool,
    ) -> fmt::Result
    where
        N: Display,
    {
        pub enum DisplayOp {
            Requirement(VersionSetId, Vec<EdgeIndex>),
            Candidate(NodeIndex),
        }

        let graph = &self.graph.graph;
        let installable_nodes = &self.installable_set;
        let mut reported: HashSet<SolvableId> = HashSet::new();

        // Note: we are only interested in requires edges here
        let indenter = Indenter::new(top_level_indent);
        let mut stack = top_level_edges
            .iter()
            .filter(|e| e.weight().try_requires().is_some())
            .chunk_by(|e| e.weight().requires())
            .into_iter()
            .map(|(version_set_id, group)| {
                let edges: Vec<_> = group.map(|e| e.id()).collect();
                (version_set_id, edges)
            })
            .sorted_by_key(|(_version_set_id, edges)| {
                edges
                    .iter()
                    .any(|&edge| installable_nodes.contains(&graph.edge_endpoints(edge).unwrap().1))
            })
            .map(|(version_set_id, edges)| {
                (
                    DisplayOp::Requirement(version_set_id, edges),
                    indenter.push_level(),
                )
            })
            .collect::<Vec<_>>();

        if !stack.is_empty() {
            // Mark the first element of the stack as not having any remaining siblings
            stack[0].1.set_last();
        }

        while let Some((node, indenter)) = stack.pop() {
            let top_level = indenter.is_at_top_level();
            let indent = indenter.get_indent();

            match node {
                DisplayOp::Requirement(version_set_id, edges) => {
                    debug_assert!(!edges.is_empty());

                    let installable = edges.iter().any(|&e| {
                        let (_, target) = graph.edge_endpoints(e).unwrap();
                        installable_nodes.contains(&target)
                    });

                    let req = self.pool.resolve_version_set(version_set_id).to_string();
                    let name = self.pool.resolve_version_set_package_name(version_set_id);
                    let name = self.pool.resolve_package_name(name);
                    let target_nx = graph.edge_endpoints(edges[0]).unwrap().1;
                    let missing =
                        edges.len() == 1 && graph[target_nx] == ProblemNode::UnresolvedDependency;
                    if missing {
                        // No candidates for requirement
                        if top_level {
                            writeln!(f, "{indent}No candidates were found for {name} {req}.")?;
                        } else {
                            writeln!(
                                f,
                                "{indent}{name} {req}, for which no candidates were found.",
                            )?;
                        }
                    } else if installable {
                        // Package can be installed (only mentioned for top-level requirements)
                        if top_level {
                            writeln!(
                                f,
                                "{indent}{name} {req} can be installed with any of the following options:"
                            )?;
                        } else {
                            writeln!(f, "{indent}{name} {req}, which can be installed with any of the following options:")?;
                        }

                        let children: Vec<_> = edges
                            .iter()
                            .filter(|&&e| {
                                installable_nodes.contains(&graph.edge_endpoints(e).unwrap().1)
                            })
                            .map(|&e| {
                                (
                                    DisplayOp::Candidate(graph.edge_endpoints(e).unwrap().1),
                                    indenter.push_level(),
                                )
                            })
                            .collect();

                        // TODO: this is an utterly ugly hack that should be burnt to ashes
                        let mut deduplicated_children = Vec::new();
                        let mut merged_and_seen = HashSet::new();
                        for child in children {
                            let (DisplayOp::Candidate(child_node), _) = child else {
                                unreachable!()
                            };
                            let solvable_id = graph[child_node].solvable_id();
                            let merged = self.merged_candidates.get(&solvable_id);

                            // Skip merged stuff that we have already seen
                            if merged_and_seen.contains(&solvable_id) {
                                continue;
                            }

                            if let Some(merged) = merged {
                                merged_and_seen.extend(merged.ids.iter().copied())
                            }

                            deduplicated_children.push(child);
                        }

                        if !deduplicated_children.is_empty() {
                            deduplicated_children[0].1.set_last();
                        }

                        stack.extend(deduplicated_children);
                    } else {
                        // Package cannot be installed (the conflicting requirement is further down the tree)
                        if top_level {
                            writeln!(f, "{indent}{name} {req} cannot be installed because there are no viable options:")?;
                        } else {
                            writeln!(f, "{indent}{name} {req}, which cannot be installed because there are no viable options:")?;
                        }

                        let children: Vec<_> = edges
                            .iter()
                            .map(|&e| {
                                (
                                    DisplayOp::Candidate(graph.edge_endpoints(e).unwrap().1),
                                    indenter.push_level(),
                                )
                            })
                            .collect();

                        // TODO: this is an utterly ugly hack that should be burnt to ashes
                        let mut deduplicated_children = Vec::new();
                        let mut merged_and_seen = HashSet::new();
                        for child in children {
                            let (DisplayOp::Candidate(child_node), _) = child else {
                                unreachable!()
                            };
                            let solvable_id = graph[child_node].solvable_id();
                            let merged = self.merged_candidates.get(&solvable_id);

                            // Skip merged stuff that we have already seen
                            if merged_and_seen.contains(&solvable_id) {
                                continue;
                            }

                            if let Some(merged) = merged {
                                merged_and_seen.extend(merged.ids.iter().copied())
                            }

                            deduplicated_children.push(child);
                        }

                        if !deduplicated_children.is_empty() {
                            deduplicated_children[0].1.set_last();
                        }

                        stack.extend(deduplicated_children);
                    }
                }
                DisplayOp::Candidate(candidate) => {
                    let solvable_id = graph[candidate].solvable_id();

                    if reported.contains(&solvable_id) {
                        continue;
                    }

                    let solvable = self.pool.resolve_solvable(solvable_id);
                    let name = self.pool.resolve_package_name(solvable.name);
                    let version = if let Some(merged) = self.merged_candidates.get(&solvable_id) {
                        reported.extend(merged.ids.iter().cloned());
                        self.merged_solvable_display
                            .display_candidates(&self.pool, &merged.ids)
                    } else {
                        self.merged_solvable_display
                            .display_candidates(&self.pool, &[solvable_id])
                    };

                    let excluded = graph
                        .edges_directed(candidate, Direction::Outgoing)
                        .find_map(|e| match e.weight() {
                            ProblemEdge::Conflict(ConflictCause::Excluded) => {
                                let ProblemNode::Excluded(reason) = graph[e.target()] else {
                                    unreachable!();
                                };
                                Some(reason)
                            }
                            _ => None,
                        });
                    let already_installed = graph.edges(candidate).any(|e| {
                        e.weight() == &ProblemEdge::Conflict(ConflictCause::ForbidMultipleInstances)
                    });
                    let constrains_conflict = graph.edges(candidate).any(|e| {
                        matches!(
                            e.weight(),
                            ProblemEdge::Conflict(ConflictCause::Constrains(_))
                        )
                    });
                    let is_leaf = graph.edges(candidate).next().is_none();

                    if let Some(excluded_reason) = excluded {
                        writeln!(
                            f,
                            "{indent}{name} {version} is excluded because {reason}",
                            reason = self.pool.resolve_string(excluded_reason)
                        )?;
                    } else if is_leaf {
                        writeln!(f, "{indent}{name} {version}")?;
                    } else if already_installed {
                        writeln!(f, "{indent}{name} {version}, which conflicts with the versions reported above.")?;
                    } else if constrains_conflict {
                        let mut version_sets = graph
                            .edges(candidate)
                            .flat_map(|e| match e.weight() {
                                ProblemEdge::Conflict(ConflictCause::Constrains(
                                    version_set_id,
                                )) => Some(version_set_id),
                                _ => None,
                            })
                            .dedup()
                            .peekable();

                        writeln!(f, "{indent}{name} {version} would constrain",)?;

                        let mut indenter = indenter.push_level();
                        while let Some(&version_set_id) = version_sets.next() {
                            let version_set = self.pool.resolve_version_set(version_set_id);
                            let name = self.pool.resolve_version_set_package_name(version_set_id);
                            let name = self.pool.resolve_package_name(name);

                            if version_sets.peek().is_none() {
                                indenter.set_last();
                            }
                            let indent = indenter.get_indent();
                            writeln!(
                                f,
                                "{indent}{name} {version_set} , which conflicts with any installable versions previously reported",
                            )?;
                        }
                    } else {
                        writeln!(f, "{indent}{name} {version} would require",)?;
                        let mut requirements = graph
                            .edges(candidate)
                            .chunk_by(|e| e.weight().requires())
                            .into_iter()
                            .map(|(version_set_id, group)| {
                                let edges: Vec<_> = group.map(|e| e.id()).collect();
                                (version_set_id, edges)
                            })
                            .sorted_by_key(|(_version_set_id, edges)| {
                                edges.iter().any(|&edge| {
                                    installable_nodes
                                        .contains(&graph.edge_endpoints(edge).unwrap().1)
                                })
                            })
                            .map(|(version_set_id, edges)| {
                                (
                                    DisplayOp::Requirement(version_set_id, edges),
                                    indenter.push_level(),
                                )
                            })
                            .collect::<Vec<_>>();

                        if !requirements.is_empty() {
                            requirements[0].1.set_last();
                        }

                        stack.extend(requirements);
                    }
                }
            }
        }

        Ok(())
    }
}

impl<VS: VersionSet, N: PackageName + Display, M: SolvableDisplay<VS, N>> fmt::Display
    for DisplayUnsat<'_, VS, N, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (top_level_missing, top_level_conflicts): (Vec<_>, _) = self
            .graph
            .graph
            .edges(self.graph.root_node)
            .partition(|e| self.missing_set.contains(&e.target()));

        if !top_level_missing.is_empty() {
            self.fmt_graph(f, &top_level_missing, false)?;
        }

        if !top_level_conflicts.is_empty() {
            writeln!(f, "The following packages are incompatible")?;
            self.fmt_graph(f, &top_level_conflicts, true)?;

            // Conflicts caused by locked dependencies
            let mut edges = self.graph.graph.edges(self.graph.root_node).peekable();
            let indenter = Indenter::new(true);
            while let Some(e) = edges.next() {
                let indenter = indenter.push_level_with_order(match edges.peek() {
                    Some(_) => ChildOrder::HasRemainingSiblings,
                    None => ChildOrder::Last,
                });
                let indent = indenter.get_indent();

                let conflict = match e.weight() {
                    ProblemEdge::Requires(_) => continue,
                    ProblemEdge::Conflict(conflict) => conflict,
                };

                // The only possible conflict at the root level is a Locked conflict
                match conflict {
                    ConflictCause::Constrains(_) | ConflictCause::ForbidMultipleInstances => {
                        unreachable!()
                    }
                    &ConflictCause::Locked(solvable_id) => {
                        let locked = self.pool.resolve_solvable(solvable_id);
                        writeln!(
                            f,
                            "{indent}{} {} is locked, but another version is required as reported above",
                            locked.name.display(&self.pool),
                            self.merged_solvable_display
                                .display_candidates(&self.pool, &[solvable_id])
                        )?;
                    }
                    ConflictCause::Excluded => continue,
                };
            }
        }

        Ok(())
    }
}

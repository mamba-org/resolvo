use std::io::Write;

use ahash::HashMap;
use itertools::Itertools;

use crate::{
    DependencyProvider, Solver,
    runtime::AsyncRuntime,
    solver::clause::{Clause, WatchedLiterals},
};

impl<D: DependencyProvider, RT: AsyncRuntime> Solver<D, RT> {
    /// Reports diagnostics about the current state of the solver.
    pub(crate) fn report_diagnostics(&self) {
        let mut forbid_clauses_by_name = HashMap::default();
        let mut forbid_clauses = 0usize;
        let mut requires_clauses = 0usize;
        let mut locked_clauses = 0usize;
        let mut learned_clauses = 0usize;
        let mut constrains_clauses = 0usize;
        let clauses = &self.state.clauses.kinds;
        for clause in clauses.iter() {
            match clause {
                Clause::ForbidMultipleInstances(_a, _b, name_id) => {
                    let count = forbid_clauses_by_name.entry(name_id).or_insert(0usize);
                    *count += 1;
                    forbid_clauses += 1;
                }
                Clause::Requires(..) => {
                    requires_clauses += 1;
                }
                Clause::Lock(..) => {
                    locked_clauses += 1;
                }
                Clause::Learnt(..) => {
                    learned_clauses += 1;
                }
                Clause::Constrains(..) => {
                    constrains_clauses += 1;
                }
                _ => {}
            }
        }

        let mut writer = tabwriter::TabWriter::new(Vec::new());
        writeln!(
            writer,
            "Total number of solvables:\t{}",
            self.state.decision_tracker.len()
        )
        .unwrap();
        writeln!(
            writer,
            "Total number of watches:\t{} ({})",
            self.state.watches.len(),
            human_bytes::human_bytes(self.state.watches.size_in_bytes() as f64)
        )
        .unwrap();
        writeln!(
            writer,
            "Total number of clauses:\t{} ({})",
            clauses.len(),
            human_bytes::human_bytes(
                (clauses.len()
                    * (std::mem::size_of::<Clause>() + std::mem::size_of::<WatchedLiterals>()))
                    as f64
            )
        )
        .unwrap();
        writeln!(writer, "- Requires:\t{}", requires_clauses).unwrap();
        writeln!(writer, "- Constrains:\t{}", constrains_clauses).unwrap();
        writeln!(writer, "- Lock:\t{}", locked_clauses).unwrap();
        writeln!(writer, "- Learned:\t{}", learned_clauses).unwrap();
        writeln!(writer, "- ForbidMultiple:\t{}", forbid_clauses).unwrap();

        for (name_id, count) in forbid_clauses_by_name
            .iter()
            .sorted_by_key(|(_, count)| **count)
            .rev()
            .take(5)
        {
            writeln!(
                writer,
                "  - {}:\t{}",
                self.provider().display_name(**name_id),
                count
            )
            .unwrap();
        }

        if forbid_clauses_by_name.len() > 5 {
            writeln!(writer, "  ...").unwrap();
        }

        let report = String::from_utf8(writer.into_inner().unwrap()).unwrap();

        tracing::info!("Solver diagnostics:\n{}", report);
    }
}

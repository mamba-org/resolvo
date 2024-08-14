use std::{
    fs::File,
    io::BufReader,
    ops::Add,
    time::{Duration, Instant, SystemTime},
};

use clap::Parser;
use csv::WriterBuilder;
use resolvo::{snapshot::DependencySnapshot, Solver, UnsolvableOrCancelled};

#[derive(Parser)]
#[clap(version = "0.1.0", author = "Bas Zalmstra <zalmstra.bas@gmail.com>")]
struct Opts {
    snapshot: String,
}

#[derive(Debug, serde::Serialize)]
struct Record {
    package: String,
    duration: f64,
    error: Option<String>,
    records: Option<usize>,
}

fn main() {
    let opts: Opts = Opts::parse();

    eprintln!("Loading snapshot ...");
    let snapshot_file = BufReader::new(File::open(&opts.snapshot).unwrap());
    let snapshot: DependencySnapshot = serde_json::from_reader(snapshot_file).unwrap();

    let mut writer = WriterBuilder::new()
        .has_headers(true)
        .from_path("timings.csv")
        .unwrap();

    for (i, (package_name_id, package)) in snapshot.packages.iter().enumerate() {
        eprint!(
            "solving {} ({i}/{}) ... ",
            &package.name,
            snapshot.packages.len()
        );
        let start = Instant::now();

        let mut provider = snapshot
            .provider()
            .with_timeout(SystemTime::now().add(Duration::from_secs(60)));
        let package_requirement = provider.add_package_requirement(package_name_id);
        let mut solver = Solver::new(provider);
        let mut records = None;
        let mut error = None;
        match solver.solve(vec![package_requirement.into()], vec![]) {
            Ok(solution) => {
                eprintln!("OK");
                records = Some(solution.len())
            }
            Err(UnsolvableOrCancelled::Unsolvable(problem)) => {
                eprintln!("FAIL");
                error = Some(problem.display_user_friendly(&solver).to_string());
            }
            Err(_) => {
                eprintln!("CANCELLED");
            }
        }

        let duration = start.elapsed();

        writer
            .serialize(Record {
                package: package.name.clone(),
                duration: duration.as_secs_f64(),
                error,
                records,
            })
            .unwrap();

        if i % 100 == 0 {
            writer.flush().unwrap();
        }
    }

    writer.flush().unwrap();
}

use std::{fs::File, path::PathBuf};

use clap::Parser;
use forcrat::{compile_util::Pass, *};

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,

    input: PathBuf,
}

fn main() {
    let args = Args::parse();

    if let Some(log) = args.log_file {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .without_time()
            .with_ansi(false)
            .with_level(false)
            .with_writer(log_file)
            .init();
    }

    let file = args.input.join("c2rust-lib.rs");
    let res = steensgaard::Steensgaard.run_on_path(&file);
    // println!("{:?}", res.vars);
    // println!("{:?}", res.var_tys);
    // println!("{:?}", res.fns);
    // println!("{:?}", res.fn_tys);
    // extern_finder::ExternFinder.run_on_path(&file);
    file_analysis::FileAnalysis { steensgaard: res }.run_on_path(&file);
}

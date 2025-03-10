use std::{fs::File, path::PathBuf};

use clap::Parser;
use forcrat::{api_list::API_LIST, compile_util::Pass, *};

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
    // extern_finder::ExternFinder.run_on_path(&file);
    let (counts, std_arg_counts) = api_counter::ApiCounter.run_on_path(&file);
    for (name, api_kind) in API_LIST {
        let v = counts.get(name).copied().unwrap_or(0);
        print!("{} ", v);
        if api_kind.is_read() || api_kind.is_write() {
            let v = std_arg_counts.get(name).copied().unwrap_or(0);
            print!("{} ", v);
        }
    }
    println!();

    // let res = steensgaard::Steensgaard.run_on_path(&file);
    // println!("{:?}", res.vars);
    // println!("{:?}", res.var_tys);
    // println!("{:?}", res.fns);
    // println!("{:?}", res.fn_tys);
    // file_analysis::FileAnalysis { steensgaard: res }.run_on_path(&file);
}

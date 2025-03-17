use std::{fs::File, path::PathBuf};

use clap::{Parser, Subcommand};
use forcrat::{api_list::API_LIST, compile_util::Pass, *};

#[derive(Subcommand, Debug)]
enum Command {
    CountApis,
    CountReturnValues,
    Analyze,
}

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long)]
    log_file: Option<PathBuf>,

    input: PathBuf,

    #[command(subcommand)]
    command: Command,
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

    match args.command {
        Command::CountApis => {
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
        }
        Command::CountReturnValues => {
            let counts = retval_use_counter::RetValCounter.run_on_path(&file);
            for (name, counts) in counts {
                println!("{} {} {}", name, counts.used, counts.unused);
            }
        }
        Command::Analyze => {
            let res = steensgaard::Steensgaard.run_on_path(&file);
            println!("{:?}", res.vars);
            println!("{:?}", res.var_tys);
            println!("{:?}", res.fns);
            println!("{:?}", res.fn_tys);
            file_analysis::FileAnalysis { steensgaard: res }.run_on_path(&file);
        }
    }
}

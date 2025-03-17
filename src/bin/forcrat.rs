use std::{
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand};
use forcrat::{api_list::API_LIST, compile_util::Pass, *};

#[derive(Subcommand, Debug)]
enum Command {
    CountApis,
    CountReturnValues,
    Analyze,
    Transformation {
        #[arg(short, long)]
        output: PathBuf,
    },
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
        Command::Transformation { mut output } => {
            output.push(args.input.file_name().unwrap());
            if output.exists() {
                assert!(output.is_dir());
                clear_dir(&output);
            } else {
                fs::create_dir(&output).unwrap();
            }
            copy_dir(&args.input, &output, true);
            let file = output.join("c2rust-lib.rs");

            let res = steensgaard::Steensgaard.run_on_path(&file);
            let res = file_analysis::FileAnalysis { steensgaard: res }.run_on_path(&file);
            transformation::Transformation {
                analysis_result: res,
            }
            .run_on_path(&file);
        }
    }
}

fn clear_dir(path: &Path) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            let name = entry_path.file_name().unwrap();
            if name != "target" {
                fs::remove_dir_all(entry_path).unwrap();
            }
        } else {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn copy_dir(src: &Path, dst: &Path, root: bool) {
    for entry in fs::read_dir(src).unwrap() {
        let src_path = entry.unwrap().path();
        let name = src_path.file_name().unwrap();
        let dst_path = dst.join(name);
        if src_path.is_file() {
            fs::copy(src_path, dst_path).unwrap();
        } else if src_path.is_dir() && (!root || name != "target") {
            fs::create_dir(&dst_path).unwrap();
            copy_dir(&src_path, &dst_path, false);
        }
    }
}

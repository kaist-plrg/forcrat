#![feature(rustc_private)]

use std::{
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand};
use forcrat::{api_list::API_LIST, compile_util::Pass, *};

#[derive(Subcommand, Debug)]
enum Command {
    CountApis {
        #[arg(long, default_value = "false")]
        distinguish_std_args: bool,
        #[arg(long, default_value = "false")]
        show_api_names: bool,
        #[arg(long, default_value = "false")]
        show_unsupported: bool,
        #[arg(long, default_value = "false")]
        only_show_total: bool,
    },
    CountReturnValues,
    FindFileReturns,
    FindFileTypes {
        #[arg(long, default_value = "false")]
        mir: bool,
    },
    Steensgaard,
    Format,
    Preprocess {
        #[arg(short, long)]
        output: PathBuf,
    },
    AnalyzeError,
    AnalyzeFile,
    Transform {
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
        Command::CountApis {
            distinguish_std_args,
            show_api_names,
            show_unsupported,
            only_show_total,
        } => {
            if show_api_names {
                print!("total ");
                for (name, api_kind) in API_LIST {
                    if !api_kind.is_posix_io() {
                        continue;
                    }
                    print!("{} ", name);
                    if distinguish_std_args && (api_kind.is_read() || api_kind.is_write()) {
                        print!("{}_std ", name);
                    }
                }
                println!();
            }
            let (counts, std_arg_counts) = api_counter::ApiCounter.run_on_path(&file);
            let sum = counts
                .values()
                .chain(std_arg_counts.values())
                .sum::<usize>();
            print!("{} ", sum);
            if only_show_total {
                println!();
                return;
            }
            for (name, api_kind) in API_LIST {
                if !api_kind.is_posix_io() {
                    continue;
                }
                if distinguish_std_args {
                    let v = counts.get(name).copied().unwrap_or(0);
                    print!("{} ", v);
                    if api_kind.is_read() || api_kind.is_write() {
                        let v = std_arg_counts.get(name).copied().unwrap_or(0);
                        print!("{} ", v);
                    }
                } else {
                    let v1 = counts.get(name).copied().unwrap_or(0);
                    let v2 = std_arg_counts.get(name).copied().unwrap_or(0);
                    print!("{} ", v1 + v2);
                }
            }
            println!();
            if show_unsupported {
                for (name, api_kind) in API_LIST {
                    if !api_kind.is_unsupported() {
                        continue;
                    }
                    let v1 = counts.get(name).copied().unwrap_or(0);
                    let v2 = std_arg_counts.get(name).copied().unwrap_or(0);
                    let v = v1 + v2;
                    if v > 0 {
                        print!("{}: {}, ", name, v);
                    }
                }
                println!();
            }
        }
        Command::CountReturnValues => {
            let counts = retval_use_counter::RetValCounter.run_on_path(&file);
            for (name, counts) in counts {
                println!("{} {} {}", name, counts.used, counts.unused);
            }
        }
        Command::FindFileReturns => {
            return_finder::ReturnFinder.run_on_path(&file);
        }
        Command::FindFileTypes { mir } => {
            ty_finder::TyFinder { mir }.run_on_path(&file);
        }
        Command::Steensgaard => {
            let res = steensgaard::Steensgaard.run_on_path(&file);
            println!("{:?}", res.vars);
            println!("{:?}", res.var_tys);
            println!("{:?}", res.fns);
            println!("{:?}", res.fn_tys);
        }
        Command::AnalyzeFile => {
            file_analysis::FileAnalysis { verbose: true }.run_on_path(&file);
        }
        Command::AnalyzeError => {
            error_analysis::ErrorAnalysis.run_on_path(&file);
        }
        Command::Transform { mut output } => {
            output.push(args.input.file_name().unwrap());
            if output.exists() {
                assert!(output.is_dir());
                clear_dir(&output);
            } else {
                fs::create_dir(&output).unwrap();
            }
            copy_dir(&args.input, &output, true);
            let file = output.join("c2rust-lib.rs");

            let result = transformation::Transformation.run_on_path(&file);
            transformation::write_to_files(&result, &output);
        }
        Command::Preprocess { mut output } => {
            output.push(args.input.file_name().unwrap());
            if output.exists() {
                assert!(output.is_dir());
                clear_dir(&output);
            } else {
                fs::create_dir(&output).unwrap();
            }
            copy_dir(&args.input, &output, true);
            let file = output.join("c2rust-lib.rs");

            let result = preprocessor::Preprocessor.run_on_path(&file);
            preprocessor::write_to_files(&result);
        }
        Command::Format => {
            format::Format.run_on_path(&file);
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

#![feature(rustc_private)]

use std::{
    fmt::Write as _,
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, Subcommand};
use forcrat::{api_list::API_LIST, compile_util::Pass, *};

#[derive(Subcommand, Debug)]
enum Command {
    CountApis {
        #[arg(long)]
        filter: Vec<String>,
        #[arg(long, default_value = "false")]
        show_detail: bool,
        #[arg(long, default_value = "false")]
        show_wide: bool,
        #[arg(long, default_value = "false")]
        show_callers: bool,
        #[arg(long, default_value = "false")]
        show_non_posix_high_level_io: bool,
        #[arg(long, default_value = "false")]
        show_api_names: bool,
        #[arg(long, default_value = "false")]
        distinguish_std_args: bool,
    },
    CountReturnValues,
    CountUnsafe,
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
        #[arg(long, default_value = "false")]
        show_stats: bool,
        #[arg(long, default_value = "false")]
        show_unsupported_reasons: bool,
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
            filter,
            show_detail,
            show_wide,
            show_callers,
            show_non_posix_high_level_io,
            show_api_names,
            distinguish_std_args,
        } => {
            if show_api_names && !show_callers {
                print!("total ");
                if show_detail {
                    for (name, api_info) in API_LIST {
                        let api_kind = api_info.kind;
                        if !api_info.is_byte && !show_wide {
                            continue;
                        }
                        if !api_kind.is_posix_high_level_io() && !show_non_posix_high_level_io {
                            continue;
                        }
                        if !filter.is_empty() && !filter.iter().any(|f| f == name) {
                            continue;
                        }
                        print!("{name} ");
                        if distinguish_std_args && api_kind.is_operation() {
                            print!("{name}_std ");
                        }
                    }
                }
                println!();
            }
            let res = api_counter::ApiCounter.run_on_path(&file);
            let mut sum = 0;
            let mut s = String::new();
            for (name, api_info) in API_LIST {
                let api_kind = api_info.kind;
                if !api_info.is_byte && !show_wide {
                    continue;
                }
                if !api_kind.is_posix_high_level_io() && !show_non_posix_high_level_io {
                    continue;
                }
                if !filter.is_empty() && !filter.iter().any(|f| f == name) {
                    continue;
                }
                if show_callers {
                    println!("{name}");
                }
                if distinguish_std_args {
                    if show_callers {
                        if let Some(v) = res.counts.get(name) {
                            for f in v {
                                println!("{f}");
                            }
                        }
                    } else {
                        let v = res.counts.get(name).map(|v| v.len()).unwrap_or(0);
                        sum += v;
                        if show_detail {
                            write!(s, "{v} ").unwrap();
                        }
                    }
                    if api_kind.is_operation() {
                        if show_callers {
                            if let Some(v) = res.std_arg_counts.get(name) {
                                for f in v {
                                    println!("{f}");
                                }
                            }
                        } else {
                            let v = res.std_arg_counts.get(name).map(|v| v.len()).unwrap_or(0);
                            sum += v;
                            if show_detail {
                                write!(s, "{v} ").unwrap();
                            }
                        }
                    }
                } else if show_callers {
                    if let Some(v) = res.counts.get(name) {
                        for f in v {
                            println!("{f}");
                        }
                    }
                    if let Some(v) = res.std_arg_counts.get(name) {
                        for f in v {
                            println!("{f}");
                        }
                    }
                } else {
                    let v1 = res.counts.get(name).map(|v| v.len()).unwrap_or(0);
                    let v2 = res.std_arg_counts.get(name).map(|v| v.len()).unwrap_or(0);
                    let v = v1 + v2;
                    sum += v;
                    if show_detail {
                        write!(s, "{v} ").unwrap();
                    }
                }
            }
            if !show_callers {
                println!("{sum} {s}");
            }
        }
        Command::CountReturnValues => {
            let counts = retval_use_counter::RetValCounter.run_on_path(&file);
            for (name, counts) in counts {
                println!("{} {} {}", name, counts.used, counts.unused);
            }
        }
        Command::CountUnsafe => {
            check_unsafety::UnsafetyChecker.run_on_path(&file);
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
            file_analysis::FileAnalysis.run_on_path(&file);
        }
        Command::AnalyzeError => {
            error_analysis::ErrorAnalysis.run_on_path(&file);
        }
        Command::Transform {
            mut output,
            show_stats,
            show_unsupported_reasons,
        } => {
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
            let start = std::time::Instant::now();
            transformation::write_to_files(&result, &output);
            let time = start.elapsed().as_millis();
            if show_stats {
                let visit_nums = result.analysis_stat.error_visit_nums;
                println!(
                    "{} {} {} {} {} {} {} {} {}",
                    result.analysis_stat.file_analysis_time,
                    result.analysis_stat.solving_time,
                    result.analysis_stat.error_analysis_time,
                    result.transformation_time + time,
                    visit_nums.len(),
                    visit_nums.iter().sum::<usize>(),
                    result.analysis_stat.loc_num,
                    result.analysis_stat.unsupported_num,
                    result.bound_num,
                );
            }
            if show_unsupported_reasons {
                for reasons in result.unsupported_reasons {
                    for reason in reasons.iter() {
                        print!("{reason:?},");
                    }
                    println!();
                }
            }
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

use clap::Parser;
use std::{path::Path, process, str};

mod compiler;
use compiler::compile;

#[derive(Parser, Debug)]
#[command(version("0.1.0"), about = "A C compiler", long_about = None)]
struct Args {
    #[arg(help = "Path to the file to compile")]
    file_path: String,
    #[clap(
        long,
        short,
        action,
        help = "Directs compiler to run to lexer, but stop before parsing"
    )]
    lex: bool,
    #[clap(
        long,
        short,
        action,
        help = "Directs compiler to run lexer and parser, but stop before assembly generation"
    )]
    parse: bool,
    #[clap(
        long,
        short,
        action,
        help = "Directs compiler to perform lexing, parsing, and assembly generation, but stop before code emission"
    )]
    codegen: bool,
}

fn main() {
    let args = Args::parse();

    // driver
    let preprocessed_file = format!("{}.i", args.file_path);
    preprocess(&args.file_path, &preprocessed_file);
    let assembly_file = compile(preprocessed_file, args.lex, args.parse, args.codegen).unwrap();
    println!("(!!!) assembly_file = {}", assembly_file);
    assemble(&assembly_file);
}

/// preprocesses the C file
/// kind of cheating, but we're only writing a compiler, not a preprocessor,
/// at least for now.
fn preprocess(input_file: &String, preprocessed_file: &String) {
    let output = if cfg!(target_os = "windows") {
        todo!("This compiler currently targets x64 Linux. Make a PR or an issue if you want a different target.")
    } else {
        process::Command::new("gcc")
            .args(["-E", "-P"]) // gcc only runs preprocessor
            .arg(input_file)
            .arg("-o")
            .arg(preprocessed_file)
            .output()
            .expect("failed to execute preprocesser")
    };

    println!(
        "(-) Preprocessing complete\n\n(-) stdout:\n{}\n\n(-) stderr:\n{}",
        str::from_utf8(&output.stdout).expect("Invalid UTF-8 sequence"),
        str::from_utf8(&output.stderr).expect("Invalid UTF-8 sequence")
    )
}

/// Assemble the C file
/// kind of cheating, but we're only writing a compiler, not a preprocessor,
/// at least for now.
fn assemble(input_file: &String) {
    let output_file = Path::new(input_file)
        .file_stem()
        .expect("Invalid path")
        .to_str()
        .expect("Invalid UTF-8 sequence");
    let output = if cfg!(target_os = "windows") {
        todo!("This compiler currently targets x64 Linux. Make a PR or an issue if you want a different target.")
    } else {
        process::Command::new("gcc") // this isn't what it looks like!!
            .args([input_file, "-o", output_file])
            .output()
            .expect("failed to execute preprocesser")
    };

    println!(
        "(-) Preprocessing complete\n\n(-) stdout:\n{}\n\n(-) stderr:\n{}",
        str::from_utf8(&output.stdout).expect("Invalid UTF-8 sequence"),
        str::from_utf8(&output.stderr).expect("Invalid UTF-8 sequence")
    )
}

use clap::Parser;
use std::{path::Path, process, str};

mod compiler;
use compiler::compile;

#[cfg(test)]
mod test;

#[derive(Parser, Debug)]
#[command(version("0.1.1"), about = "A C compiler for x86-64 Linux", long_about = None)]
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
    #[clap(
        long,
        short,
        action,
        help = "Directs compiler to perform lexing, parsing, and tacky, but stop before code emission"
    )]
    tacky: bool,
    #[clap(
        long,
        short,
        action,
        help = "Directs for binary to be placed adjacent in current directory"
    )]
    incd: bool,
}

fn main() {
    let args = Args::parse();
    let incd = args.incd; // will be moving

    // driver
    let stripped_extension = if args.file_path.ends_with(r".c") {
        String::from(args.file_path.strip_suffix(r".c").unwrap())
    } else {
        println!("(!) {} is not a c file", args.file_path);
        return;
    };
    let preprocessed_file = format!("{}.i", stripped_extension);
    preprocess(&args.file_path, &preprocessed_file);
    let assembly_file = match compile(stripped_extension, args) {
        Ok(strang) => strang,
        Err(e) => {
            println!("{}", e);
            return;
        }
    };
    assemble(&assembly_file, incd);
}

/// preprocesses the C file
/// kind of cheating, but we're only writing a compiler, not a preprocessor,
/// at least for now.
pub fn preprocess(input_file: &String, preprocessed_file: &String) {
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

    let out = str::from_utf8(&output.stdout).expect("Invalid UTF-8 sequence");
    let err = str::from_utf8(&output.stderr).expect("Invalid UTF-8 sequence");

    if !out.is_empty() {
        println!("PREPROCESS STDOUT: {}", out);
    }
    if !err.is_empty() {
        println!("PREPROCESS STDERR: {}", err);
    }
}

/// Assemble the C file
/// kind of cheating, but we're only writing a compiler, not a preprocessor,
/// at least for now.
pub fn assemble(input_file: &String, incd: bool) {
    let output_file = if incd {
        Path::new(input_file)
            .file_stem()
            .expect("Invalid path")
            .to_str()
            .expect("Invalid UTF-8 sequence")
    } else {
        Path::new(input_file)
            .to_str()
            .expect("Invalid path")
            .strip_suffix(r".s")
            .unwrap()
    };
    let output = if cfg!(target_os = "windows") {
        todo!("This compiler currently targets x64 Linux. Make a PR or an issue if you want a different target.")
    } else {
        process::Command::new("gcc") // this isn't what it looks like!!
            .args([input_file, "-o", output_file])
            .output()
            .expect("failed to execute preprocesser")
    };

    let out = str::from_utf8(&output.stdout).expect("Invalid UTF-8 sequence");
    let err = str::from_utf8(&output.stderr).expect("Invalid UTF-8 sequence");

    if !out.is_empty() {
        println!("ASSEMBLE STDOUT: {}", out);
    }
    if !err.is_empty() {
        println!("ASSEMBLE STDERR: {}", err);
    }
}

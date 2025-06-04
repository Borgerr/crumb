# crumb

A C compiler targetting x86_64-unknown-linux-gnu.

## Building

Currently, the compiler should be built natively with `cargo`,
using `cargo run` or
`cargo build --release` and finding the binary in `build/release`.

## Usage

`crumb [OPTIONS] <FILE_PATH>`

Also, on invocation, you can see a list of options and flags to use with the CLI.

### Arguments

`<FILE_PATH>` Path to the file to compile.

### Options:

- `-l`, `--lex`, Directs compiler to run to lexer, but stop before parsing.
- `-p`, `--parse`, Directs compiler to run lexer and parser, but stop before assembly generation
- `-c`, `--codegen`, Directs compiler to perform lexing, parsing, and assembly generation, but stop before code emission
- `-t`, `--tacky`, Directs compiler to perform lexing, parsing, and tacky, but stop before code emission
- `-i`, `--incd`, Directs for binary to be placed adjacent in current directory
- `-h`, `--help`, Print help
- `-V`, `--version`, Print version


use atty::Stream;
use bril_rs::{load_program, load_program_from_read, Program};
use cfg::Cfg;
use clap::Parser;
use serde_json;
use std::fs::File;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct CLIArgs {
    /// The optional file to read from, if not specified a bril program
    /// is expected on stdin
    #[arg(short, long)]
    file: Option<String>,
}

fn main() {
    let args = CLIArgs::parse();
    if args.file.is_some() {
        let prog =
            load_program_from_read(File::open(args.file.unwrap()).unwrap());
        println!("{}", serde_json::to_string(&transform_prog(prog)).unwrap());
    } else if !atty::is(Stream::Stdin) {
        println!(
            "{}",
            serde_json::to_string(&transform_prog(load_program())).unwrap()
        );
    } else {
        eprintln!("Either specify a file or pipe in a bril program.");
        eprintln!("See `dummy-pass --help` for more information.");
    }
}

fn transform_prog(mut prog: Program) -> Program {
    for f in &mut prog.functions {
        let cfg = Cfg::from(f, false);
        let new_body = cfg.to_src();
        f.instrs = new_body;
    }
    prog
}

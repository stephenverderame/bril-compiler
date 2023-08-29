#![warn(clippy::pedantic, clippy::nursery)]
use atty::Stream;
use bril_rs::{load_program, load_program_from_read, Program};
use cfg::{Cfg, CfgEdgeTo, CFG_END_ID};
use clap::Parser;
use std::fs::File;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct CLIArgs {
    /// The optional file to read from, if not specified a bril program
    /// is expected on stdin
    #[arg(short, long)]
    file: Option<String>,

    /// Specify this flag to make a CFG node for each instruction instead of
    /// each basic block
    #[arg(long, default_value_t = false)]
    single: bool,
}

/// # bril2cfg
/// A tool to convert a bril program to a dot file
/// representing the control flow graph of each function
/// in the program.
/// ## Usage
/// `bril2cfg <bril json on stdin>`
/// OR specify a file
/// `bril2cfg -f <bril json file path>`
/// ## Example
/// `ts2bril test.ts | bril2cfg`
/// OR
/// `bril2cfg -f test.json`
fn main() {
    let args = CLIArgs::parse();
    if args.file.is_some() {
        let prog =
            load_program_from_read(File::open(args.file.unwrap()).unwrap());
        print_prog(prog, args.single);
    } else if !atty::is(Stream::Stdin) {
        print_prog(load_program(), args.single);
    } else {
        eprintln!("Either specify a file or pipe in a bril program.");
        eprintln!("See `bril2cfg --help` for more information.");
    }
}

/// Print the dot file for the given program.
fn print_prog(prog: Program, single: bool) {
    println!("digraph {{");
    for f in prog.functions {
        let cfg = Cfg::from(&f, single);
        let mut args_name = "(".to_owned();
        for (idx, a) in f.args.iter().enumerate() {
            args_name.push_str(&format!("{}: {}", a.name, a.arg_type));
            if idx != f.args.len() - 1 {
                args_name.push_str(", ");
            }
        }
        args_name.push(')');
        print_dot(&cfg, &f.name, &args_name);
    }
    println!("}}");
}

/// Write a dot file for the given CFG.
/// The end node is not printed
///
/// We print each function as a clustered subgraph
/// of a digraph
fn print_dot(cfg: &Cfg, name: &str, args: &str) {
    println!("\tsubgraph cluster_{name} {{");
    println!("\t\tlabel=\"{name}{args}\";");
    println!("\t\trankdir=\"TB\";");
    for (i, node) in &cfg.blocks {
        if *i != CFG_END_ID {
            println!(
                "\t\t{name}_{i} [label=\"{node}\", shape=\"rectangle\", style=\"rounded\"];"
            );
        }
    }
    println!();
    for i in cfg.blocks.keys() {
        let next = cfg.adj_lst.get(i).unwrap();
        match next {
            CfgEdgeTo::Branch {
                true_node,
                false_node,
            } => {
                if *true_node != CFG_END_ID {
                    println!(
                        "\t\t{name}_{i} -> {name}_{true_node} [label=\"T\"];"
                    );
                }
                if *false_node != CFG_END_ID {
                    println!(
                        "\t\t{name}_{i} -> {name}_{false_node} [label=\"F\"];"
                    );
                }
            }
            CfgEdgeTo::Next(next_node) => {
                if *next_node != CFG_END_ID {
                    println!("\t\t{name}_{i} -> {name}_{next_node};");
                }
            }
            CfgEdgeTo::Terminal => {}
        }
    }
    println!("\t}}");
}

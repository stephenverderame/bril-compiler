#![warn(clippy::pedantic, clippy::nursery)]
use bril_rs::{load_program, load_program_from_read, Program};
use cfg::{Cfg, CfgEdgeTo, CFG_END_ID};
use std::{env, fs::File};

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
    if env::args().len() >= 2 && env::args().nth(1).unwrap() == "--help" {
        eprintln!("Usage: bril2cfg <bril json on stdin>");
        eprintln!("Ex: `ts2bril test.ts | bril2cfg`");
        eprintln!("Usage: bril2cfg -f <bril json file path>");
        eprintln!("Ex: `bril2cfg -f test.json`");
    } else if env::args().len() >= 3 && env::args().nth(1).unwrap() == "-f" {
        let prog = load_program_from_read(
            File::open(env::args().nth(2).unwrap()).unwrap(),
        );
        print_prog(prog);
    } else {
        print_prog(load_program());
    }
}

/// Print the dot file for the given program.
fn print_prog(prog: Program) {
    println!("digraph {{");
    for f in prog.functions {
        let cfg = Cfg::from(&f);
        print_dot(&cfg, &f.name);
    }
    println!("}}");
}

/// Write a dot file for the given CFG.
/// The end node is not printed
///
/// We print each function as a clustered subgraph
/// of a digraph
fn print_dot(cfg: &Cfg, name: &str) {
    println!("\tsubgraph cluster_{name} {{");
    println!("\t\tlabel=\"{name}\";");
    println!("\t\trankdir=\"TB\";");
    for (i, node) in &cfg.blocks {
        if *i != CFG_END_ID {
            println!("\t\t{name}_{i} [label=\"{node}\", shape=\"ellipse\"];");
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

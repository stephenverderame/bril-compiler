#![warn(clippy::pedantic, clippy::nursery)]
use atty::Stream;
use bril_rs::{load_program, load_program_from_read, Program};
use cfg::analysis::dominators::compute_dominators;
use cfg::analysis::loops::{find_natural_loops, NaturalLoop};
use cfg::analysis::{Dir, Fact};
use cfg::{
    analysis::analyze, analysis::live_vars::LiveVars, analysis::Backwards, Cfg,
    CfgEdgeTo, CFG_END_ID,
};
use clap::Parser;
use std::collections::{BTreeSet, HashMap};
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

    /// The name of a dataflow analysis to run
    /// Options: "live_vars"
    #[arg(long)]
    df: Option<String>,

    /// Specify this flag to display a dom tree instead of a CFG
    #[arg(long, default_value_t = false)]
    dom: bool,

    /// Specify this flag to display loops in the CFG
    #[arg(long, default_value_t = false)]
    loops: bool,
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
        let prog = load_program_from_read(
            File::open(args.file.as_ref().unwrap()).unwrap(),
        );
        print_prog(prog, &args);
    } else if !atty::is(Stream::Stdin) {
        print_prog(load_program(), &args);
    } else {
        eprintln!("Either specify a file or pipe in a bril program.");
        eprintln!("See `bril2cfg --help` for more information.");
    }
}

/// Print the dot file for the given program.
fn print_prog(prog: Program, args: &CLIArgs) {
    println!("digraph {{");
    for f in prog.functions {
        let cfg = Cfg::from(&f, args.single);
        let mut args_name = "(".to_owned();
        for (idx, a) in f.args.iter().enumerate() {
            args_name.push_str(&format!("{}: {}", a.name, a.arg_type));
            if idx != f.args.len() - 1 {
                args_name.push_str(", ");
            }
        }
        args_name.push(')');
        print_dot(&cfg, &f.name, &args_name, args);
    }
    println!("}}");
}

/// Write a dot file for the given CFG.
/// The end node is not printed
///
/// We print each function as a clustered subgraph
/// of a digraph
fn print_dot(cfg: &Cfg, fn_name: &str, fn_args: &str, args: &CLIArgs) {
    let df_res_str = display_facts(&args.df, cfg);
    println!("\tsubgraph cluster_{fn_name} {{");
    println!("\t\tlabel=\"{fn_name}{fn_args}\";");
    println!("\t\trankdir=\"TB\";");
    let empty = (String::new(), String::new());
    for (i, node) in &cfg.blocks {
        if *i != CFG_END_ID {
            let (header, footer) = df_res_str.get(i).unwrap_or(&empty);
            println!(
                "\t\t{fn_name}_{i} [label=\"{header}{node}{footer}\", shape=\"rectangle\", style=\"rounded\"];"
            );
        }
    }
    display_clusters(cfg, args, fn_name);
    println!();
    if args.dom {
        display_dom(cfg, fn_name);
    } else {
        display_cfg(cfg, fn_name);
    }
    println!("\t}}");
}

/// Prints the edges of the CFG
fn display_cfg(cfg: &Cfg, fn_name: &str) {
    for i in cfg.blocks.keys() {
        let next = cfg.adj_lst.get(i).unwrap();
        match next {
            CfgEdgeTo::Branch {
                true_node,
                false_node,
            } => {
                if *true_node != CFG_END_ID {
                    println!(
                        "\t\t{fn_name}_{i} -> {fn_name}_{true_node} [label=\"T\"];"
                    );
                }
                if *false_node != CFG_END_ID {
                    println!(
                        "\t\t{fn_name}_{i} -> {fn_name}_{false_node} [label=\"F\"];"
                    );
                }
            }
            CfgEdgeTo::Next(next_node) => {
                if *next_node != CFG_END_ID {
                    println!("\t\t{fn_name}_{i} -> {fn_name}_{next_node};");
                }
            }
            CfgEdgeTo::Terminal => {}
        }
    }
}

/// Prints the given natural loop and all nested loops
/// # Arguments
/// * `lp` - The natural loop to print
/// * `nest_lvl` - The nesting level of the loop (0 for top level loops)
/// * `fn_name` - The name of the function the loop is in
fn display_loop(lp: &NaturalLoop, nest_lvl: usize, fn_name: &str) {
    let subgraph_indent =
        (0..nest_lvl + 2).fold(String::new(), |a, _| a + "\t");
    let body_indent = (0..nest_lvl + 3).fold(String::new(), |a, _| a + "\t");
    let color = match nest_lvl % 3 {
        0 => "blue",
        1 => "green",
        2 => "red",
        _ => unreachable!(),
    };
    println!(
        "{subgraph_indent}subgraph cluster_{fn_name}_loop{} {{",
        lp.header
    );
    println!("{body_indent}label=\"\";");
    println!("{body_indent}color=\"{color}\";");
    println!("{body_indent}style=\"rounded\";");
    println!("{body_indent}bgcolor=\"#FFFFFF\";");
    // sort for deterministic output
    let nodes: BTreeSet<_> = lp.nodes.iter().collect();
    for node in nodes {
        println!("{body_indent}{fn_name}_{node};");
    }
    // sort for deterministic output
    let mut nested = lp.nested.clone();
    nested.sort_by(|a, b| a.header.cmp(&b.header));
    for child in nested {
        display_loop(&child, nest_lvl + 1, fn_name);
    }
    println!("{subgraph_indent}}}");
}

fn display_clusters(cfg: &Cfg, args: &CLIArgs, fn_name: &str) {
    if !args.loops {
        return;
    }
    let domtree = compute_dominators(cfg);
    let mut loops = find_natural_loops(cfg, &domtree);
    loops.sort_by(|a, b| a.header.cmp(&b.header));
    for lp in loops {
        display_loop(&lp, 0, fn_name);
    }
}

/// Prints the edges of the dominator tree
fn display_dom(cfg: &Cfg, fn_name: &str) {
    let dom = compute_dominators(cfg);
    for n in cfg.blocks.keys() {
        let dominated = dom.immediately_dominated(*n);
        let sorted_dominated: BTreeSet<_> = dominated.iter().collect();
        for d in sorted_dominated {
            if *n != CFG_END_ID && *d != CFG_END_ID {
                println!(
                    "\t\t{fn_name}_{n} -> {fn_name}_{d} [style=\"dashed\"];"
                );
            }
        }
    }
    dom.check_dom_tree(cfg);
}

/// Performs an analysis on a cfg and returns a mapping from block ids to
/// CFG header and footer strings
/// # Arguments
/// * `df` - The name of the data flow analysis
/// * `cfg` - The cfg
/// # Returns
/// The mapping from block to header and footer information.
/// The map may not necessarily be a total mapping
fn display_facts(
    df: &Option<String>,
    cfg: &Cfg,
) -> HashMap<usize, (String, String)> {
    use cfg::CfgNode;
    let mut res = HashMap::new();
    match df {
        Some(x) if x == "live_vars" => {
            let out =
                analyze::<LiveVars, Backwards>(cfg, &LiveVars::top(), None);
            for (k, v) in &cfg.blocks {
                if let CfgNode::Block(block) = v {
                    let (out_fact, in_facts) =
                        out.block_facts(block, *k, Dir::Backwards);

                    let in_str = format!(
                        "{}\\n----------\\n",
                        in_facts.iter().fold(LiveVars::top(), |a, b| a.meet(b))
                    );
                    let out_str = format!("\\n----------\\n{out_fact}");
                    res.insert(*k, (in_str, out_str));
                } else {
                    res.insert(*k, (String::new(), String::new()));
                };
            }
        }
        Some(x) => panic!("Unrecognized dataflow pass: {x}"),
        _ => (),
    }
    res
}

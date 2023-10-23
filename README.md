# CS 6120 BRIL

This is a repository containing implementations of 
analyses, optimizations, and other passes for CS 6120
using the [Big Red Intermediate Language](https://capra.cs.cornell.edu/bril/intro.html)

Each of these tools is developed unix style and communicates via the shell.

## Contents

* `bril-rs` - Simple rust library for interfacing with Bril. Taken from Patrick LaFontaine in the [BRIL Repo](https://github.com/sampsyo/bril) with some small modifications.
* `brilirs` - A BRIL interpreter written in Rust. Taken from William Thompson in the [BRIL repo](https://github.com/sampsyo/bril) with some small modifcations.
* `cfg` - Library for constructing CFGs and performing data flow analyses. Currently
implemented analyses include reaching definitions, constructing dominator trees,
live variables, loop invariant instructions, and finding natural loops.
* `bril2cfg` - Converts bril to dot graphs. Can convert to CFG graphs, display data flow
analyses, and display the dominator tree.
* `test` - Test directory for [TURNT](https://github.com/cucapra/turnt) snapshot tests.
Most tests come from [the bril repo](https://github.com/sampsyo/bril) benchmarks.
* `dummy-pass` - Simply converts a bril program into a CFG and back into a bril program.
Removes unnecessary jumps in the conversion process.
* `local-dce` - Dead code elimination as a local optimization performed on basic
blocks. Also performs trivial global DCE by removing all pure instructions which
don't have their return values read
* `common-cli` - Procedural macros for the basic CLI options and interactions for
compiler passes
* `lvn` - Local value numbering performed on basic blocks. Also does 
constant folding, constant propagation, copy propagation, and algebraic simplification
at a basic block level.
* `dce` - (Regular/Global) dead code elimination
* `licm` - Loop invariant code motion
* `ssa` - Conversion into and out of SSA with semi-aggressive coalescing
* `is-ssa` - Asserts that a program is in SSA form or does not contain any phi
nodes (depending on arguments)
* `gc` - A (sort-of) incremental, generational garbage collector for `brilirs`
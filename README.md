# CS 6120 BRIL

This is a repository containing implementations of 
analyses, optimizations, and other passes for CS 6120
using the [Big Red Intermediate Language](https://capra.cs.cornell.edu/bril/intro.html)

Each of these tools is developed unix style and communicates via the shell.

## Contents

* `bril-rs` - Simple rust library for interfacing with Bril. Most of it
is taken from Patrick LaFontaine from [https://github.com/sampsyo/bril](https://github.com/sampsyo/bril)
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
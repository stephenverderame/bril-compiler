# CS 6120 BRIL

This is a repository containing implementations of 
analyses, optimizations, and other passes for CS 6120
using the [Big Red Intermediate Language](https://capra.cs.cornell.edu/bril/intro.html)

Each of these tools is developed unix style and communicates via the shell.

## Contents

* `bril-rs` - Simple rust library for interfacing with Bril. Most of it
is taken from Patrick LaFontaine from [https://github.com/sampsyo/bril](https://github.com/sampsyo/bril)
* `cfg` - Library for constructing CFGs
* `bril2cfg` - Converts bril to dot graphs
* `test` - Test directory for [TURNT](https://github.com/cucapra/turnt) snapshot tests.
Most tests come from [https://github.com/sampsyo/bril](https://github.com/sampsyo/bril) benchmarks.
* `dummy-pass` - Simply converts a bril program into a CFG and back into a bril program.
Removes unnecessary jumps in the conversion process.
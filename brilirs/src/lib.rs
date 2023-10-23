#![warn(clippy::all, clippy::pedantic, clippy::nursery)]
#![warn(missing_docs)]
#![allow(clippy::float_cmp)]
#![allow(clippy::similar_names)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::too_many_arguments)]
#![doc = include_str!("../README.md")]

use basic_block::BBProgram;
use bril_rs::Program;
use gc::error::PositionalInterpError;

/// The internal representation of brilirs, provided a ```TryFrom<Program>``` conversion
pub mod basic_block;
/// Provides ```check::type_check``` to validate [Program]
pub mod check;
#[doc(hidden)]
pub mod cli;
/// Provides ```interp::execute_main``` to execute [Program] that have been converted into [`BBProgram`]
pub mod interp;

#[doc(hidden)]
#[allow(clippy::needless_pass_by_value)]
#[allow(clippy::fn_params_excessive_bools)]
pub fn run_input<T: std::io::Write, U: std::io::Write>(
    input: impl std::io::Read,
    out: T,
    input_args: &[String],
    profiling: bool,
    profiling_out: U,
    check: bool,
    text: bool,
    _src_name: Option<String>,
    gc_settings: (usize, usize, usize),
    debug_gc: bool,
) -> Result<(), PositionalInterpError> {
    // It's a little confusing because of the naming conventions.
    //      - bril_rs takes file.json as input
    //      - bril2json takes file.bril as input
    let prog: Program = if text {
        unimplemented!("I got rid of this, for now.");
    } else {
        bril_rs::load_abstract_program_from_read(input).try_into()?
    };
    let bbprog: BBProgram = prog.try_into()?;
    check::type_check(&bbprog)?;

    if !check {
        interp::execute_main(
            &bbprog,
            out,
            input_args,
            profiling,
            profiling_out,
            gc_settings,
            debug_gc,
        )?;
    }

    Ok(())
}

#![warn(clippy::pedantic, clippy::nursery)]
#![allow(clippy::enum_glob_use)]
use std::collections::HashMap;

use bril_rs::{Code, Function, Instruction, Literal, ValueOps};
use cfg::{BasicBlock, CfgNode};
use common_cli::{cli_args, compiler_pass};

#[cli_args]
struct ExtraArgs {}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Copy)]
struct ValNum(usize);

impl ValNum {
    const fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    Add(ValNum, ValNum),
    Mul(ValNum, ValNum),
    Sub(ValNum, ValNum),
    Div(ValNum, ValNum),
    Id(ValNum),
    Eq(ValNum, ValNum),
    Lt(ValNum, ValNum),
    Gt(ValNum, ValNum),
    Le(ValNum, ValNum),
    Ge(ValNum, ValNum),
    Bool(bool),
    Int(i64),
    /// A unique value for values we cannot reason about such as calls
    Unique(u64),
}

type Env = HashMap<String, ValNum>;
type Locs = HashMap<ValNum, String>;
type Vns = HashMap<Value, ValNum>;

/// The state of the data structures used in local value numbering
#[derive(Debug)]
struct LvnState {
    /// Maps variable names to their value numbers
    /// Invariant: `exists x st. env[x] = v /\ locs[v] = x`
    env: Env,
    /// Maps value numbers to their home location
    locs: Locs,
    /// Maps value expressions to their value numbers
    /// Invariant: `forall (k, v) in vns, v in locs.keys()`
    vns: Vns,
    cur_val: ValNum,
    lvn_temp_num: u64,
}

impl LvnState {
    fn prototype(&self, lvn_temp_num: u64) -> Self {
        Self {
            env: self.env.clone(),
            locs: self.locs.clone(),
            vns: self.vns.clone(),
            cur_val: self.cur_val,
            lvn_temp_num,
        }
    }
}

fn initialize_lvn(func: &Function) -> LvnState {
    let mut env = Env::new();
    let mut locs = Locs::new();
    let mut vns = Vns::new();
    for (i, arg) in func.args.iter().enumerate() {
        let val_num = ValNum(i);
        env.insert(arg.name.clone(), val_num);
        locs.insert(val_num, arg.name.clone());
        vns.insert(Value::Id(val_num), val_num);
    }
    LvnState {
        env,
        locs,
        vns,
        cur_val: ValNum(func.args.len()),
        lvn_temp_num: 0,
    }
}

#[compiler_pass(true)]
fn lvn(mut cfg: Cfg, _args: &CLIArgs, func: &Function) -> Cfg {
    let lvn_state = initialize_lvn(func);
    let mut lvn_temp_num = lvn_state.lvn_temp_num;
    for block in &mut cfg.blocks.iter_mut().filter_map(|(_, node)| match node {
        CfgNode::Block(block) => Some(block),
        _ => None,
    }) {
        lvn_temp_num = block_lvn(block, lvn_state.prototype(lvn_temp_num));
    }
    cfg
}

fn make_val(instr: &Instruction, env: &Env, uid: &mut u64) -> Option<Value> {
    use Value::*;
    if let Some(ret) = instr.get_type() {
        if ret != bril_rs::Type::Int && ret != bril_rs::Type::Bool {
            return None;
        }
    }
    match instr {
        Instruction::Value { op, args, .. } => match op {
            ValueOps::Add => Some(Add(env[&args[0]], env[&args[1]])),
            ValueOps::Mul => Some(Mul(env[&args[0]], env[&args[1]])),
            ValueOps::Sub => Some(Sub(env[&args[0]], env[&args[1]])),
            ValueOps::Div => Some(Div(env[&args[0]], env[&args[1]])),
            ValueOps::Eq => Some(Eq(env[&args[0]], env[&args[1]])),
            ValueOps::Lt => Some(Lt(env[&args[0]], env[&args[1]])),
            ValueOps::Gt => Some(Gt(env[&args[0]], env[&args[1]])),
            ValueOps::Le => Some(Le(env[&args[0]], env[&args[1]])),
            ValueOps::Ge => Some(Ge(env[&args[0]], env[&args[1]])),
            ValueOps::Id => Some(Id(env[&args[0]])),
            ValueOps::Call | ValueOps::Load => {
                *uid += 1;
                Some(Unique(*uid - 1))
            }
            _ => None,
        },
        Instruction::Constant {
            value: Literal::Bool(value),
            ..
        } => Some(Bool(*value)),
        Instruction::Constant {
            value: Literal::Int(value),
            ..
        } => Some(Int(*value)),
        Instruction::Constant { .. } | Instruction::Effect { .. } => None,
    }
}

/// Generates a value instruction from `op` and `args`
/// Requires that `original_instr` is not an effect
fn make_val_instr(
    op: ValueOps,
    args: Vec<String>,
    original_instr: &Instruction,
) -> Instruction {
    Instruction::Value {
        dest: original_instr.get_dest().unwrap(),
        op,
        args,
        pos: original_instr.get_pos(),
        funcs: vec![],
        labels: vec![],
        // unwrap bc original_instr should not be an effect
        op_type: original_instr.get_type().unwrap(),
    }
}

/// Generates a constant instruction from `value`
/// Requires that `original_instr` is not an effect
fn make_const_instr(
    value: Literal,
    original_instr: &Instruction,
) -> Instruction {
    Instruction::Constant {
        dest: original_instr.get_dest().unwrap(),
        op: bril_rs::ConstOps::Const,
        pos: original_instr.get_pos(),
        const_type: original_instr.get_type().unwrap(),
        value,
    }
}

/// Converts a value expression into a value instruction
#[allow(clippy::too_many_lines)]
fn val_to_instr(
    val: &Value,
    locs: &Locs,
    original_instr: &Instruction,
) -> Instruction {
    use Value::*;
    match val {
        Add(v1, v2) => make_val_instr(
            ValueOps::Add,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Mul(v1, v2) => make_val_instr(
            ValueOps::Mul,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Sub(v1, v2) => make_val_instr(
            ValueOps::Sub,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Div(v1, v2) => make_val_instr(
            ValueOps::Div,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Eq(v1, v2) => make_val_instr(
            ValueOps::Eq,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Lt(v1, v2) => make_val_instr(
            ValueOps::Lt,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Gt(v1, v2) => make_val_instr(
            ValueOps::Gt,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Le(v1, v2) => make_val_instr(
            ValueOps::Le,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Ge(v1, v2) => make_val_instr(
            ValueOps::Ge,
            vec![locs[v1].clone(), locs[v2].clone()],
            original_instr,
        ),
        Id(v) => {
            make_val_instr(ValueOps::Id, vec![locs[v].clone()], original_instr)
        }
        Bool(b) => make_const_instr(Literal::Bool(*b), original_instr),
        Int(i) => make_const_instr(Literal::Int(*i), original_instr),
        Unique(_) => original_instr.clone(),
    }
}

/// Generate new value numbers for any values we haven't yet seen in the arguments
/// of an instruction
fn gen_new_vals(instr: &Instruction, mut state: LvnState) -> LvnState {
    if let Some(args) = instr.get_args() {
        for a in args {
            if !state.env.contains_key(a) {
                state.env.insert(a.clone(), state.cur_val);
                state.locs.insert(state.cur_val, a.clone());
                state.vns.insert(Value::Id(state.cur_val), state.cur_val);
                state.cur_val = state.cur_val.next();
            }
        }
    }
    state
}

/// Generates an instruction from `instr` that assigns
/// the value of `var` to the destination of `instr`
fn make_id_instr(var: &str, instr: &Instruction) -> Instruction {
    match instr {
        Instruction::Constant {
            dest,
            op: _,
            pos,
            const_type,
            value: _,
        } => Instruction::Value {
            dest: dest.to_string(),
            op: ValueOps::Id,
            args: vec![var.to_string()],
            pos: pos.clone(),
            funcs: vec![],
            labels: vec![],
            op_type: const_type.clone(),
        },
        Instruction::Value {
            dest,
            op: _,
            pos,
            op_type,
            args: _,
            funcs,
            labels,
        } => Instruction::Value {
            dest: dest.to_string(),
            op: ValueOps::Id,
            args: vec![var.to_string()],
            pos: pos.clone(),
            funcs: funcs.clone(),
            labels: labels.clone(),
            op_type: op_type.clone(),
        },
        Instruction::Effect { .. } => panic!("Expected constant or effect"),
    }
}

/// If `instr` overwrites a variable which housed a value number, add a new id instruction
/// to copy the old value into a new home and update the location of the value number
fn handle_overwrite(
    instr: &Instruction,
    mut state: LvnState,
    mut new_instrs: Vec<Instruction>,
) -> (LvnState, Vec<Instruction>) {
    // if dest
    if let Some(dest) = instr.get_dest() {
        let mut rehome = None;
        // if dest is numbered
        if let Some(num) = state.env.get(&dest) {
            // if dest is home to a value number
            if let Some(home) = state.locs.get_mut(num) {
                if home == &dest {
                    *home = format!("_{dest}_lvn{}", state.lvn_temp_num);
                    rehome = Some((home.clone(), num));
                }
            }
        }

        if let Some((new_home, vn)) = rehome {
            new_instrs.push(Instruction::Value {
                args: vec![dest],
                dest: new_home.clone(),
                funcs: vec![],
                labels: vec![],
                op: ValueOps::Id,
                pos: instr.get_pos(),
                op_type: instr.get_type().unwrap(),
            });
            state.env.insert(new_home, *vn);
            state.lvn_temp_num += 1;
        }
    }
    (state, new_instrs)
}

/// Update the environment with the new value number for the destination
/// of the instruction
fn update_env(instr: &Instruction, val_num: ValNum, mut env: Env) -> Env {
    if let Some(dest) = instr.get_dest() {
        env.insert(dest, val_num);
    }
    env
}

/// Rewrites the arguments of `instr` to use the new value numbers
fn rewrite_instr(instr: &mut Instruction, state: &LvnState) {
    if let Some(args) = instr.get_args_mut() {
        for arg in args {
            if let Some(num) = state.env.get(arg) {
                *arg = state.locs[num].clone();
            }
        }
    }
}

/// Performs local value numbering on a basic block
/// # Arguments
/// * `block` - The basic block to perform local value numbering on
/// * `state` - The current state of the local value numbering structures
fn block_lvn(block: &mut BasicBlock, mut state: LvnState) -> u64 {
    use std::collections::hash_map::Entry;
    // unique id for values we cannot reason about such as calls
    let mut uid = 0u64;
    let mut new_instrs = vec![];
    let mut new_terminator = None;
    for instr in block.instrs.iter_mut().chain(block.terminator.as_mut()) {
        state = gen_new_vals(instr, state);
        rewrite_instr(instr, &state);
        let val = make_val(instr, &state.env, &mut uid);
        if let Some(val) = val {
            *instr = val_to_instr(&val, &state.locs, instr);
            (state, new_instrs) = handle_overwrite(instr, state, new_instrs);
            let val_num = match state.vns.entry(val) {
                Entry::Vacant(e) => {
                    e.insert(state.cur_val);
                    state.locs.insert(
                        state.cur_val,
                        instr.get_dest().unwrap().clone(),
                    );
                    let r = state.cur_val;
                    state.cur_val = state.cur_val.next();
                    r
                }
                Entry::Occupied(num_entry) => {
                    let num = *num_entry.get();
                    *instr = make_id_instr(&state.locs[&num], instr);
                    num
                }
            };
            state.env = update_env(instr, val_num, state.env);
        }
        if cfg::is_terminator(instr) {
            new_terminator = Some(instr.clone());
        } else {
            new_instrs.push(instr.clone());
        }
    }
    block.instrs = new_instrs;
    block.terminator = new_terminator;
    state.lvn_temp_num
}

const fn lvn_post(instrs: Vec<Code>) -> Vec<Code> {
    instrs
}

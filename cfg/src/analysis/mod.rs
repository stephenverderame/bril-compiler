use crate::{CFG_END_ID, CFG_START_ID};

use super::{BasicBlock, Cfg, CfgEdgeTo, CfgNode};
use bril_rs::Instruction;
use std::collections::HashMap;
pub mod dominators;
pub mod live_vars;
pub mod loops;
pub mod moveable_instrs;
pub mod reaching_defs;

/// A fact in the analysis
pub trait Fact: PartialEq + Clone {
    /// Returns the top element of the lattice
    fn top() -> Self;

    /// Returns the greatest lower bound of the two facts
    #[must_use]
    fn meet(&self, b: &Self) -> Self;

    /// Returns the output fact of the transfer function for
    /// the given instruction
    fn transfer(&self, instr: &Instruction, block_id: usize) -> Vec<Self>
    where
        Self: std::marker::Sized;
}

/// A direction of the analysis
pub trait Direction {
    /// Gets the adj list for the direction
    fn get_adj_list(cfg: &Cfg) -> HashMap<usize, Vec<usize>>;

    /// Iterates over the instructions in the block in the direction
    /// # Arguments
    /// * `it` - The iterator over the instructions
    /// * `func` - The function to call on each instruction
    ///    The function is called on instructions in the order of the direction
    ///    of the analysis
    fn local_iter<'a>(
        it: &mut dyn std::iter::DoubleEndedIterator<Item = &'a Instruction>,
        func: &mut dyn FnMut(&'a Instruction),
    );
}

#[derive(Clone, Copy, PartialEq, Eq)]
/// Analysis direction
pub enum Dir {
    Forwards,
    Backwards,
}

/// The result of an analysis
#[allow(clippy::module_name_repetitions)]
pub struct AnalysisResult<T: Fact> {
    pub in_facts: HashMap<*const Instruction, T>,
    pub block_out_facts: HashMap<usize, Vec<T>>,
}

impl<T: Fact> AnalysisResult<T> {
    /// Gets the "input" and "output" facts of a basic block
    /// "input" and "output" are relative to a forward analysis
    /// # Arguments
    /// * `block` - The block to get the facts for
    /// * `block_id` - The id of the block
    /// * `dir` - The direction of the analysis
    /// # Panics
    #[must_use]
    pub fn block_facts<'a>(
        &'a self,
        block: &BasicBlock,
        block_id: usize,
        dir: Dir,
    ) -> (&'a T, &'a [T]) {
        let mut it = block.instrs.iter().chain(block.terminator.as_ref());
        let instr = it.next().unwrap() as *const _;
        let last = it.last().map_or(instr, |x| x as *const _);
        if dir == Dir::Forwards {
            (
                self.in_facts.get(&instr).unwrap(),
                self.block_out_facts.get(&block_id).unwrap(),
            )
        } else {
            (
                self.in_facts.get(&last).unwrap(),
                self.block_out_facts.get(&block_id).unwrap(),
            )
        }
    }
}

/// A reference or an index into an array
enum Refy<'a, T> {
    Ref(&'a T),
    Idx(usize),
}

impl<'a, T> Refy<'a, T> {
    /// Borrows the reference or the index into the array
    const fn borrow(&self, array: &'a [T]) -> &T {
        match self {
            Self::Ref(r) => r,
            Self::Idx(p) => &array[*p],
        }
    }
}

/// Analyzes a basic block
/// # Arguments
/// * `cfg` - The CFG
/// * `block` - The block to analyze
/// * `res_in_facts` - The input facts for each instruction
/// * `in_fact` - The input fact for the block
/// # Returns
/// * Tuple of input facts for each instruction and the output fact for the block
fn analyze_basic_block<T: Fact, D: Direction>(
    cfg: &Cfg,
    block_id: usize,
    mut res_in_facts: HashMap<*const Instruction, T>,
    in_fact: &T,
) -> (HashMap<*const Instruction, T>, Vec<T>) {
    let mut fact = Refy::Ref(in_fact);
    let mut block_out = vec![];
    if let CfgNode::Block(block) = &cfg.blocks.get(&block_id).unwrap() {
        D::local_iter(
            &mut block.instrs.iter().chain(block.terminator.as_ref()),
            &mut |instr| {
                res_in_facts.insert(
                    instr as *const Instruction,
                    fact.borrow(&block_out).clone(),
                );
                block_out = fact.borrow(&block_out).transfer(instr, block_id);
                assert!(!block_out.is_empty());
                fact = Refy::Idx(0);
            },
        );
    }
    (res_in_facts, block_out)
}

/// Broadcasts the output facts to the neighbors
/// If there is one output fact, it is broadcasted to all neighbors
/// Otherwise, the number of output facts must be equal to the number of neighbors
/// # Arguments
/// * `out_fact` - The output fact of the current block
/// * `in_facts` - The input facts for each block
/// * `adj_lst` - The adjacency list of the CFG
/// * `block` - The current block
/// # Returns
/// * The input facts for each block
fn broadcast_out_facts<T: Fact>(
    out_fact: &[T],
    mut in_facts: HashMap<usize, T>,
    adj_lst: &HashMap<usize, Vec<usize>>,
    block: usize,
) -> HashMap<usize, T> {
    if out_fact.is_empty() {
        // do nothing (meet w/ top)
    } else if out_fact.len() == 1 {
        for neighbor in adj_lst.get(&block).unwrap() {
            in_facts.insert(
                *neighbor,
                in_facts.get(neighbor).unwrap().meet(&out_fact[0]),
            );
        }
    } else {
        assert_eq!(out_fact.len(), adj_lst.get(&block).unwrap().len());
        for (neighbor, fact) in
            adj_lst.get(&block).unwrap().iter().zip(out_fact)
        {
            in_facts
                .insert(*neighbor, in_facts.get(neighbor).unwrap().meet(fact));
        }
    }
    in_facts
}

/// Performs an analysis pass on the CFG
/// # Arguments
/// * `cfg` - The CFG
/// * `restricted_set` - The set of blocks to analyze or None to analyze all blocks
/// * `top` - The top element of the lattice or `None` to use `T::top()`
/// # Returns
/// * The input and output facts for each instruction
/// # Panics
///
#[must_use]
pub fn analyze<T: Fact, D: Direction>(
    cfg: &Cfg,
    restricted_set: Option<&[usize]>,
    top: Option<T>,
) -> AnalysisResult<T> {
    use std::collections::hash_map::Entry;
    let mut in_facts: HashMap<usize, T> = HashMap::new();
    let mut out_facts: HashMap<usize, Vec<T>> = HashMap::new();
    let mut res_in_facts: HashMap<*const Instruction, T> = HashMap::new();
    let mut worklist: Vec<usize> = Vec::new();
    let adj_lst = D::get_adj_list(cfg);
    let top = top.unwrap_or_else(T::top);
    in_facts.extend(cfg.blocks.keys().map(|k| (*k, top.clone())));
    worklist.extend(cfg.blocks.keys());

    while let Some(block) = worklist.pop() {
        if let Some(restricted_set) = restricted_set {
            if !restricted_set.contains(&block) {
                continue;
            }
        }
        let in_fact = in_facts.get(&block).unwrap();
        let out_fact;
        (res_in_facts, out_fact) =
            analyze_basic_block::<T, D>(cfg, block, res_in_facts, in_fact);
        let add_neighbors = match out_facts.entry(block) {
            Entry::Occupied(o) => o.get() != &out_fact,
            Entry::Vacant(_) => true,
        };
        if add_neighbors && block != CFG_END_ID && block != CFG_START_ID {
            in_facts =
                broadcast_out_facts(&out_fact, in_facts, &adj_lst, block);
            out_facts.insert(block, out_fact);
            worklist.extend(adj_lst.get(&block).unwrap());
        }
    }

    AnalysisResult {
        in_facts: res_in_facts,
        block_out_facts: out_facts,
    }
}

pub struct Forwards {}
impl Direction for Forwards {
    fn get_adj_list(cfg: &Cfg) -> HashMap<usize, Vec<usize>> {
        let mut res = HashMap::new();
        for (k, v) in &cfg.adj_lst {
            match v {
                CfgEdgeTo::Next(n) => res.insert(*k, vec![*n]),
                CfgEdgeTo::Branch {
                    true_node: t,
                    false_node: f,
                } => res.insert(*k, vec![*t, *f]),
                CfgEdgeTo::Terminal => res.insert(*k, vec![]),
            };
        }
        res
    }

    fn local_iter<'a>(
        it: &mut dyn std::iter::DoubleEndedIterator<Item = &'a Instruction>,
        func: &mut dyn FnMut(&'a Instruction),
    ) {
        for instr in it {
            func(instr);
        }
    }
}

pub struct Backwards {}
impl Direction for Backwards {
    fn get_adj_list(cfg: &Cfg) -> HashMap<usize, Vec<usize>> {
        let mut res = HashMap::new();
        for (k, v) in &cfg.adj_lst {
            res.entry(*k).or_insert_with(Vec::default);
            match v {
                CfgEdgeTo::Next(n) => {
                    res.entry(*n).or_insert_with(Vec::new).push(*k);
                }
                CfgEdgeTo::Branch {
                    true_node: t,
                    false_node: f,
                } => {
                    res.entry(*t).or_insert_with(Vec::new).push(*k);
                    res.entry(*f).or_insert_with(Vec::new).push(*k);
                }
                CfgEdgeTo::Terminal => {}
            };
        }
        res
    }

    fn local_iter<'a>(
        it: &mut dyn std::iter::DoubleEndedIterator<Item = &'a Instruction>,
        func: &mut dyn FnMut(&'a Instruction),
    ) {
        for instr in it.rev() {
            func(instr);
        }
    }
}

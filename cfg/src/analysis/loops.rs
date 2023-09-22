use crate::CFG_END_ID;

use super::{dominators::DomTree, Cfg};
use std::collections::{BinaryHeap, HashSet};

/// A natural loop in the CFG
#[derive(Clone, Debug)]
pub struct NaturalLoop {
    /// the header of the loop
    pub header: usize,
    /// set of all nodes in the loop
    pub nodes: HashSet<usize>,
    /// set of all nodes outside the loop that have predecessors in the loop
    pub exits: Vec<usize>,
    /// list of all nested loops
    pub nested: Vec<NaturalLoop>,
}

impl NaturalLoop {
    /// Returns the natural loop for the backedge `(u, v)` in the CFG
    /// This is found by performing a DFS from `v` and collecting all nodes
    /// until the path reaches `u`
    /// Writeup note: Basically done by Copilot
    fn from_backedge(backedge: (usize, usize), cfg: &Cfg) -> Option<Self> {
        let transposed = cfg.preds();
        let (u, header) = backedge;
        let mut nodes = HashSet::new();
        nodes.insert(u);
        nodes.insert(header);
        // start w/ tail, go backwards until we hit the header
        let mut stack = vec![u];
        while let Some(node) = stack.pop() {
            if node == header {
                // reached header
                break;
            }
            nodes.insert(node);
            for n in transposed.get(&node).unwrap_or(&Vec::new()) {
                if !nodes.contains(n) {
                    stack.push(*n);
                }
            }
        }
        nodes.remove(&CFG_END_ID);
        let mut exits = Vec::new();
        for node in &nodes {
            for next in cfg.adj_lst[node].nodes() {
                if !nodes.contains(&next) {
                    exits.push(next);
                    break;
                }
            }
            if *node != header
                && !transposed
                    .get(node)
                    .unwrap_or(&Vec::new())
                    .iter()
                    .all(|p| nodes.contains(p))
            {
                // not a natural loop
                // predecessor of a non-header node is not in the loop
                return None;
            }
        }
        Some(Self {
            header,
            nodes,
            exits,
            nested: Vec::new(),
        })
    }

    /// Returns the union of two natural loops
    /// # Panics
    /// * If the two loops have different headers
    fn merge(&mut self, other: &Self, cfg: &Cfg) {
        assert_eq!(self.header, other.header);
        self.nodes.extend(other.nodes.iter().copied());
        let mut exits = Vec::new();
        for node in &self.nodes {
            if cfg.adj_lst[node]
                .nodes()
                .iter()
                .any(|n| !self.nodes.contains(n))
            {
                exits.push(*node);
            }
        }
        self.exits = exits;
    }
}

/// Returns a list of backedges `(u, v)` in the CFG
/// A backedge `(u, v)` is an edge from `u` to `v` where `v` dominates `u`
fn find_backedges(cfg: &Cfg, domtree: &DomTree) -> Vec<(usize, usize)> {
    let mut res = Vec::new();
    for (node_start, edge) in &cfg.adj_lst {
        for node_end in edge.nodes() {
            if domtree.is_dominator(node_end, *node_start) {
                res.push((*node_start, node_end));
            }
        }
    }
    res
}

/// Finds all backedges that have the same header and merges them into a single
/// natural loop, removing the backedges from the list
/// # Arguments
/// * `header` - The header of the natural loop
/// * `cfg` - The CFG
/// * `backedges` - The list of backedges
/// # Returns
/// The merged natural loop with the given header or `None` if no backedges
/// have the given header
fn merge_loops(
    header: usize,
    cfg: &Cfg,
    backedges: &mut Vec<(usize, usize)>,
) -> Option<NaturalLoop> {
    let mut edges = Vec::new();
    let mut to_remove = BinaryHeap::new();
    for (idx, edge @ (_, v)) in backedges.iter().enumerate() {
        if v == &header {
            edges.push(*edge);
            to_remove.push(idx);
        }
    }
    // pop back to front so indices don't change
    while let Some(idx) = to_remove.pop() {
        backedges.swap_remove(idx);
    }
    let mut lp = None;
    while lp.is_none() && !edges.is_empty() {
        lp = NaturalLoop::from_backedge(edges.swap_remove(0), cfg);
    }
    lp.map(|mut lp| {
        for edge in edges {
            if let Some(other) = NaturalLoop::from_backedge(edge, cfg) {
                lp.merge(&other, cfg);
            }
        }
        lp
    })
}

/// Returns all natural loops which have the given header or are nested within
/// a loop with the given header
/// # Arguments
/// * `backedges` - The list of backedges
/// * `cfg` - The CFG
/// * `header` - The header of the natural loop
/// # Returns
/// The natural loop with the given header or `None` if no backedges have the
/// given header
fn form_loop(
    backedges: &mut Vec<(usize, usize)>,
    cfg: &Cfg,
    header: usize,
) -> Option<NaturalLoop> {
    if let Some(mut lp) = merge_loops(header, cfg, backedges) {
        for n in &lp.nodes {
            if let Some(nested_lp) = form_loop(backedges, cfg, *n) {
                lp.nested.push(nested_lp);
            }
        }
        Some(lp)
    } else {
        None
    }
}

/// Adds a natural loop to the list of natural loops
/// If any of the existing loops in the list have a header which is in the new loop,
/// the existing loop is added as a nested loop of the new loop
/// # Arguments
/// * `loops` - The list of natural loops
/// * `lp` - The new natural loop
/// # Returns
/// The list of natural loops with the new loop added
fn add_to_loop_list(
    mut loops: Vec<NaturalLoop>,
    mut lp: NaturalLoop,
) -> Vec<NaturalLoop> {
    let mut children = BinaryHeap::new();
    for (idx, node) in loops.iter().enumerate() {
        if lp.nodes.contains(&node.header) {
            children.push(idx);
        }
    }
    while let Some(nest_idx) = children.pop() {
        lp.nested.push(loops.swap_remove(nest_idx));
    }
    loops.push(lp);
    loops
}

/// Returns a list of natural loops in the CFG
/// Natural loops with the same headers have been merged
///
/// Thus, loops are either disjoint or nested
#[must_use]
#[allow(clippy::module_name_repetitions)]
pub fn find_natural_loops(cfg: &Cfg, domtree: &DomTree) -> Vec<NaturalLoop> {
    let mut res = Vec::new();
    let mut backedges = find_backedges(cfg, domtree);
    while let Some((_, v)) = backedges.last().copied() {
        let lp = form_loop(&mut backedges, cfg, v);
        if let Some(lp) = lp {
            // only need to take into account child loops that have
            // already been made because if the parent loop is made first,
            // any child loops will be added to the parent loop in
            // `form_loop`
            res = add_to_loop_list(res, lp);
        }
    }
    res
}

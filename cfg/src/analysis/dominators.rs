use std::collections::HashSet;

use super::*;

/// A node in the dominator tree
pub struct DomNode {
    /// The block id
    block: usize,
    /// The blocks immediately dominated by `block`
    dominated: Vec<usize>,
}

impl DomNode {
    /// Returns true if `self` dominates `n`
    /// # Arguments
    /// * `nodes` - A map from each block id to `DomTree` node
    /// * `n` - The block
    /// # Returns
    /// * True if `self` dominates `n`
    fn is_dominator(&self, nodes: &HashMap<usize, Self>, n: usize) -> bool {
        self.block == n
            || self
                .dominated
                .iter()
                .any(|&d| nodes[&d].is_dominator(nodes, n))
    }

    /// Returns the blocks strictly dominated by `self`
    /// # Arguments
    /// * `nodes` - A map from each block id to `DomTree` node
    /// * `doms` - The accumulated set of blocks dominated by `self`
    fn dominated(
        &self,
        nodes: &HashMap<usize, Self>,
        mut doms: HashSet<usize>,
    ) -> HashSet<usize> {
        for &dom in &self.dominated {
            if doms.insert(dom) {
                doms = nodes[&dom].dominated(nodes, doms);
            }
        }
        doms
    }
}

/// A dominator tree
pub struct DomTree {
    /// A map from each block id to `DomTree` node
    nodes: HashMap<usize, DomNode>,
}

/// Returns true if `dominator` dominates `node`
/// Does this by performing a DFS from start and checking if we reach `node` before `dominator`
fn slow_is_dom(
    node: usize,
    dominator: usize,
    adj_lst: &HashMap<usize, CfgEdgeTo>,
) -> bool {
    let mut visited = HashSet::new();
    let mut stack = vec![CFG_START_ID];
    // DFS from start, we fail if we reach `node`
    // we end the branch if we reach `dominator`
    while !stack.is_empty() {
        let n = stack.pop();
        if visited.contains(&n) || n == Some(dominator) {
            continue;
        }
        visited.insert(n);
        if n == Some(node) {
            return false;
        }

        if let Some(succs) = adj_lst.get(&n.unwrap()) {
            stack.extend(succs.nodes().iter());
        }
    }
    true
}

impl DomTree {
    /// Constructs a new dom tree
    /// # Arguments
    /// * `doms` - A map from each block to nodes that dominate it
    /// # Returns
    /// * The dom tree
    fn new(doms_map: &HashMap<usize, HashSet<usize>>) -> Self {
        let mut nodes = doms_map
            .keys()
            .copied()
            .map(|k| {
                (
                    k,
                    DomNode {
                        block: k,
                        dominated: Vec::new(),
                    },
                )
            })
            .collect::<HashMap<_, _>>();
        for (block, block_dominators) in doms_map {
            for dominator in block_dominators.iter().filter(|x| **x != *block) {
                // all the nodes that `dominator` dominates
                let dominated = doms_map
                    .iter()
                    .filter_map(|(k, v)| {
                        if v.contains(dominator) && *k != *dominator {
                            Some(*k)
                        } else {
                            None
                        }
                    })
                    .collect::<HashSet<_>>();

                // > 1 because `block` should be in both sets
                if dominated.intersection(doms_map.get(block).unwrap()).count()
                    > 1
                {
                    // dominator dominates a node which is also a
                    // dominator of `block`

                    // so `dominator` is not a strict dominator
                    continue;
                }
                nodes.get_mut(dominator).unwrap().dominated.push(*block);
            }
        }
        Self { nodes }
    }
    /// Returns true if `dom` dominates `block`
    /// # Arguments
    /// * `dom` - The potential dominator
    /// * `block` - The block
    /// # Returns
    /// * True if `dom` dominates `block`
    /// # Panics
    /// * If `block` is not in the CFG
    #[must_use]
    pub fn is_dominator(&self, dom: usize, block: usize) -> bool {
        block == dom
            || self
                .nodes
                .get(&dom)
                .unwrap()
                .dominated
                .iter()
                .any(|d| self.nodes[d].is_dominator(&self.nodes, block))
    }

    /// Computes the dominance frontier of a block
    /// The dominance frontier of a block `b` is the set of blocks `d` such that
    /// `d` is a successor of a block `s` dominated by `b` but `d` is not dominated by `b`
    /// # Arguments
    /// * `block` - The block
    /// * `cfg` - The CFG
    /// # Returns
    /// * The dominance frontier of `block`
    #[must_use]
    pub fn dom_frontier(&self, block: usize, cfg: &Cfg) -> Vec<usize> {
        let dominated =
            self.nodes[&block].dominated(&self.nodes, HashSet::new());
        let mut frontier = Vec::new();
        for dom in &dominated {
            let dom = *dom;
            let dom_succs = cfg.adj_lst[&dom].nodes();
            for succ in dom_succs {
                if !dominated.contains(&succ) {
                    frontier.push(dom);
                }
            }
        }
        frontier
    }

    /// Returns all the blocks dominated by `block`
    #[must_use]
    pub fn dominated(&self, block: usize) -> HashSet<usize> {
        self.nodes[&block].dominated(&self.nodes, HashSet::new())
    }

    /// Returns the blocks immediately (and strictly) dominated by `block`
    #[must_use]
    pub fn immediately_dominated(&self, block: usize) -> HashSet<usize> {
        self.nodes[&block].dominated.iter().copied().collect()
    }

    /// Checks that the dominator tree is correct
    /// # Arguments
    /// * `cfg` - The CFG
    /// # Panics
    /// * If the dominator tree is incorrect
    pub fn check_dom_tree(&self, cfg: &Cfg) {
        let adj_lst = &cfg.adj_lst;

        for (block, node) in &self.nodes {
            // TODO: if we do something with the end block, we may want to regularize it
            // Ex: all returns go to the end block
            for other in self.nodes.keys() {
                if other != block
                    && *other != CFG_END_ID
                    && *block != CFG_START_ID
                {
                    if node
                        .dominated(&self.nodes, HashSet::new())
                        .contains(other)
                    {
                        // block dominates other
                        assert!(
                            slow_is_dom(*other, *block, adj_lst),
                            "dominator tree is incorrect"
                        );
                    } else {
                        // block does not dominate other
                        assert!(
                            !slow_is_dom(*other, *block, adj_lst),
                            "dominator tree is incorrect"
                        );
                    }
                }
            }
        }
    }
}

/// Computes the dominators of each block in the CFG
/// # Arguments
/// * `cfg` - The CFG
/// # Returns
/// * A map from each block to nodes that dominate it
/// # Panics
#[must_use]
#[allow(clippy::module_name_repetitions)]
pub fn compute_dominators(cfg: &Cfg) -> DomTree {
    let preds = cfg.preds();
    let mut doms: HashMap<_, HashSet<_>> = HashMap::new();
    let all_blocks = cfg.blocks.keys().copied().collect::<HashSet<_>>();
    for block in cfg.blocks.keys() {
        doms.insert(*block, all_blocks.clone());
    }
    let mut changed = true;
    let default_preds = Vec::new();
    while changed {
        changed = false;
        for block in cfg.blocks.keys() {
            let mut pred_iter =
                preds.get(block).unwrap_or(&default_preds).iter();
            let mut new_dom: HashSet<usize> = pred_iter
                .next()
                .map(|x| doms.get(x).unwrap().clone())
                .unwrap_or_default();
            for pred in pred_iter {
                new_dom = new_dom
                    .intersection(doms.get(pred).unwrap())
                    .copied()
                    .collect();
            }
            new_dom.insert(*block);
            if new_dom != *doms.get(block).unwrap_or(&HashSet::new()) {
                doms.insert(*block, new_dom);
                changed = true;
            }
        }
    }
    // doms.insert(CFG_START_ID, HashSet::new());
    DomTree::new(&doms)
}

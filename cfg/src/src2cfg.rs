use std::collections::HashSet;

use super::*;
/// Returns true if `instr` is a nop
const fn is_nop(instr: &Instruction) -> bool {
    matches!(
        instr,
        Instruction::Effect {
            op: EffectOps::Nop,
            ..
        }
    )
}
impl Cfg {
    /// Finishes the current block and adds it to the CFG
    /// # Arguments
    /// * `active_block` - The current block
    /// * `terminator` - The terminator instruction of the block
    /// * `active_labels` - The labels for the current block
    /// * `next_id` - The next id to use for a block
    /// * `blocks` - The map from node id to instruction
    /// * `labels` - The map from label to node id
    /// # Returns
    /// * The next id to use for a block
    fn add_block(
        mut active_block: BasicBlock,
        terminator: Option<Instruction>,
        active_labels: Vec<String>,
        next_id: usize,
        blocks: &mut BTreeMap<usize, CfgNode>,
        labels: &mut HashMap<String, usize>,
    ) -> usize {
        active_block.terminator = terminator;
        blocks.insert(next_id, CfgNode::Block(active_block));
        for lbl in active_labels {
            labels.insert(lbl, next_id);
        }
        next_id + 1
    }

    /// Loops through all instructions, creating basic blocks and
    /// adding them to the CFG. Returns the last basic block,
    /// labels that are still active, and the next id to use for a block
    fn create_blocks_for_instrs(
        f: &Function,
        mut id: usize,
        single_mode: bool,
        blocks: &mut BTreeMap<usize, CfgNode>,
        labels: &mut HashMap<String, usize>,
    ) -> (BasicBlock, Vec<String>, usize) {
        let mut active_block = BasicBlock::default();
        // the labels we encounter before the next instruction
        let mut active_labels = Vec::new();
        for code in &f.instrs {
            match code {
                Code::Label { label, .. } => {
                    if !active_block.is_empty() {
                        id = Self::add_block(
                            active_block,
                            None,
                            active_labels,
                            id,
                            blocks,
                            labels,
                        );
                        active_block = BasicBlock::default();
                        active_labels = vec![label.clone()];
                    }
                    active_labels.push(label.clone());
                }
                Code::Instruction(instr) => {
                    if is_terminator(instr) {
                        id = Self::add_block(
                            active_block,
                            Some(instr.clone()),
                            active_labels,
                            id,
                            blocks,
                            labels,
                        );
                        active_block = BasicBlock::default();
                        active_labels = Vec::new();
                    } else if !is_nop(instr) {
                        active_block.instrs.push(instr.clone());
                        if single_mode {
                            // instruction-level CFG, so make every instruction
                            // its own block
                            id = Self::add_block(
                                active_block,
                                None,
                                active_labels,
                                id,
                                blocks,
                                labels,
                            );
                            active_block = BasicBlock::default();
                            active_labels = Vec::new();
                        }
                    }
                }
            }
        }
        (active_block, active_labels, id)
    }

    /// Generate a CFG from a function
    /// # Arguments
    /// * `f` - The function
    /// * `single_mode` - If true, then a basic block is a single instruction
    /// # Returns
    /// * The CFG
    #[must_use]
    pub fn from(f: &Function, single_mode: bool) -> Self {
        // map from label to node id
        let mut labels = HashMap::new();
        // map from node id to instruction
        let mut blocks = BTreeMap::new();
        // node id counter
        let i = CFG_END_ID + 1;
        blocks.insert(CFG_START_ID, CfgNode::Start);
        blocks.insert(CFG_END_ID, CfgNode::End);
        let (leftover_block, leftover_labels, next_id) =
            Self::create_blocks_for_instrs(
                f,
                i,
                single_mode,
                &mut blocks,
                &mut labels,
            );
        if leftover_block.is_empty() {
            // any labels that are still active that are at the end of the function
            for lbl in leftover_labels {
                labels.insert(lbl, CFG_END_ID);
            }
        } else {
            Self::add_block(
                leftover_block,
                None,
                leftover_labels,
                next_id,
                &mut blocks,
                &mut labels,
            );
        }
        Self::gen_cfg_from_lbls_and_blocks(labels, blocks)
    }

    /// Generate a CFG from a map from label to node id and a map from node id to instruction
    ///
    /// # Arguments
    /// * `labels_map` - A map from label to node id
    /// * `blocks` - A map from node id to instruction
    /// * `labels_rev` - A map from node id to labels
    #[must_use]
    fn gen_cfg_from_lbls_and_blocks(
        labels_map: HashMap<String, usize>,
        blocks: BTreeMap<usize, CfgNode>,
    ) -> Self {
        // cfg adjacency list
        let mut adj_lst = HashMap::new();
        // the last id of an instruction included in the CFG
        // this is to keep track of a sequential stream of instructions
        let mut last_id = Some(CFG_START_ID);
        adj_lst.insert(CFG_END_ID, CfgEdgeTo::Terminal);
        for (id, instr) in blocks.iter().filter_map(|(id, instr)| match instr {
            CfgNode::Block(BasicBlock { terminator, .. }) => {
                Some((id, terminator))
            }
            CfgNode::Start | CfgNode::End => None,
        }) {
            if instr.is_none()
                || !Self::handle_effects(
                    instr.as_ref().unwrap(),
                    *id,
                    &labels_map,
                    &mut adj_lst,
                    &mut last_id,
                )
            {
                Self::add_edge(&mut adj_lst, &last_id, *id);
                last_id = Some(*id);
            }
        }
        // make the transition from the last sequntial instruction to be
        // to the end node.
        if let Some(last_id) = last_id {
            adj_lst.insert(last_id, CfgEdgeTo::Next(CFG_END_ID));
        }
        Self::splice_out_goto_and_make_self(adj_lst, blocks, labels_map)
    }

    /// Splice out blocks containing only jumps from the `adj_list`,
    /// constructs and CFG with
    /// the resulant `adj_list` and blocks, and then cleans the CFG
    /// which removes unreachable nodes
    fn splice_out_goto_and_make_self(
        adj_lst: HashMap<usize, CfgEdgeTo>,
        blocks: BTreeMap<usize, CfgNode>,
        labels_map: HashMap<String, usize>,
    ) -> Self {
        Self {
            blocks,
            adj_lst,
            labels: Self::construct_labels_map(labels_map),
        }
        .clean()
    }

    /// Constructs a map from labels to node ids
    fn construct_labels_map(
        labels_map: HashMap<String, usize>,
    ) -> HashMap<usize, Vec<String>> {
        let mut labels_rev = HashMap::new();
        for (lbl, id) in labels_map {
            labels_rev.entry(id).or_insert_with(Vec::new).push(lbl);
        }
        labels_rev
    }

    /// If `id` is a jump instruction, return the id of the next real (non-jump)
    /// node by following the chain of jumps.
    /// Otherwise, return `id`
    ///
    /// If `id` is the starting id, then we have an infinite loop
    /// and we return `None`
    /// # Arguments
    /// * `id` - The id of the jump instruction
    /// * `starting_id` - The id of the jump instruction that started the chain or
    ///    `None` if this is the first jump instruction in the chain
    /// # Returns
    /// * The id of the next real node or `None` if there is an infinite loop
    fn next_real_node(
        &self,
        node: usize,
        starting_id: Option<usize>,
    ) -> Option<usize> {
        if matches!(starting_id, Some(id) if id == node) {
            // infinite loop
            return None;
        }
        match &self.blocks.get(&node) {
            Some(CfgNode::Block(BasicBlock {
                terminator:
                    None
                    | Some(Instruction::Effect {
                        op: EffectOps::Jump,
                        ..
                    }),
                instrs,
                ..
            })) if instrs.is_empty() => {
                if let Some(CfgEdgeTo::Next(next)) = self.adj_lst.get(&node) {
                    self.next_real_node(*next, starting_id.or(Some(node)))
                } else {
                    Some(node)
                }
            }
            _ => Some(node),
        }
    }

    /// Removes unreachable nodes, empty blocks, and blocks that just contain jumps
    /// from the CFG
    /// # Returns
    /// * The cleaned CFG
    /// # Panics
    /// If an internal error occurs
    #[must_use]
    pub fn clean(mut self) -> Self {
        let mut visited = HashSet::new();
        let mut q = VecDeque::new();
        let mut new_adj_list = HashMap::new();
        q.push_back(CFG_START_ID);
        while !q.is_empty() {
            let reachable = q.pop_front().unwrap();
            if visited.contains(&reachable) {
                continue;
            }
            visited.insert(reachable);
            match self.adj_lst.get(&reachable) {
                Some(CfgEdgeTo::Next(next)) => {
                    let new_nxt =
                        self.next_real_node(*next, None).unwrap_or(reachable);
                    new_adj_list.insert(reachable, CfgEdgeTo::Next(new_nxt));
                    q.push_back(new_nxt);
                }
                Some(CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                }) => {
                    let true_node = self
                        .next_real_node(*true_node, None)
                        .unwrap_or(reachable);
                    let false_node = self
                        .next_real_node(*false_node, None)
                        .unwrap_or(reachable);
                    new_adj_list.insert(
                        reachable,
                        CfgEdgeTo::Branch {
                            true_node,
                            false_node,
                        },
                    );
                    q.push_back(true_node);
                    q.push_back(false_node);
                }
                Some(CfgEdgeTo::Terminal) | None => {
                    new_adj_list.insert(reachable, CfgEdgeTo::Terminal);
                }
            }
        }
        self.blocks.retain(|id, _| new_adj_list.contains_key(id));
        self.adj_lst = new_adj_list;
        self
    }

    /// Add an edge from each node in `froms` to `to`.
    fn add_edge(
        adj_lst: &mut HashMap<usize, CfgEdgeTo>,
        froms: &Option<usize>,
        to: usize,
    ) {
        if let Some(from) = froms {
            adj_lst.insert(*from, CfgEdgeTo::Next(to));
        }
    }

    /// Handles adding effect instructions to the CFG
    /// Adds `Effect { op, labels, }` to the CFG `adj_lst`
    /// Updates `last_id` accordingly
    ///
    /// # Arguments
    /// * `instr` - The effect instruction
    /// * `id` - The id of the effect instruction
    /// * `labels_map` - A map from label to node id
    /// * `adj_lst` - The adjacency list of the CFG
    /// * `last_id` - The last id of an instruction included in the CFG
    ///
    /// # Returns
    /// * `true` if the instruction was an effect instruction and was handled
    fn handle_effects(
        instr: &Instruction,
        id: usize,
        labels_map: &HashMap<String, usize>,
        adj_lst: &mut HashMap<usize, CfgEdgeTo>,
        last_id: &mut Option<usize>,
    ) -> bool {
        if let Instruction::Effect {
            op,
            args: _,
            labels,
            ..
        } = instr
        {
            match op {
                EffectOps::Branch => {
                    assert_eq!(labels.len(), 2);
                    let true_node = *labels_map.get(&labels[0]).unwrap();
                    let false_node = *labels_map.get(&labels[1]).unwrap();
                    adj_lst.insert(
                        id,
                        CfgEdgeTo::Branch {
                            true_node,
                            false_node,
                        },
                    );
                    Self::add_edge(adj_lst, last_id, id);
                    *last_id = None;
                    true
                }
                EffectOps::Jump => {
                    let next = *labels_map.get(&labels[0]).unwrap();
                    Self::add_edge(adj_lst, last_id, id);
                    Self::add_edge(adj_lst, &Some(id), next);
                    *last_id = None;
                    true
                }
                EffectOps::Return => {
                    Self::add_edge(adj_lst, last_id, id);
                    Self::add_edge(adj_lst, &Some(id), CFG_END_ID);
                    *last_id = None;
                    true
                }
                // do not change last_id
                EffectOps::Nop => true,
                _ => false,
            }
        } else {
            false
        }
    }
}

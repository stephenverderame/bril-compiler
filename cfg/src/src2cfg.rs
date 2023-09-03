use super::*;
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
                    } else {
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
        mut adj_lst: HashMap<usize, CfgEdgeTo>,
        blocks: BTreeMap<usize, CfgNode>,
        labels_map: HashMap<String, usize>,
    ) -> Self {
        for (self_id, edge) in &mut adj_lst {
            match edge {
                CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                } => {
                    *true_node = Self::get_next_real_node(
                        &blocks,
                        *true_node,
                        &labels_map,
                        None,
                    )
                    .unwrap_or(*self_id);
                    *false_node = Self::get_next_real_node(
                        &blocks,
                        *false_node,
                        &labels_map,
                        None,
                    )
                    .unwrap_or(*self_id);
                }
                CfgEdgeTo::Next(next) => {
                    *next = Self::get_next_real_node(
                        &blocks,
                        *next,
                        &labels_map,
                        None,
                    )
                    .unwrap_or(*self_id);
                }
                CfgEdgeTo::Terminal => {}
            }
        }
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
    /// * `blocks` - A map from node id to instruction
    /// * `id` - The id of the jump instruction
    /// * `labels_map` - A map from label to node id
    /// * `starting_id` - The id of the first jump instruction in the chain or
    /// `None` if this is the first jump instruction in the chain
    ///
    /// # Returns
    /// * `Some(id)` where `id` is the id of the next real node or `None` if
    ///  there is an infinite loop
    fn get_next_real_node(
        blocks: &BTreeMap<usize, CfgNode>,
        id: usize,
        labels_map: &HashMap<String, usize>,
        starting_id: Option<usize>,
    ) -> Option<usize> {
        if starting_id.map_or(false, |first_id| id == first_id) {
            // infinite loop
            return None;
        }
        // we don't worry about totally empty blocks
        // because we never construct a block that is completely empty
        // ie:
        // ```
        // .foo:
        // .bar:
        // ```
        // this is handled
        if let Some(CfgNode::Block(BasicBlock {
            terminator:
                Some(Instruction::Effect {
                    op: EffectOps::Jump,
                    labels: dest_labels,
                    ..
                }),
            instrs,
        })) = blocks.get(&id)
        {
            if instrs.is_empty() {
                return Self::get_next_real_node(
                    blocks,
                    *labels_map.get(dest_labels.get(0).unwrap()).unwrap(),
                    labels_map,
                    starting_id.or(Some(id)),
                );
            }
        }
        Some(id)
    }

    /// Remove unreachable nodes from the CFG
    /// Unreachable nodes occur when we splice out jumps when
    /// constructing the cfg. Prior to cleaning, the
    /// adjacency list may contain such jumps that have
    /// been spliced out. Cleaning will remove these jumps
    fn clean(mut self) -> Self {
        let mut keeps = vec![];
        let mut q = VecDeque::new();
        q.push_back(CFG_START_ID);
        while !q.is_empty() {
            let reachable = q.pop_front().unwrap();
            if keeps.contains(&reachable) {
                continue;
            }
            keeps.push(reachable);
            match self.adj_lst.get(&reachable) {
                Some(CfgEdgeTo::Next(next)) => {
                    q.push_back(*next);
                }
                Some(CfgEdgeTo::Branch {
                    true_node,
                    false_node,
                }) => {
                    q.push_back(*true_node);
                    q.push_back(*false_node);
                }
                Some(CfgEdgeTo::Terminal) | None => {}
            }
        }
        self.adj_lst.retain(|id, _| keeps.contains(id));
        self.blocks.retain(|id, _| self.adj_lst.contains_key(id));
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

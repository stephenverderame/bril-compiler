use super::Instruction;
use super::ValueOps;
use std::collections::BTreeSet;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use bril_rs::Argument;
use cfg::analysis::available_copies::AvailableCopies;
use cfg::{
    analysis::{live_vars::LiveVars, AnalysisResult},
    Cfg, CfgNode,
};

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct UndirectedEdge {
    u: String,
    v: String,
}

impl UndirectedEdge {
    fn new(a: &str, b: &str) -> Self {
        if a < b {
            Self {
                u: a.to_string(),
                v: b.to_string(),
            }
        } else {
            Self {
                u: b.to_string(),
                v: a.to_string(),
            }
        }
    }
}

/// An interference and move-related graph
pub struct InterferenceGraph {
    /// Map from variable to set of variables it interferes with
    /// The map is symmetric so that if a interferes with b, b interferes with a
    interference: HashMap<String, HashSet<String>>,
    /// Set of edges connected variables that are move related
    move_related: BTreeSet<UndirectedEdge>,
    /// Map from coalesced variable to variable it was coalesced into
    coalesced_nodes: HashMap<String, String>,
    /// Map from variable name to all variables that have been coalesced into it
    merged_nodes: HashMap<String, HashSet<String>>,
    /// Set of function arguments
    fn_args: HashSet<String>,
}

impl InterferenceGraph {
    /// Creates an interference graph from the given live variables
    pub fn new(
        cfg: &Cfg,
        live_vars: &AnalysisResult<LiveVars>,
        copies: &AnalysisResult<AvailableCopies>,
        fn_args: &[Argument],
    ) -> Self {
        let mut interference: HashMap<_, HashSet<_>> = HashMap::new();
        let mut move_related = BTreeSet::new();
        for blk in cfg.blocks.values() {
            if let CfgNode::Block(blk) = blk {
                for (instr_id, instr) in &blk.instrs {
                    let live_out = &live_vars.in_facts[instr_id].vars;
                    let mut copy = None;
                    if let Instruction::Value {
                        op: ValueOps::Id,
                        args,
                        dest,
                        ..
                    } = instr
                    {
                        if !interference
                            .get(dest)
                            .map_or(false, |interferers| {
                                interferers.contains(&args[0])
                            })
                            && &args[0] != dest
                        {
                            // add more related if not interfering along another path
                            move_related
                                .insert(UndirectedEdge::new(&args[0], dest));
                        }
                        copy = Some(args[0].clone());
                    }
                    if let Some(dest) = instr.get_dest() {
                        for live_var in live_out.iter().filter(|&x| {
                            x != &dest
                                && copy.as_ref().map(|y| y != x).unwrap_or(true)
                        }) {
                            if copies.in_facts[instr_id]
                                .get_copy(live_var)
                                .unwrap_or(live_var)
                                == copies.in_facts[instr_id]
                                    .get_copy(&dest)
                                    .unwrap_or(&dest)
                            {
                                continue;
                            }
                            interference
                                .entry(live_var.clone())
                                .or_default()
                                .insert(dest.clone());
                            interference
                                .entry(dest.clone())
                                .or_default()
                                .insert(live_var.clone());
                            move_related
                                .remove(&UndirectedEdge::new(live_var, &dest));
                        }
                    }
                }
            }
        }
        Self {
            interference,
            move_related,
            coalesced_nodes: HashMap::new(),
            merged_nodes: HashMap::new(),
            fn_args: fn_args.iter().map(|x| x.name.clone()).collect(),
        }
    }

    /// Coalesces `b` into `a`
    /// This will update the interference graph such that `b` is no longer in the graph
    /// and `a` interferes with all variables that `b` interfered with
    /// Likewise, this will update the move related graph such that `b` is no longer in the graph
    /// and `a` is move related to all non-interfering variables that `b` was
    /// move related to
    /// Requires that `a` is not a function argument
    fn coalesce(mut self, a: &str, b: &str) -> Self {
        self.coalesced_nodes.insert(b.to_string(), a.to_string());
        let interfere_b = self.interference.remove(b).unwrap_or_default();
        let merged_b = self.merged_nodes.remove(b).unwrap_or_default();
        self.merged_nodes
            .entry(a.to_string())
            .or_default()
            .extend(merged_b);
        self.merged_nodes.get_mut(a).unwrap().insert(b.to_string());
        for new_interfere in &interfere_b {
            self.move_related
                .remove(&UndirectedEdge::new(new_interfere, a));
        }
        self.interference
            .entry(a.to_string())
            .or_default()
            .extend(interfere_b);
        for v in self.interference.values_mut() {
            if v.contains(b) {
                v.remove(b);
                v.insert(a.to_string());
            }
        }
        let mut remove_move_related = HashSet::new();
        let mut add_move_related = HashSet::new();
        for edge @ UndirectedEdge { u, v } in &self.move_related {
            if u == b && !self.interference[a].contains(v) {
                remove_move_related.insert(edge.clone());
                add_move_related.insert(UndirectedEdge::new(a, v));
            } else if v == b && !self.interference[a].contains(u) {
                remove_move_related.insert(edge.clone());
                add_move_related.insert(UndirectedEdge::new(a, u));
            } else if v == b || u == b {
                remove_move_related.insert(edge.clone());
            }
        }
        self.move_related
            .retain(|x| !remove_move_related.contains(x));
        self.move_related.extend(add_move_related);
        self
    }

    /// Coalesces all move related nodes that we can
    pub fn coalesce_all(mut self) -> Self {
        while !self.move_related.is_empty() {
            let e = self.move_related.iter().next().unwrap().clone();
            self.move_related.remove(&e);
            // always coalesce into a function argument
            if self.fn_args.contains(&e.v) {
                assert!(!self.fn_args.contains(&e.u));
                self = self.coalesce(&e.v, &e.u);
            } else {
                self = self.coalesce(&e.u, &e.v);
            }
        }
        self
    }

    /// Returns the new variable name for `name`
    /// If `name` was not coalesced, returns `name`
    pub fn get_canonical_name(&self, name: &str) -> String {
        let mut name_opt = Some(name.to_string());
        let mut last_name = name.to_string();
        while let Some(name) = name_opt {
            last_name = name.to_string();
            name_opt = self.coalesced_nodes.get(&name).cloned();
        }
        last_name
    }
}

impl std::fmt::Debug for InterferenceGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ids = HashMap::new();
        writeln!(f, "graph interference {{")?;
        for (id, n) in self.interference.keys().enumerate() {
            let mut str = n.to_string();
            for merged in self.merged_nodes.get(n).unwrap_or(&HashSet::new()) {
                str.push_str(&format!("/{merged}"));
            }
            writeln!(f, "\tn{id} [label=\"{}\", shape=\"ellipse\"];", str)?;
            ids.insert(n, id);
        }
        let mut displayed_edges = HashSet::new();
        for (k, v) in &self.interference {
            let k_id = ids[k];
            for v in v {
                let v_id = ids[v];
                if !displayed_edges.contains(&UndirectedEdge::new(k, v)) {
                    writeln!(f, "\tn{k_id} -- n{v_id};")?;
                    displayed_edges.insert(UndirectedEdge::new(k, v));
                }
            }
        }
        let mut id = self.interference.len();
        for UndirectedEdge { u, v } in &self.move_related {
            if !self.interference.contains_key(u) {
                writeln!(f, "\tn{id} [label=\"{}\", shape=\"ellipse\"];", u)?;
                ids.insert(u, id);
                id += 1;
            }
            if !self.interference.contains_key(v) {
                writeln!(f, "\tn{id} [label=\"{}\", shape=\"ellipse\"];", v)?;
                ids.insert(v, id);
                id += 1;
            }
            let u_id = ids[u];
            let v_id = ids[v];
            writeln!(f, "\tn{u_id} -- n{v_id} [style=dashed];")?;
        }
        writeln!(f, "}}")
    }
}

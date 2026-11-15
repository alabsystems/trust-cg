// Author: Andrew Yates | Copyright 2026 | License: Apache-2.0

//! Sparse counts of actual graph entries for required EH handler pairs.
//! This is graph metadata observation, not EH acceptance or proof authority.

use super::{BlockId, EhCallSiteEntry, MachBlock};
use crate::fast_hash::FxHashMap;

/// Edge-entry counts for only the `(call block, landing pad)` pairs named by
/// handler rows. Observe each actual layout block once: construction and the
/// traversal use expected O(handler rows + blocks + graph entries) hash work,
/// with storage only
/// proportional to distinct required handler pairs, not every graph edge.
#[derive(Debug, Default)]
pub struct EhEdgeCensus {
    counts: FxHashMap<(BlockId, BlockId), (usize, usize)>,
}

impl EhEdgeCensus {
    /// Index required semantic handler pairs. No-handler/filler rows are not
    /// indexed. Duplicate rows request the same pair; their validity remains
    /// the consumer's responsibility, separate from graph-entry counting.
    pub fn for_handlers(sites: &[EhCallSiteEntry]) -> Self {
        let mut census = Self::default();
        for site in sites {
            if let Some(pad) = site.landing_pad_block {
                census
                    .counts
                    .entry((site.call_block, pad))
                    .or_insert((0, 0));
            }
        }
        census
    }

    /// Count every matching stored successor/predecessor entry. Duplicated
    /// edges and repeated observations are deliberately not deduplicated, so
    /// they cannot repair an invalid graph into reciprocal singleton counts.
    pub fn observe_block(&mut self, block_id: BlockId, block: &MachBlock) {
        if self.counts.is_empty() {
            return;
        }
        for &successor in &block.succs {
            if let Some((outgoing, _)) = self.counts.get_mut(&(block_id, successor)) {
                *outgoing = outgoing.saturating_add(1);
            }
        }
        for &predecessor in &block.preds {
            if let Some((_, incoming)) = self.counts.get_mut(&(predecessor, block_id)) {
                *incoming = incoming.saturating_add(1);
            }
        }
    }

    /// Return `(successor entries, predecessor entries)` for a required pair;
    /// an unindexed pair has no observed evidence and returns `(0, 0)`.
    pub fn counts(&self, from: BlockId, to: BlockId) -> (usize, usize) {
        self.counts.get(&(from, to)).copied().unwrap_or((0, 0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn handler(from: u32, to: u32) -> EhCallSiteEntry {
        EhCallSiteEntry {
            call_block: BlockId(from),
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(BlockId(to)),
        }
    }

    #[test]
    fn many_actual_callers_share_one_pad_without_an_all_edges_cache() {
        const CALLERS: u32 = 1024;
        let pad_id = BlockId(CALLERS);
        let handlers: Vec<_> = (0..CALLERS).map(|from| handler(from, CALLERS)).collect();
        let mut census = EhEdgeCensus::for_handlers(&handlers);
        let mut pad = MachBlock::new();
        for from in 0..CALLERS {
            let mut caller = MachBlock::new();
            caller.succs = vec![pad_id, BlockId(CALLERS + 1)];
            pad.preds.push(BlockId(from));
            census.observe_block(BlockId(from), &caller);
        }
        census.observe_block(pad_id, &pad);
        assert_eq!(census.counts.len(), CALLERS as usize);
        for from in 0..CALLERS {
            assert_eq!(census.counts(BlockId(from), pad_id), (1, 1));
            assert_eq!(census.counts(BlockId(from), BlockId(CALLERS + 1)), (0, 0));
        }
    }

    #[test]
    fn missing_duplicate_and_one_sided_entries_keep_exact_counts() {
        for (successors, predecessors, expected) in [
            (0, 0, (0, 0)),
            (1, 0, (1, 0)),
            (0, 1, (0, 1)),
            (1, 1, (1, 1)),
            (2, 1, (2, 1)),
            (1, 2, (1, 2)),
        ] {
            let mut census = EhEdgeCensus::for_handlers(&[handler(0, 1)]);
            let mut caller = MachBlock::new();
            caller.succs = vec![BlockId(1); successors];
            let mut pad = MachBlock::new();
            pad.preds = vec![BlockId(0); predecessors];
            census.observe_block(BlockId(0), &caller);
            census.observe_block(BlockId(1), &pad);
            assert_eq!(census.counts(BlockId(0), BlockId(1)), expected);
        }
    }

    #[test]
    fn repeated_observations_do_not_hide_duplicate_graph_evidence() {
        let mut census = EhEdgeCensus::for_handlers(&[handler(0, 1)]);
        let mut caller = MachBlock::new();
        caller.succs.push(BlockId(1));
        let mut pad = MachBlock::new();
        pad.preds.push(BlockId(0));
        census.observe_block(BlockId(0), &caller);
        census.observe_block(BlockId(1), &pad);
        assert_eq!(census.counts(BlockId(0), BlockId(1)), (1, 1));
        census.observe_block(BlockId(0), &caller);
        assert_eq!(census.counts(BlockId(0), BlockId(1)), (2, 1));
        census.observe_block(BlockId(1), &pad);
        assert_eq!(census.counts(BlockId(0), BlockId(1)), (2, 2));
    }

    #[test]
    fn fillers_and_duplicate_metadata_rows_do_not_invent_graph_entries() {
        let mut filler = handler(2, 3);
        filler.landing_pad_block = None;
        let mut census = EhEdgeCensus::for_handlers(&[handler(0, 1), handler(0, 1), filler]);
        let mut caller = MachBlock::new();
        caller.succs = vec![BlockId(1), BlockId(3)];
        let mut pad = MachBlock::new();
        pad.preds.push(BlockId(0));
        census.observe_block(BlockId(0), &caller);
        census.observe_block(BlockId(1), &pad);
        assert_eq!(census.counts.len(), 1);
        assert_eq!(census.counts(BlockId(0), BlockId(1)), (1, 1));
        assert_eq!(census.counts(BlockId(2), BlockId(3)), (0, 0));
    }
}

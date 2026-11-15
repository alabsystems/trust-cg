// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Private names for source regions' cut edges and their machine walks.

use super::{Block, CutEdge, E, HashMap, MachineState, Walked};

/// Source cut edges keyed by their (region block, destination loop header).
pub(super) type RegionCutEdges = HashMap<(Block, Block), CutEdge>;

/// Cut-edge machine states under psABI and optional clean-bool conventions.
pub(super) type ConventionCutExitStates =
    HashMap<(Block, Block), (MachineState, Option<MachineState>)>;

/// The walks of one DAG under one caller convention ([`super::walk_region`]): each
/// block's walk, each edge's `jcc` literals and (slice 12) the machine state
/// at the end of each cut edge's walk.
pub(super) type RegionWalk = (
    HashMap<Block, Walked>,
    HashMap<(Block, Block), Vec<E>>,
    HashMap<(Block, Block), MachineState>,
);

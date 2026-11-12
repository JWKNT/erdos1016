import Erdos1016.ExactMaximumSupport.Stable
import Erdos1016.ExactMaximumSupport.SecondOrderLower

/-!
This audit checks the support results and every final case input.
The exact maximum and sharp second-order endpoints are checked separately in
`audits/ExactMaximumEndpoints.lean`.
-/

#print axioms Erdos1016.ExactMaximumSupport.CubicReduction.cubicReductionStatement
#print axioms Erdos1016.ExactMaximum.lowerBoundStatement
#print axioms Erdos1016.ExactMaximumSupport.maxCycles_secondOrder_lower
#print axioms Erdos1016.ExactMaximumSupport.secondOrder_scale_isBigO_maxCycles_excess
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.Packing.exists_cutoff
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.Packing.exists_finset_cutoff
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth.exists_raising_cutoff
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.ChainContradiction.exists_constant
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.RetainedChainContradiction.bound_of_mass
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingContradiction.bound_of_budgets
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget.exists_rank_threshold
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.ForestProbability.exists_cutoff
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces.exists_constants
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings.exists_strings
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingProduct.forest_density_le_cut_product
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingIndependence.average_evaluation_product
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpaces.relevant_terminalBranch_card
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient.region_forest_le_mark_product
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient.lift_cut_card_le
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingRegionRank.card_le_induced_cycleRank
#print axioms Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringLift.exists_length_cutoff
#print axioms Erdos1016.ExactMaximumSupport.poleLayerBoundStatement
#print axioms Erdos1016.ExactMaximumSupport.PoleCyclePacking.poleCyclePackingStatement
#print axioms Erdos1016.ExactMaximumSupport.PathForestProbability.affineForestProbability_eq_path_density
#print axioms Erdos1016.ExactMaximumSupport.PathExteriorProbability.restrictedForestProbability_ge_501
#print axioms Erdos1016.ExactMaximumSupport.VertexRankDeletion.rank_region_le_twice_card_of_diff_forest
#print axioms Erdos1016.ExactMaximumSupport.CycleLayerSpan.twice_level_difference_le_support
#print axioms Erdos1016.ExactMaximumSupport.ThinIntervalBoundary.cut_region_le_width
#print axioms Erdos1016.ExactMaximumSupport.FewCyclesSums.double_sum_two_rpow_half_le
#print axioms Erdos1016.ExactMaximumSupport.FewCyclesSums.sum_two_rpow_half_ranks_le
#print axioms Erdos1016.ExactMaximumSupport.PoleOutsideRank.exists_physical_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleOutsideRank.poleOutsideRankStatement
#print axioms Erdos1016.ExactMaximumSupport.NetworkFourLayers.exists_cycle_of_four_distance_layers
#print axioms Erdos1016.ExactMaximumSupport.fourThinLayersStatement
#print axioms Erdos1016.ExactMaximumSupport.ThinLayerShortCycle.exists_cycle_of_few_bad_layers
#print axioms Erdos1016.ExactMaximumSupport.ThinLayerShortCycle.exists_cycle_of_rank_budget
#print axioms Erdos1016.ExactMaximumSupport.thinLayersStatement
#print axioms Erdos1016.ExactMaximumSupport.LayerCountLedger.exceptional_card_le
#print axioms Erdos1016.ExactMaximumSupport.LayerCountLedger.nonordinary_card_le
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathMarker.eq_of_same_layer
#print axioms Erdos1016.ExactMaximumSupport.PolePathRank.bridgeless_path_rank
#print axioms Erdos1016.ExactMaximumSupport.NetworkGeodesic.exists_shortest_path
#print axioms Erdos1016.ExactMaximumSupport.PoleParallelCount.card_parallel_outside_le_twice_rank
#print axioms Erdos1016.ExactMaximumSupport.BridgelessLayers.internal_layer_card_ge_two
#print axioms Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut.hasCyclicCutLE_four_of_rank_ge_nine
#print axioms Erdos1016.ExactMaximumSupport.NetworkShortCycleCut.cycle_support_cyclic_cut
#print axioms Erdos1016.ExactMaximumSupport.NetworkShortCycleCut.four_lt_size_of_cyclic_cut_lower_bound
#print axioms Erdos1016.ExactMaximumSupport.InterfaceMatchings.matching_count_le_two
#print axioms Erdos1016.ExactMaximumSupport.InterfaceMatchings.adjacent_matching_sum_le_three
#print axioms Erdos1016.ExactMaximumSupport.MatchingProduct.prod_filter_interior_le_rpow
#print axioms Erdos1016.ExactMaximumSupport.MatchingProduct.prod_filter_range_le
#print axioms Erdos1016.ExactMaximumSupport.OrdinaryLayerOrder.twice_rank_le_inner_layers_add_bad
#print axioms Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle.exists_avoiding_constant
#print axioms Erdos1016.ExactMaximumSupport.NatFewCyclesSums.double_sum_two_pow_half_le
#print axioms Erdos1016.ExactMaximumSupport.NatFewCyclesSums.twelve_fails_at_nine

#check Erdos1016.ExactMaximum.exactMaximumStatement_of_four
#check Erdos1016.ExactMaximumSupport.sharpSecondOrder_rpow_of_exactMaximum

/-- The completed large-girth endpoint has the full graph hypotheses and conclusion. -/
example : ∃ D R : ℕ, ∀ M : Erdos1016.FiniteMultiGraph,
    M.toSimpleGraph.Connected → (∀ v,M.degree v=3) → ¬ M.HasLoop →
    R≤M.cycleRank → ¬ M.HasCyclicCutLE 4 → ¬ M.HasCycleShorterThan D →
    M.numCycles<2^(M.cycleRank-1) :=
  Erdos1016.ExactMaximumSupport.LargeGirth.largeGirthStatement

/-- The four-layer endpoint preserves actual physical cycles and their vertex support. -/
example : ∀ (V E : Type) [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → ∀ j : ℕ,
    N.IsThinLayer s t j → N.IsThinLayer s t (j + 1) →
    N.IsThinLayer s t (j + 2) → N.IsThinLayer s t (j + 3) →
    ∃ Z : N.Word, N.IsCycleWord Z ∧ Erdos1016.BoundaryTrace.Network.size Z ≤ 4 ∧
      ∀ v, 0 < N.deg Z v → j ≤ N.graph.dist s v ∧ N.graph.dist s v ≤ j + 3 :=
  Erdos1016.ExactMaximumSupport.fourThinLayersStatement

/-- The complete thin-layer theorem has no supplied rank, path, or counting certificate. -/
example : ∃ C : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V),
    N.IsBridgelessTwoPole s t →
    501 * 2 ^ Erdos1016.BoundaryDecay.networkRank N ≤ 1000 * N.numPaths s t →
    (∀ v, N.graph.dist s v ≤ Erdos1016.BoundaryDecay.networkRank N + C) ∧
      Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C :=
  Erdos1016.ExactMaximumSupport.thinLayersStatement

/-- The avoidance statement quantifies over actual forbidden sets and actual physical cycle words. -/
example : ∃ C : ℕ, ∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V),
    N.IsBridgelessTwoPole s t →
    501 * 2 ^ Erdos1016.BoundaryDecay.networkRank N ≤ 1000 * N.numPaths s t →
    ∀ X : Finset V, X.card ≤ k → 5 * C + 4 * k + 5 ≤ Erdos1016.BoundaryDecay.networkRank N →
    ∃ z : N.Word, N.IsCycleWord z ∧ Erdos1016.BoundaryTrace.Network.size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → v ∉ X :=
  Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle.exists_avoiding_constant

#print axioms Erdos1016.ExactMaximumSupport.CycleTwoStrands.twoStrandsStatement
#print axioms Erdos1016.ExactMaximumSupport.LayerMatchingCount.card_layerMatching
#print axioms Erdos1016.ExactMaximumSupport.layerMatchingStatement
#print axioms Erdos1016.ExactMaximumSupport.PoleFewCycles.bridgelessFewCyclesStatement
#print axioms Erdos1016.ExactMaximumSupport.PoleFewCycles.twoPoleFewCyclesStatement
#print axioms Erdos1016.ExactMaximumSupport.PoleFewCycles.fewCyclesStatement
#print axioms Erdos1016.ExactMaximumSupport.PoleFewCycles.threeCutStatement

/-- The few-cycles endpoint ranges over actual weak poles and distinct degree-two ports. -/
example : ∃ K : ℕ, 1 ≤ K ∧ ∀ (V E : Type) [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E), N.IsWeakPole → ∀ s t : V,
    N.IsPort s → N.IsPort t → s ≠ t →
    501 * 2 ^ Erdos1016.BoundaryDecay.networkRank N ≤ 1000 * N.numPaths s t →
    N.numCycles ^ 2 ≤ K * 2 ^ Erdos1016.BoundaryDecay.networkRank N :=
  Erdos1016.ExactMaximumSupport.PoleFewCycles.fewCyclesStatement

#print axioms Erdos1016.ExactMaximumSupport.PoleMarginProbability.exists_path_layer_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginProbability.restricted_forest_probability
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginProbability.exists_packing_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank.exists_exterior_rank_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank.exists_physical_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank.exists_network_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginLayers.exists_thin_layer_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginLayers.exists_avoiding_constant
#print axioms Erdos1016.ExactMaximumSupport.RingUpperArithmetic.cycle_bound_of_doubled
#print axioms Erdos1016.ExactMaximumSupport.RingUpperArithmetic.singleton_cycle_bound
#print axioms Erdos1016.ExactMaximumSupport.LadderPermutation.fixed_or_adjacent_exchange
#print axioms Erdos1016.ExactMaximumSupport.LadderPermutation.sum_tileWeights
#print axioms Erdos1016.ExactMaximumSupport.PolePortReduction.exists_two_pole
#print axioms Erdos1016.ExactMaximumSupport.PoleGapReduction.gap_of_two_pole
#print axioms Erdos1016.ExactMaximumSupport.PoleGapReduction.gapStatement_of_bridgeless

#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.interface_quarter
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.interface_gap
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.rung_gap
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.square_eighth
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.square_five_eighths
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.sum_gap
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortArithmetic.adjacent_port_quarter
#print axioms Erdos1016.ExactMaximumSupport.PoleAdjacentGap.path_eq_unit_of_selected
#print axioms Erdos1016.ExactMaximumSupport.PoleAdjacentGap.numPaths_le_avoiding_add_one
#print axioms Erdos1016.ExactMaximumSupport.PoleAdjacentGap.two_mul_avoiding_paths_le
#print axioms Erdos1016.ExactMaximumSupport.PoleAdjacentGap.two_mul_numPaths_le
#print axioms Erdos1016.ExactMaximumSupport.PoleAdjacentGap.adjacent_port_quarter
#print axioms Erdos1016.ExactMaximumSupport.PoleSmallRank.rank_pos
#print axioms Erdos1016.ExactMaximumSupport.PoleSmallRank.vertex_eq_port_of_rank_one
#print axioms Erdos1016.ExactMaximumSupport.PoleSmallRank.full_of_rank_one
#print axioms Erdos1016.ExactMaximumSupport.PoleGapReduction.gap_of_two_pole_bounded
#print axioms Erdos1016.ExactMaximumSupport.PoleGapReduction.gap_of_rank_bound
#print axioms Erdos1016.ExactMaximumSupport.PoleGapInduction.gapStatement_of_thirdPort
#print axioms Erdos1016.ExactMaximumSupport.PoleTerminalDeletion.exists_three_pole_deletion
#print axioms Erdos1016.ExactMaximumSupport.PoleTwoPaths.exists_two_paths
#print axioms Erdos1016.ExactMaximumSupport.NetworkIso.numCycles_eq
#print axioms Erdos1016.ExactMaximumSupport.NetworkIso.numPaths_eq
#print axioms Erdos1016.ExactMaximumSupport.NetworkIso.networkRank_eq
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.chain_rank
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.capped_rank
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.ring_rank
#print axioms Erdos1016.ExactMaximumSupport.PoleCyclicShore.exists_avoiding_constant
#print axioms Erdos1016.ExactMaximumSupport.PoleCyclicShore.exists_cubic_shore_constant

/-- The gap remains conditional on the exact third-port statement. -/
example (h : Erdos1016.ExactMaximumSupport.PoleGapInduction.ThirdPortStatement) :
    Erdos1016.ExactMaximum.GapStatement :=
  Erdos1016.ExactMaximumSupport.PoleGapInduction.gapStatement_of_thirdPort h

/-- The two-pole cyclic shore contains only actual degree-three vertices. -/
example : ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V),
    N.IsBridgelessTwoPole s t →
    (1/2 + ε) * (2:ℝ)^Erdos1016.BoundaryDecay.networkRank N ≤ N.numPaths s t →
    B ≤ Erdos1016.BoundaryDecay.networkRank N →
    ∃ S : V → Prop, N.IsCyclicCut S ∧ N.cutSize S ≤ 4 ∧
      ∀ v, S v → N.deg (fun _ => 1) v = 3 :=
  Erdos1016.ExactMaximumSupport.PoleCyclicShore.exists_cubic_shore_constant

#print axioms Erdos1016.ExactMaximumSupport.LadderTileOrder.ordered_prefix_weights
#print axioms Erdos1016.ExactMaximumSupport.LadderTileOrder.ordered_total_weight
#print axioms Erdos1016.ExactMaximumSupport.LadderTileOrder.consecutive_starts
#print axioms Erdos1016.ExactMaximumSupport.LadderTileOrder.kind_weight
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.exists_order
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.vertex_support
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.innerEquiv
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.inner_card
#print axioms Erdos1016.ExactMaximumSupport.FullPairMatching.exists_full_pair_matching
#print axioms Erdos1016.ExactMaximumSupport.FullPairRailEquiv.matchingEquiv
#print axioms Erdos1016.ExactMaximumSupport.FullPairRailEquiv.matchingEdgeEquiv
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction.thirdPortStatement_of_bridgeless
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore.exists_connected_marked_suppression
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.odd_cycles_card_le
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.interface_parity
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.even_or_odd_interfaces
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.zero_interface_cycles_card_le
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.fixed_interface_cycles_card_le

/-- Bridges are discharged; the bridgeless third-port count is still an explicit premise. -/
example (h : Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction.BridgelessThirdPortStatement) :
    Erdos1016.ExactMaximum.GapStatement :=
  Erdos1016.ExactMaximumSupport.PoleGapInduction.gapStatement_of_thirdPort
    (Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction.thirdPortStatement_of_bridgeless h)

/-- Every actual path has an injective physical-label and vertex order. -/
example {V E : Type} [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V) (P : N.Word)
    (hP : N.IsPathWord s t P) :
    Nonempty (Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order N s t P) :=
  Erdos1016.ExactMaximumSupport.NetworkPathOrder.exists_order N hP

#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.segment_isPath
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.segment_vertex_support
#print axioms Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order.segment_vertexDisjoint
#print axioms Erdos1016.ExactMaximumSupport.FullPairPermutation.permutation
#print axioms Erdos1016.ExactMaximumSupport.FullPairAvoidance.avoids_ladder_patterns
#print axioms Erdos1016.ExactMaximumSupport.FullPairOrderedRails.exists_ordered_rails
#print axioms Erdos1016.ExactMaximumSupport.FullPairLadderIso.exists_ladder_iso
#print axioms Erdos1016.ExactMaximumSupport.LadderTileCoordinates.vertexEquiv
#print axioms Erdos1016.ExactMaximumSupport.LadderTileSequence.total_weight
#print axioms Erdos1016.ExactMaximumSupport.LadderTileEdges.edgeMap_joins
#print axioms Erdos1016.ExactMaximumSupport.LadderTileIso.exists_capped_iso
#print axioms Erdos1016.ExactMaximumSupport.FullPairCappedLadder.exists_capped_ladder
#print axioms Erdos1016.ExactMaximumSupport.FullPairCappedLadder.rank_one_or_capped
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortDeletedEdge.numPaths_restored
#print axioms Erdos1016.ExactMaximumSupport.NetworkIso.deleteEdge
#print axioms Erdos1016.ExactMaximumSupport.NetworkPositiveSubnetwork.numPaths_positive_deleteEdge
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortRestoredCore.numPaths_restored_in_model
#print axioms Erdos1016.ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.partial_even_cycles_card_le
#print axioms Erdos1016.ExactMaximumSupport.RingOmega.partialSum_bound
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.numCycles_le_sector_ledger
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.full_interface_cycles_card_le_half
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.ring_doubled_cycle_bound
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.ring_no_square_cycle_bound
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.ring_numCycles_le_horakKim
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.ring_numCycles_le_horakKim_rank

/-- The actual full-pole classification has no supplied decomposition premise. -/
example {V E : Type} [Fintype V] [Fintype E]
    (N : Erdos1016.BoundaryTrace.Network V E) (s t : V)
    (hN : N.IsBridgelessTwoPole s t) (hf : N.IsFullPair s t)
    (hr : 2 ≤ Erdos1016.BoundaryDecay.networkRank N) :
    ∃ k : ℕ, ∃ T : Fin (k+1) → Erdos1016.ExactMaximumSupport.MixedTiles.Kind,
      ∃ I : Erdos1016.ExactMaximumSupport.NetworkIso
        (Erdos1016.ExactMaximumSupport.MixedTiles.capped T) N,
        I.vertices (Sum.inr false)=s ∧ I.vertices (Sum.inr true)=t ∧
        Erdos1016.ExactMaximumSupport.MixedTiles.weight T+1=
          Erdos1016.BoundaryDecay.networkRank N :=
  Erdos1016.ExactMaximumSupport.FullPairCappedLadder.exists_capped_ladder N hN hf hr

/-- The physical ring count uses the network's actual cycle rank. -/
example {k : ℕ} (T : Fin (k+1) → Erdos1016.ExactMaximumSupport.MixedTiles.Kind)
    (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (hW : 7 ≤ Erdos1016.ExactMaximumSupport.MixedTiles.weight T) :
    (Erdos1016.ExactMaximumSupport.MixedTiles.ring T hk twist).numCycles ≤
      Erdos1016.ExactMaximum.horakKim (Erdos1016.BoundaryDecay.networkRank
        (Erdos1016.ExactMaximumSupport.MixedTiles.ring T hk twist)) :=
  Erdos1016.ExactMaximumSupport.MixedTiles.ring_numCycles_le_horakKim_rank T hk twist hW

example : Erdos1016.ExactMaximum.FourCutArithmeticStatement :=
  Erdos1016.ExactMaximumSupport.FourCutArithmeticProof.fourCutArithmeticStatement

#print axioms Erdos1016.ExactMaximumSupport.FourPoleChain.isChain
#print axioms Erdos1016.ExactMaximumSupport.FourPoleBridgeLift.side_bridgeless
#print axioms Erdos1016.ExactMaximumSupport.FourCutGluing.exists_glued
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.gluedRingIso
#print axioms Erdos1016.ExactMaximumSupport.MixedTiles.glued_numCycles_le_horakKim_rank
#print axioms Erdos1016.ExactMaximumSupport.ringCaseStatement
#print axioms Erdos1016.ExactMaximumSupport.MarkedPathCount.count_iso
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction.small_rank
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction.numPaths_eq_count
#print axioms Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction.gapStatement_of_capped
#print axioms Erdos1016.ExactMaximumSupport.CyclicShoreMargin.strict_half
#print axioms Erdos1016.ExactMaximumSupport.CyclicShoreMargin.real_margin
#print axioms Erdos1016.ExactMaximumSupport.CyclicShoreMargin.left_factor
#print axioms Erdos1016.ExactMaximumSupport.CyclicShoreMargin.right_factor
#print axioms Erdos1016.ExactMaximumSupport.NetworkInducedCut.cutSize_lift
#print axioms Erdos1016.ExactMaximumSupport.NetworkInducedCut.cyclic_lift
#print axioms Erdos1016.ExactMaximumSupport.NetworkInducedCut.deg_lift
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.ExtendedShore.cubic
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.whole_positive
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.weak_bridgeless_constant
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.bridgeless_constant
#print axioms Erdos1016.ExactMaximumSupport.PoleMarginBridge.exists_split

/-- The unrestricted full-cross ring case is unconditional. -/
example : Erdos1016.ExactMaximum.RingCaseStatement :=
  Erdos1016.ExactMaximumSupport.ringCaseStatement

/-- The remaining gap input is the actual capped-model marked-edge count. -/
example (h : Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction.CappedMarkedCountStatement) :
    Erdos1016.ExactMaximum.GapStatement :=
  Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction.gapStatement_of_capped h

#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.cutSize_lift_bridge
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.lift_left
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.extended_constant
#print axioms Erdos1016.ExactMaximumSupport.PoleExtendedShore.marked_two_pole_constant
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.within_grow_inside
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.cycle_pos_inside
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.cyclic_lift
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.crosses_iff
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.cutSize_eq
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.cubic_lift
#print axioms Erdos1016.ExactMaximumSupport.SuppressedCyclicShore.lift
#print axioms Erdos1016.ExactMaximumSupport.PoleTrackedSuppression.extraPorts_suppress
#print axioms Erdos1016.ExactMaximumSupport.PoleTrackedSuppression.extraPorts_card
#print axioms Erdos1016.ExactMaximumSupport.PoleTrackedSuppression.exists_thread
#print axioms Erdos1016.ExactMaximumSupport.PoleTrackedSuppression.exists_reduction
#print axioms Erdos1016.ExactMaximumSupport.PoleTrackedSuppression.exists_marked_two_pole
#print axioms Erdos1016.ExactMaximumSupport.cyclicShoreStatement

/-- The cyclic-shore input is unconditional on the original network model. -/
example : Erdos1016.ExactMaximum.CyclicShoreStatement :=
  Erdos1016.ExactMaximumSupport.cyclicShoreStatement

#print axioms Erdos1016.ExactMaximumSupport.shortCycleStatement
#print axioms Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts.endpoints
#print axioms Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts.middle_left
#print axioms Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts.middle_right

/-- The bounded-girth case is unconditional. -/
example : Erdos1016.ExactMaximum.ShortCycleStatement :=
  Erdos1016.ExactMaximumSupport.shortCycleStatement

#print axioms Erdos1016.ExactMaximumSupport.MixedCappedCapCounts.left_cap_count
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedRightCap.right_cap_quarter
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedInterfaceCounts.interface_quarter
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedStem.rank
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedStem.numPaths_le
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedRungCounts.rung_gap
#print axioms Erdos1016.ExactMaximumSupport.MarkedSquareLocalCounts.route_sum
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry.retained_iff
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry.thread
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry.local_route_sum
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedSquareCounts.square_eighth
#print axioms Erdos1016.ExactMaximumSupport.MixedCappedMarkedCounts.cappedMarkedCountStatement
#print axioms Erdos1016.ExactMaximumSupport.gapStatement

/-- The gap input has no remaining mathematical premise. -/
example : Erdos1016.ExactMaximum.GapStatement :=
  Erdos1016.ExactMaximumSupport.gapStatement

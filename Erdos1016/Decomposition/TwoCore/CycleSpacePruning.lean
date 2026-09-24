import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.Decomposition.TwoCore.PhysicalCore
import Erdos1016.Probability.Conditional.CycleExtensionProbability

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CoreCycleSpace

open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideVertex S) :=
  Network.Shore.outsideVertexFintype G.traceNetwork S
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideEdge G.traceNetwork S) :=
  Network.Shore.outsideEdgeFintype G.traceNetwork S

/-- The vertices used by an even word have minimum degree two in the
ambient induced graph. This includes disconnected words. -/
theorem usedVertices_minTwo (G : PhysicalGraph) (x : G.CycleSpace) :
    MinTwo G.toSimpleGraph (G.usedVertices x.1) := by
  intro v hv
  have hpos : 0 < G.selectedDegree x.1 v := by
    apply Finset.card_pos.mpr
    obtain ⟨e, he, hi⟩ := (mem_usedVertices x.1 _).mp hv
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hi⟩⟩
  have heven : 2 ∣ G.selectedDegree x.1 v := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [← boundary_eq_selectedDegree_cast]
    exact congrFun x.2 v
  have htwo : 2 ≤ G.selectedDegree x.1 v := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hsub : (G.selectedGraph x.1).neighborSet v ⊆
      (↑((G.usedVertices x.1).filter fun w => G.toSimpleGraph.Adj v w) : Set G.Vertex) := by
    intro w hw
    obtain ⟨e, he, hends⟩ := hw
    have hwused : w ∈ G.usedVertices x.1 := by
      apply (mem_usedVertices x.1 _).mpr
      refine ⟨e, he, ?_⟩
      rcases hends with h | h
      · exact Or.inr h.2
      · exact Or.inl h.1
    exact Finset.mem_filter.mpr ⟨hwused, ⟨e, one_ne_zero, hends⟩⟩
  have hcount := Set.ncard_le_ncard hsub
  rw [← selectedDegree_eq_neighbor_ncard, Set.ncard_coe_Finset] at hcount
  exact htwo.trans hcount

/-- An even word vanishing at a deleted region is supported on the full
two-core of its complement. -/
theorem usedVertices_subset_complement_core
    (G : PhysicalGraph) (U : Finset G.Vertex) (x : G.CycleSpace)
    (hx : ForcedRegion G.traceNetwork U 0 x.1) :
    G.usedVertices x.1 ⊆ vertices G.toSimpleGraph Uᶜ := by
  apply maximal G.toSimpleGraph Uᶜ _ _ (usedVertices_minTwo G x)
  intro v hv
  apply Finset.mem_compl.mpr
  intro hvU
  obtain ⟨e, he, hi⟩ := (mem_usedVertices x.1 _).mp hv
  apply he
  apply hx e
  rcases hi with h | h
  · exact Or.inl (show G.src e ∈ U from h.symm ▸ hvU)
  · exact Or.inr (show G.dst e ∈ U from h.symm ▸ hvU)

/-- Pruned vertices impose no additional zero constraints on the residual
cycle space, even after an arbitrary further region is prescribed zero. -/
theorem forced_zero_union_iff_core
    (G : PhysicalGraph) (U D : Finset G.Vertex) (x : G.CycleSpace) :
    ForcedRegion G.traceNetwork (U ∪ D) 0 x.1 ↔
      ForcedRegion G.traceNetwork ((vertices G.toSimpleGraph Uᶜ)ᶜ ∪ D) 0 x.1 := by
  constructor
  · intro hx
    have hxU : ForcedRegion G.traceNetwork U 0 x.1 := by
      intro e he
      apply hx e
      rcases he with hs | hd
      · exact Or.inl (Finset.mem_union_left _ hs)
      · exact Or.inr (Finset.mem_union_left _ hd)
    have hcore := usedVertices_subset_complement_core G U x hxU
    intro e he
    by_cases hz : x.1 e = 0
    · exact hz
    have hs := hcore ((mem_usedVertices x.1 _).mpr ⟨e, hz, Or.inl rfl⟩)
    have hd := hcore ((mem_usedVertices x.1 _).mpr ⟨e, hz, Or.inr rfl⟩)
    apply hx e
    rcases he with h | h <;> rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_compl.mp h hs).elim
    · exact Or.inl (Finset.mem_union_right _ h)
    · exact (Finset.mem_compl.mp h hd).elim
    · exact Or.inr (Finset.mem_union_right _ h)
  · intro hx e he
    have hsub : U ⊆ (vertices G.toSimpleGraph Uᶜ)ᶜ := by
      intro v hv
      exact Finset.mem_compl.mpr fun hvc =>
        Finset.mem_compl.mp (vertices_subset G.toSimpleGraph Uᶜ hvc) hv
    apply hx e
    rcases he with h | h <;> rcases Finset.mem_union.mp h with h | h
    · exact Or.inl (Finset.mem_union_left _ (hsub h))
    · exact Or.inl (Finset.mem_union_right _ h)
    · exact Or.inr (Finset.mem_union_left _ (hsub h))
    · exact Or.inr (Finset.mem_union_right _ h)

/-- Equal zero cylinders have equal residual ranks. This uses the exact
finite cylinder count, so it does not need a pruning-order choice. -/
theorem outside_rank_eq_of_forced_zero_iff
    (G : PhysicalGraph) (S T : Finset G.Vertex)
    (h : ∀ x : G.CycleSpace, ForcedRegion G.traceNetwork S 0 x.1 ↔
      ForcedRegion G.traceNetwork T 0 x.1) :
    networkRank (Network.Shore.outside G.traceNetwork S) =
      networkRank (Network.Shore.outside G.traceNetwork T) := by
  classical
  let h' : ∀ x : G.traceNetwork.CycleSpace,
      ForcedRegion G.traceNetwork S 0 x.1 ↔ ForcedRegion G.traceNetwork T 0 x.1 :=
    fun x => h (G.traceCycleEquiv.symm x)
  have hdensity :
      Finite.density (fun x : G.traceNetwork.CycleSpace => ForcedRegion G.traceNetwork S 0 x.1) =
      Finite.density (fun x : G.traceNetwork.CycleSpace => ForcedRegion G.traceNetwork T 0 x.1) := by
    congr 1
    funext x
    exact propext (h' x)
  have hS := forced_region_probability G.traceNetwork S 0
  have hT := forced_region_probability G.traceNetwork T 0
  simp only [ZeroMemClass.coe_zero] at hS hT
  rw [hS, hT] at hdensity
  have heq : (2 : ℝ) ^ networkRank (Network.Shore.outside G.traceNetwork S) =
      (2 : ℝ) ^ networkRank (Network.Shore.outside G.traceNetwork T) :=
    (div_left_inj' (pow_ne_zero (networkRank G.traceNetwork) (by norm_num : (2 : ℝ) ≠ 0))).mp hdensity
  exact (pow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective heq

/-- Both ranks in the conditional probability ratio may be computed in the
full two-core of the original residual graph. -/
theorem outside_rank_union_eq_core
    (G : PhysicalGraph) (U D : Finset G.Vertex) :
    networkRank (Network.Shore.outside G.traceNetwork (U ∪ D)) =
      networkRank (Network.Shore.outside G.traceNetwork
        ((vertices G.toSimpleGraph Uᶜ)ᶜ ∪ D)) :=
  outside_rank_eq_of_forced_zero_iff G _ _ (forced_zero_union_iff_core G U D)

end Erdos1016.Proof.CoreCycleSpace

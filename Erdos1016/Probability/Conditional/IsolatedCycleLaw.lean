import Erdos1016.Cycles.Geometry.IsolatedCycleComplement
import Erdos1016.Probability.Conditional.CycleExtensionProbability

set_option autoImplicit false
noncomputable section
namespace Erdos1016.Proof.IsolatedCycleConditionalLaw

open BoundaryDecay BoundaryTrace SafeCore
open CycleExtensionProbability IsolatedCycleExterior

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (G : PhysicalGraph) : DecidableEq G.CycleWord := Classical.decEq _
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideVertex S) := Network.Shore.outsideVertexFintype G.traceNetwork S
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideEdge G.traceNetwork S) := Network.Shore.outsideEdgeFintype G.traceNetwork S

/-- Ordinary-region separation excludes even a single inter-region edge. -/
theorem crossSize_eq_zero_of_far {G : PhysicalGraph}
    (J U D : Finset G.Vertex) (q : ℕ) (hq : 1 ≤ q)
    (hUJ : U ⊆ J) (hDJ : D ⊆ J)
    (hfar : ∀ (u d : J), u.1 ∈ U → d.1 ∈ D →
      ∀ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u d, q < p.length) :
    crossSize G U D = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro e he
  rcases (mem_crossing G U D e).mp he with h | h
  · have hadj : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Adj
        ⟨G.src e, hUJ h.1⟩ ⟨G.dst e, hDJ h.2⟩ :=
      ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩
    have hh := hfar _ _ h.1 h.2 (.cons hadj .nil)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hh
    omega
  · have hadj : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Adj
        ⟨G.dst e, hUJ h.2⟩ ⟨G.src e, hDJ h.1⟩ :=
      ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩
    have hh := hfar _ _ h.2 h.1 (.cons hadj .nil)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hh
    omega

/-- The exact isolated extension law. The old cycles may have arbitrary
mutual proximity. Only the newly added induced cycle is far from them. -/
theorem conditional_cycle_probability_eq_weight_of_far
    {G : PhysicalGraph} (hG : G.IsConnected)
    (J : Finset G.Vertex) (F : Finset G.CycleWord) (D : G.CycleWord)
    (B : Finset G.Vertex) (q : ℕ) (hq : 1 ≤ q)
    (hFdisj : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hFDdisj : ∀ C ∈ F, Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hFJ : ∀ C ∈ F, Cycle.vertices C ⊆ J) (hDJ : Cycle.vertices D ⊆ J)
    (hFcubic : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hDcubic : ∀ v ∈ Cycle.vertices D, G.degree v = 3)
    (hinduced : Cycle.IsInduced D)
    (hB : B ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ)
    (hsmall : ∀ R ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ, R ≠ B →
      R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ v ∈ R, G.degree v = 3) ∧ R.card + 1 ≤ q ∧
      (∀ e f, e ∈ crossing G R (Cycle.vertices D) → f ∈ crossing G R (Cycle.vertices D) → e = f))
    (hfar : ∀ (u d : J), u.1 ∈ tupleVertices F → d.1 ∈ Cycle.vertices D →
      ∀ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u d, q < p.length) :
    conditionalDensity (tupleEvent F) (Cycle.Event D) = 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length D := by
  let U := tupleVertices F
  have hUJ : U ⊆ J := by
    intro v hv
    obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
    exact hFJ C hC hv
  have hUDisj : Disjoint U (Cycle.vertices D) := by
    apply Finset.disjoint_left.mpr
    intro v hv hd
    obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hFDdisj C hC) hv hd
  have hUcubic : ∀ v ∈ U, G.degree v = 3 := by
    intro v hv
    obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
    exact hFcubic C hC v hv
  have hUDcubic : ∀ v ∈ U ∪ Cycle.vertices D, G.degree v = 3 := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (hUcubic v) (hDcubic v)
  have hcomp := originalExteriorComponents_union_eq_of_far_region hG J U
    (Cycle.vertices D) B q hq hUJ hDJ hUDisj (CycleSupply.cycle_vertices_connected G D)
    hB hsmall hfar
  have hcross := crossSize_eq_zero_of_far J U (Cycle.vertices D) q hq hUJ hDJ hfar
  have hedge := internalEdges_union_card G U (Cycle.vertices D) hUDisj
  have hcard := Finset.card_union_of_disjoint hUDisj
  have hDedges : (internalEdges G (Cycle.vertices D)).card = BoundaryDecay.Cycle.length D := by
    rw [hinduced]
    rfl
  have hDv := Cycle.length_eq_vertices_card D
  have hold := cubic_original_rank_loss G hG U hUcubic
  have hnew := cubic_original_rank_loss G hG (U ∪ Cycle.vertices D) hUDcubic
  have hrank : (networkRank (Network.Shore.outside G.traceNetwork (U ∪ Cycle.vertices D)) : ℤ) -
      networkRank (Network.Shore.outside G.traceNetwork U) = -(BoundaryDecay.Cycle.length D : ℤ) := by
    omega
  rw [conditional_cycle_probability_eq_residual_rank_ratio F D hFdisj hFDdisj]
  have hunion : tupleVertices (insert D F) = U ∪ Cycle.vertices D := by
    simp [tupleVertices, U, Finset.biUnion_insert, Finset.union_comm]
  rw [hunion, hrank, dyadic_neg_nat]

end Erdos1016.Proof.IsolatedCycleConditionalLaw
end

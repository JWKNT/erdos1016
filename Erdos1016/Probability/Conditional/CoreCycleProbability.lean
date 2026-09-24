import Erdos1016.Decomposition.TwoCore.DegreeThreeRankLoss
import Erdos1016.Decomposition.TwoCore.DeletedCycleConnectivity

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CoreConditionalProbability

open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay BoundaryTrace SafeCore
open CycleExtensionProbability

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideVertex S) :=
  Network.Shore.outsideVertexFintype G.traceNetwork S
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideEdge G.traceNetwork S) :=
  Network.Shore.outsideEdgeFintype G.traceNetwork S

theorem cycle_subset_residual_core (G : PhysicalGraph) (U : Finset G.Vertex)
    (D : G.CycleWord) (hdisj : Disjoint U (Cycle.vertices D)) :
    Cycle.vertices D ⊆ vertices G.toSimpleGraph Uᶜ := by
  apply maximal G.toSimpleGraph Uᶜ _ _ (CoreCycleSpace.usedVertices_minTwo G (Cycle.seed D))
  intro v hv
  exact Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp hdisj h hv)

theorem componentCount_empty (G : PhysicalGraph) : componentCount G ∅ = 0 := by
  unfold componentCount
  have h : components G ∅ = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro C hC
    obtain ⟨v, hv⟩ := (component_connected G hC).1
    exact Finset.not_mem_empty v (component_subset G hC hv)
  rw [h, Finset.card_empty]

theorem componentCount_pos (G : PhysicalGraph) (K : Finset G.Vertex)
    (hK : K.Nonempty) : 1 ≤ componentCount G K := by
  obtain ⟨v, hv⟩ := hK
  obtain ⟨C, hC, _⟩ := components_cover G hv
  exact Finset.card_pos.mpr ⟨C, hC⟩

/-- The geometric small-component conclusion implies the required rank
drop in the original residual network, including all its pruned trees. -/
theorem residual_rank_drop (G : PhysicalGraph) (U : Finset G.Vertex)
    (D : G.CycleWord) (B : Finset G.Vertex)
    (hdisj : Disjoint U (Cycle.vertices D)) (hinduced : Cycle.IsInduced D)
    (hcubic : ∀ v ∈ Cycle.vertices D, G.degree v ≤ 3)
    (hB : B ∈ components G (U ∪ Cycle.vertices D)ᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ Cycle.vertices D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ e f, e ∈ crossing G R (Cycle.vertices D) →
        f ∈ crossing G R (Cycle.vertices D) → e = f)) :
    (networkRank (Network.Shore.outside G.traceNetwork (U ∪ Cycle.vertices D)) : ℤ) +
      ((Cycle.vertices D).filter fun v =>
        degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph Uᶜ) v = 3).card ≤
      (networkRank (Network.Shore.outside G.traceNetwork U) : ℤ) := by
  let K := vertices G.toSimpleGraph Uᶜ
  have hDK : Cycle.vertices D ⊆ K := cycle_subset_residual_core G U D hdisj
  have hcycle : (internalEdges G (Cycle.vertices D)).card = (Cycle.vertices D).card := by
    rw [hinduced]
    exact Cycle.length_eq_vertices_card D
  have hdegree : ∀ v ∈ Cycle.vertices D, degreeWithin G.toSimpleGraph K v = 2 ∨
      degreeWithin G.toSimpleGraph K v = 3 := by
    intro v hv
    have hlo := vertices_minTwo G.toSimpleGraph Uᶜ v (hDK hv)
    have hhi := (degreeWithin_le_degree G.toSimpleGraph K v).trans
      ((original_degree_eq_graph_degree G v) ▸ hcubic v hv)
    change 2 ≤ degreeWithin G.toSimpleGraph K v at hlo
    omega
  have hcomp : componentCount G (K \ Cycle.vertices D) ≤ componentCount G K := by
    rcases ConditionalCoreComplement.twoCore_sdiff_connected_or_empty G U
        (Cycle.vertices D) B hB hsmall with h | h
    · rw [show K \ Cycle.vertices D = ∅ from h, componentCount_empty]
      exact Nat.zero_le _
    · rw [componentCount_eq_one_of_connected G h]
      exact componentCount_pos G K ((Cycle.vertices_nonempty D).mono hDK)
  have hr := CoreRankLoss.rank_drop_ge_degreeThree G K (Cycle.vertices D) hDK hcycle hdegree hcomp
  have hnum := CoreCycleSpace.outside_rank_union_eq_core G U (Cycle.vertices D)
  have hden := CoreCycleSpace.outside_rank_eq_of_forced_zero_iff G U Kᶜ (fun x => by
    simpa only [Finset.union_empty] using
      CoreCycleSpace.forced_zero_union_iff_core G U ∅ x)
  have hset : Kᶜ ∪ Cycle.vertices D = (K \ Cycle.vertices D)ᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  rw [hnum, hden]
  rw [← hset] at hr
  exact hr

/-- Conditional occurrence of a retained cycle costs one factor of one-half
per degree-three vertex in the full residual two-core. -/
theorem conditional_cycle_probability_le
    (G : PhysicalGraph) (F : Finset G.CycleWord) (D : G.CycleWord)
    (B : Finset G.Vertex)
    (hFdisj : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hFDdisj : ∀ C ∈ F, Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hinduced : Cycle.IsInduced D)
    (hcubic : ∀ v ∈ Cycle.vertices D, G.degree v ≤ 3)
    (hB : B ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ)
    (hsmall : ∀ R ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ e f, e ∈ crossing G R (Cycle.vertices D) →
        f ∈ crossing G R (Cycle.vertices D) → e = f)) :
    conditionalDensity (tupleEvent F) (Cycle.Event D) ≤
      1 / (2 : ℝ) ^ ((Cycle.vertices D).filter fun v =>
        degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v = 3).card := by
  apply conditional_cycle_probability_le_of_residual_rank_drop F D _ hFdisj hFDdisj
  have hdisj : Disjoint (tupleVertices F) (Cycle.vertices D) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hFDdisj C hC) hvC hvD
  have hr := residual_rank_drop G (tupleVertices F) D B hdisj hinduced hcubic hB hsmall
  have hset : tupleVertices (insert D F) = tupleVertices F ∪ Cycle.vertices D := by
    simp [tupleVertices, Finset.union_comm]
  rw [hset]
  exact hr

end Erdos1016.Proof.CoreConditionalProbability

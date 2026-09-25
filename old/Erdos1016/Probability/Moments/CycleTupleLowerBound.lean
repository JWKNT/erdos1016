import Erdos1016.Probability.Conditional.CycleFactorization
import Erdos1016.Probability.Avoidance.ConditionalExtensionBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators
open Erdos1016.BoundaryDecay Erdos1016.SafeCore

private theorem mem_internalEdges (G : PhysicalGraph) (S : Finset G.Vertex) (e : G.Edge) :
    e ∈ internalEdges G S ↔ G.src e ∈ S ∧ G.dst e ∈ S := by
  classical
  simp [internalEdges]

/-- A disjoint union of physical cycles contains at least as many internal
edges as vertices, even when there are chords or edges between its cycles. -/
theorem cycle_union_internal_edges_ge_vertices
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (C : ι → G.CycleWord)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (BoundaryDecay.Cycle.vertices (C i)) (BoundaryDecay.Cycle.vertices (C j))) :
    (F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)).card =
        ∑ i ∈ F, BoundaryDecay.Cycle.length (C i) ∧
      (F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)).card ≤
        (internalEdges G (F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i))).card := by
  classical
  have hvdisj : (↑F : Set ι).PairwiseDisjoint (fun i => BoundaryDecay.Cycle.vertices (C i)) := by
    intro i hi j hj hij
    exact hdisj i hi j hj hij
  have hedisj : (↑F : Set ι).PairwiseDisjoint (fun i => BoundaryDecay.Cycle.edges (C i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hvi := (mem_internalEdges G (BoundaryDecay.Cycle.vertices (C i)) e).mp
      (BoundaryDecay.Cycle.edges_subset_internal (C i) hei)
    have hvj := (mem_internalEdges G (BoundaryDecay.Cycle.vertices (C j)) e).mp
      (BoundaryDecay.Cycle.edges_subset_internal (C j) hej)
    exact Finset.disjoint_left.mp (hdisj i hi j hj hij) hvi.1 hvj.1
  have hvcount : (F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)).card =
      ∑ i ∈ F, BoundaryDecay.Cycle.length (C i) := by
    rw [Finset.card_biUnion hvdisj]
    exact Finset.sum_congr rfl fun i _ => (BoundaryDecay.Cycle.length_eq_vertices_card (C i)).symm
  have hecount : (F.biUnion fun i => BoundaryDecay.Cycle.edges (C i)).card =
      ∑ i ∈ F, BoundaryDecay.Cycle.length (C i) := by
    rw [Finset.card_biUnion hedisj]
    rfl
  have hsub : (F.biUnion fun i => BoundaryDecay.Cycle.edges (C i)) ⊆
      internalEdges G (F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)) := by
    intro e he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hs, ht⟩ := (mem_internalEdges G (BoundaryDecay.Cycle.vertices (C i)) e).mp
      (BoundaryDecay.Cycle.edges_subset_internal (C i) hei)
    exact (mem_internalEdges G _ e).mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, hi, hs⟩, Finset.mem_biUnion.mpr ⟨i, hi, ht⟩⟩
  exact ⟨hvcount, by rw [hvcount, ← hecount]; exact Finset.card_le_card hsub⟩

/-- Actual joint cycle probabilities dominate geometric product weights.
This needs only disjointness, cubic incidences on the cycles, and a nonempty
exterior. No distance, independence, or connected-exterior premise is used. -/
theorem disjoint_cycle_tuple_probability_ge_product
    {G : PhysicalGraph} (hG : G.IsConnected)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (C : ι → G.CycleWord)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (BoundaryDecay.Cycle.vertices (C i)) (BoundaryDecay.Cycle.vertices (C j)))
    (hcubic : ∀ i ∈ F, ∀ v ∈ BoundaryDecay.Cycle.vertices (C i), G.degree v = 3)
    (v₀ : G.Vertex) (hv₀ : v₀ ∉ F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)) :
    (∏ i ∈ F, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (C i)) ≤
      Finite.density (fun x : G.CycleSpace => ∀ i ∈ F, BoundaryDecay.Cycle.Event (C i) x) := by
  classical
  let U := F.biUnion fun i => BoundaryDecay.Cycle.vertices (C i)
  let z := ∑ i ∈ F, BoundaryDecay.Cycle.seed (C i)
  have hzero : ∀ i ∈ F, ∀ j ∈ F, j ≠ i → ∀ e,
      G.src e ∈ BoundaryDecay.Cycle.vertices (C i) ∨ G.dst e ∈ BoundaryDecay.Cycle.vertices (C i) →
        (BoundaryDecay.Cycle.seed (C j)).1 e = 0 := by
    intro i hi j hj hji e he
    exact BoundaryDecay.Cycle.word_zero_at_disjoint_incidence (C i) (C j)
      (hdisj i hi j hj hji.symm) e he
  have hevent : Finite.density (fun x : G.CycleSpace => ∀ i ∈ F, BoundaryDecay.Cycle.Event (C i) x) =
      forcedProbability G U z := by
    unfold forcedProbability Finite.density Finite.count
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    have hiff := forcedRegion_biUnion_iff F (fun i => BoundaryDecay.Cycle.vertices (C i))
      (fun i => BoundaryDecay.Cycle.seed (C i)) x hzero
    change (∀ i ∈ F, BoundaryDecay.Cycle.Event (C i) x) ↔ ForcedRegion G.traceNetwork U z.1 x.1 at hiff
    simp only [hiff]
  have hU : ∀ v ∈ U, G.degree v = 3 := by
    intro v hv
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    exact hcubic i hi v hv
  have hgeom := cycle_union_internal_edges_ge_vertices F C hdisj
  have hcomp := originalExteriorComponents_pos G U v₀ hv₀
  have hweight : (∏ i ∈ F, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (C i)) =
      dyadic (-(∑ i ∈ F, BoundaryDecay.Cycle.length (C i) : ℕ)) := by
    rw [dyadic_neg_nat]
    simp only [one_div]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hweight, hevent, cubic_forcedProbability G hG U hU z]
  apply dyadic_mono
  have hUcard : U.card = ∑ i ∈ F, BoundaryDecay.Cycle.length (C i) := hgeom.1
  have hiedges : U.card ≤ (internalEdges G U).card := hgeom.2
  omega

end Erdos1016.Proof.ConditionalMoments

import Erdos1016.Probability.Conditional.CoreCycleProbability
import Erdos1016.Nonbacktracking.Walks.WeightedPrefixes
import Erdos1016.Cycles.Geometry.PhysicalCycleEmbedding

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalBranchWeights

open scoped BigOperators
open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay
open CycleExtensionProbability PhysicalCycleEmbedding

/-- Reciprocal branching on degrees two and three, extended harmlessly to
other degrees for use as a total vertex function. -/
def weight (d : ℕ) : ℝ := if d = 2 then 1 else 1 / 2

theorem weight_nonneg (d : ℕ) : 0 ≤ weight d := by unfold weight; split <;> norm_num
theorem weight_le_one (d : ℕ) : weight d ≤ 1 := by unfold weight; split <;> norm_num
theorem weight_le_half (d : ℕ) (hd : d ≠ 2) : weight d ≤ 1 / 2 := by simp [weight, hd]

/-- Deleting further ordinary vertices can only reduce the nonbacktracking
row sum. In particular, the protector and its apex need not be part of the
graph in which walks are counted. -/
theorem row_le_one (G : PhysicalGraph) (d : G.Vertex → ℕ)
    (hd : ∀ v, d v = 2 ∨ d v = 3) (hdegree : ∀ v, G.degree v ≤ d v)
    (e : Dart G) : weight (d (head G e)) * ((successors G e).card : ℝ) ≤ 1 := by
  have hc := (Nat.sub_le_sub_right (hdegree (head G e)) 1)
  rw [← successors_card G e] at hc
  rcases hd (head G e) with h | h
  · rw [h] at hc ⊢
    have hc' : ((successors G e).card : ℝ) ≤ 1 := by exact_mod_cast hc
    simpa [weight] using hc'
  · rw [h] at hc ⊢
    have hc' : ((successors G e).card : ℝ) ≤ 2 := by exact_mod_cast hc
    norm_num [weight]
    linarith

theorem product_eq_inverse_pow {V : Type*} (S : Finset V) (d : V → ℕ)
    (hd : ∀ v ∈ S, d v = 2 ∨ d v = 3) :
    (∏ v ∈ S, weight (d v)) = 1 / (2 : ℝ) ^ (S.filter fun v => d v = 3).card := by
  classical
  have hpoint (v : V) (hv : v ∈ S) : weight (d v) = if d v = 3 then 1 / 2 else 1 := by
    rcases hd v hv with h | h <;> simp [weight, h]
  rw [Finset.prod_congr rfl hpoint, Finset.prod_ite]
  simp [div_pow]

/-- The surviving ordinary graph uses the full core degree for its weights.
This is the actual setting in which the protector is omitted from walk
counting while still contributing incidences to the conditional rank. -/
def inducedCoreDegree (G : PhysicalGraph) (K S : Finset G.Vertex)
    (v : (inducedPhysical G S).Vertex) : ℕ :=
  degreeWithin G.toSimpleGraph K ((induced G S).vertex v)

theorem inducedCoreDegree_two_or_three (G : PhysicalGraph) (K S : Finset G.Vertex)
    (hSK : S ⊆ K) (hmin : MinTwo G.toSimpleGraph K)
    (hmax : ∀ v ∈ S, G.degree v ≤ 3) (v : (inducedPhysical G S).Vertex) :
    inducedCoreDegree G K S v = 2 ∨ inducedCoreDegree G K S v = 3 := by
  have hv := induced_vertex_mem G S v
  have hlo := hmin _ (hSK hv)
  have hhi := (degreeWithin_le_degree G.toSimpleGraph K ((induced G S).vertex v)).trans
    ((original_degree_eq_graph_degree G _) ▸ hmax _ hv)
  unfold inducedCoreDegree
  omega

theorem induced_degree_le_coreDegree (G : PhysicalGraph) (K S : Finset G.Vertex)
    (hSK : S ⊆ K) (v : (inducedPhysical G S).Vertex) :
    (inducedPhysical G S).degree v ≤ inducedCoreDegree G K S v := by
  classical
  have hdeg := inducedPhysical_degree_eq G S
    ((Fintype.equivFin (BoundaryTrace.Network.Shore.InsideVertex S)).symm v)
  simp only [Equiv.apply_symm_apply] at hdeg
  rw [hdeg]
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨hSK (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩

theorem induced_core_row_le_one (G : PhysicalGraph) (K S : Finset G.Vertex)
    (hSK : S ⊆ K) (hmin : MinTwo G.toSimpleGraph K)
    (hmax : ∀ v ∈ S, G.degree v ≤ 3) (e : Dart (inducedPhysical G S)) :
    weight (inducedCoreDegree G K S (head (inducedPhysical G S) e)) *
      ((successors (inducedPhysical G S) e).card : ℝ) ≤ 1 :=
  row_le_one _ _ (inducedCoreDegree_two_or_three G K S hSK hmin hmax)
    (induced_degree_le_coreDegree G K S hSK) e

/-- The conditional rank bound is exactly the product of branching weights
on the new cycle; this form is consumed by the weighted walk count. -/
theorem conditional_mass_le_product
    (G : PhysicalGraph) (F : Finset G.CycleWord) (D : G.CycleWord)
    (B : Finset G.Vertex)
    (hFdisj : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hFDdisj : ∀ C ∈ F, Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hinduced : Cycle.IsInduced D)
    (hcubic : ∀ v ∈ Cycle.vertices D, G.degree v ≤ 3)
    (hB : B ∈ SafeCore.components G (tupleVertices F ∪ Cycle.vertices D)ᶜ)
    (hsmall : ∀ R ∈ SafeCore.components G (tupleVertices F ∪ Cycle.vertices D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ e f, e ∈ SafeCore.crossing G R (Cycle.vertices D) →
        f ∈ SafeCore.crossing G R (Cycle.vertices D) → e = f)) :
    conditionalDensity (tupleEvent F) (Cycle.Event D) ≤
      ∏ v ∈ Cycle.vertices D,
        weight (degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v) := by
  classical
  have hdisj : Disjoint (tupleVertices F) (Cycle.vertices D) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hFDdisj C hC) hvC hvD
  have hDK := CoreConditionalProbability.cycle_subset_residual_core G (tupleVertices F) D hdisj
  have hdegree : ∀ v ∈ Cycle.vertices D,
      degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v = 2 ∨
      degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v = 3 := by
    intro v hv
    have hlo := vertices_minTwo G.toSimpleGraph (tupleVertices F)ᶜ v (hDK hv)
    have hhi := (degreeWithin_le_degree G.toSimpleGraph
      (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v).trans
      ((original_degree_eq_graph_degree G v) ▸ hcubic v hv)
    change 2 ≤ degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph (tupleVertices F)ᶜ) v at hlo
    omega
  rw [product_eq_inverse_pow _ _ hdegree]
  exact CoreConditionalProbability.conditional_cycle_probability_le G F D B hFdisj hFDdisj
    hinduced hcubic hB hsmall

end Erdos1016.Proof.ConditionalBranchWeights

import Erdos1016.Decomposition.TwoCore.CycleSpacePruning
import Erdos1016.Graph.InducedShore

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CoreRankLoss

open scoped BigOperators
open Nonbacktracking Nonbacktracking.FiniteTwoCore BoundaryDecay BoundaryTrace SafeCore

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideVertex S) :=
  Network.Shore.outsideVertexFintype G.traceNetwork S
local instance (G : PhysicalGraph) (S : Finset G.Vertex) :
    Fintype (Network.Shore.OutsideEdge G.traceNetwork S) :=
  Network.Shore.outsideEdgeFintype G.traceNetwork S

/-- Euler rank of a literal induced region, keeping isolated vertices. -/
theorem region_rank_euler (G : PhysicalGraph) (K : Finset G.Vertex) :
    (networkRank (Network.Shore.outside G.traceNetwork Kᶜ) : ℤ) =
      (internalEdges G K).card - (K.card : ℤ) + componentCount G K := by
  have hV : Fintype.card (Network.Shore.OutsideVertex Kᶜ) = K.card := by
    apply Fintype.card_of_subtype
    intro v
    simp
  have hE : Fintype.card (Network.Shore.OutsideEdge G.traceNetwork Kᶜ) =
      (internalEdges G K).card := by
    apply Fintype.card_of_subtype
    intro e
    simp [internalEdges, PhysicalGraph.traceNetwork]
  have hC : Fintype.card (Network.Shore.outside G.traceNetwork Kᶜ).Component =
      componentCount G K := by
    rw [outside_component_card, ← exteriorCount_eq_original]
    simp [exteriorCount]
  rw [network_rank_int, hV, hE, hC]

theorem degreeWithin_eq_traceInsideDegree (G : PhysicalGraph) (K : Finset G.Vertex)
    (v : G.Vertex) (hv : v ∈ K) :
    degreeWithin G.toSimpleGraph K v = G.traceInsideDegree K v :=
  (inducedPhysical_degree_eq G K ⟨v, hv⟩).symm.trans
    (Extremal.inducedShore_degree_eq_traceInsideDegree G K ⟨v, hv⟩)

/-- The degree ledger within a residual core, localized to the candidate
cycle's vertices. No degree bound is needed on the protected apex. -/
theorem degree_sum_within_subset (G : PhysicalGraph) (K D : Finset G.Vertex)
    (hDK : D ⊆ K) :
    (∑ v ∈ D, degreeWithin G.toSimpleGraph K v) =
      2 * (internalEdges G D).card + crossSize G D (K \ D) := by
  have hdegree (v : G.Vertex) (hv : v ∈ D) :
      degreeWithin G.toSimpleGraph K v =
        ∑ e : G.Edge, if G.src e ∈ K ∧ G.dst e ∈ K then
          ((if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0)) else 0 := by
    rw [degreeWithin_eq_traceInsideDegree G K v (hDK hv)]
    unfold PhysicalGraph.traceInsideDegree PhysicalGraph.traceInsideEdgesAt
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    have hn := G.noLoops e
    by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v <;>
      by_cases hsk : G.src e ∈ K <;> by_cases hdk : G.dst e ∈ K <;>
      simp_all [PhysicalGraph.incident]
  have hpoint (e : G.Edge) :
      (if G.src e ∈ K ∧ G.dst e ∈ K then
        ((if G.src e ∈ D then 1 else 0) + (if G.dst e ∈ D then 1 else 0)) else 0) =
      2 * (if G.src e ∈ D ∧ G.dst e ∈ D then 1 else 0) +
        (if (G.src e ∈ D ∧ G.dst e ∈ K \ D) ∨
          (G.src e ∈ K \ D ∧ G.dst e ∈ D) then 1 else 0) := by
    have hs : G.src e ∈ D → G.src e ∈ K := fun h => hDK h
    have hd : G.dst e ∈ D → G.dst e ∈ K := fun h => hDK h
    by_cases hsD : G.src e ∈ D <;> by_cases htD : G.dst e ∈ D <;>
      by_cases hsK : G.src e ∈ K <;> by_cases htK : G.dst e ∈ K <;>
      simp_all
  calc
    _ = ∑ v ∈ D, ∑ e : G.Edge, if G.src e ∈ K ∧ G.dst e ∈ K then
          ((if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0)) else 0 :=
      Finset.sum_congr rfl hdegree
    _ = ∑ e : G.Edge, if G.src e ∈ K ∧ G.dst e ∈ K then
        ((if G.src e ∈ D then 1 else 0) + (if G.dst e ∈ D then 1 else 0)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : G.src e ∈ K ∧ G.dst e ∈ K
      · simp only [if_pos he]
        by_cases hs : G.src e ∈ D <;> by_cases ht : G.dst e ∈ D <;>
          simp [Finset.sum_add_distrib, eq_comm, hs, ht]
      · simp only [if_neg he, Finset.sum_const_zero]
    _ = _ := by
      simp_rw [hpoint]
      simp only [internalEdges, crossSize, crossing, Finset.card_eq_sum_ones,
        Finset.sum_filter, Finset.sum_add_distrib, Finset.mul_sum]

/-- Deleting an induced cycle from a region loses at least its number of
degree-three core vertices whenever the complement does not gain components. -/
theorem rank_drop_ge_degreeThree
    (G : PhysicalGraph) (K D : Finset G.Vertex)
    (hDK : D ⊆ K)
    (hcycle : (internalEdges G D).card = D.card)
    (hdegree : ∀ v ∈ D, degreeWithin G.toSimpleGraph K v = 2 ∨
      degreeWithin G.toSimpleGraph K v = 3)
    (hcomp : componentCount G (K \ D) ≤ componentCount G K) :
    (networkRank (Network.Shore.outside G.traceNetwork (K \ D)ᶜ) : ℤ) +
      (D.filter fun v => degreeWithin G.toSimpleGraph K v = 3).card ≤
        (networkRank (Network.Shore.outside G.traceNetwork Kᶜ) : ℤ) := by
  have hd : Disjoint D (K \ D) := by
    apply Finset.disjoint_left.mpr
    intro v hv h
    exact (Finset.mem_sdiff.mp h).2 hv
  have hu : D ∪ (K \ D) = K := Finset.union_sdiff_of_subset hDK
  have hcard : D.card + (K \ D).card = K.card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  have he := internalEdges_union_card G D (K \ D) hd
  rw [hu, hcycle] at he
  have hsum : (∑ v ∈ D, degreeWithin G.toSimpleGraph K v) =
      2 * D.card + (D.filter fun v => degreeWithin G.toSimpleGraph K v = 3).card := by
    have hpoint (v : G.Vertex) (hv : v ∈ D) : degreeWithin G.toSimpleGraph K v =
        2 + (if degreeWithin G.toSimpleGraph K v = 3 then 1 else 0) := by
      rcases hdegree v hv with h | h <;> simp [h]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
    simp [Finset.sum_boole, Nat.mul_comm]
  have hledger := degree_sum_within_subset G K D hDK
  rw [hcycle, hsum] at hledger
  rw [region_rank_euler, region_rank_euler]
  omega

end Erdos1016.Proof.CoreRankLoss

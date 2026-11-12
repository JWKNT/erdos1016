import Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.NetSmallCut

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Rank lost outside a fixed marker

The induced exterior retains every physical edge. Its components have disjoint
physical boundary cuts. When every nonempty proper cut has at least two edges,
the component count is at most half the marker boundary. Euler's formula and
the cubic degree ledger then give a loss of five ranks for eight deleted
vertices. The final wrapper derives the cut condition from the absence of a
cyclic cut of size at most four in the actual loopless cubic multigraph.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.MarkerRankLoss
open FiniteMultiGraph
local instance markerRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The induced multigraph and the literal induced simple graph have the same components. -/
theorem induced_componentCount (G : FiniteMultiGraph) (X : Finset G.Vertex) :
    (PieceCore.Induced.graph G X).componentCount =
      Fintype.card (ExteriorComponents.Component G X) := by
  exact (Fintype.card_congr (PieceCore.Induced.graphIso G X).connectedComponentEquiv).symm

/-- Every exterior component consumes at least two distinct physical boundary edges. -/
theorem twice_components_le_cut (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hP : P.Nonempty)
    (hcuts : ∀ U : Finset G.Vertex, U.Nonempty → U ≠ Finset.univ →
      2 ≤ (G.cutEdges U).card) :
    2 * (PieceCore.Induced.graph G Pᶜ).componentCount ≤ (G.cutEdges P).card := by
  rw [induced_componentCount]
  have hcomp (c : ExteriorComponents.Component G Pᶜ) :
      2 ≤ (G.cutEdges (ExteriorComponents.vertices G Pᶜ c)).card := by
    apply hcuts
    · obtain ⟨v, hv⟩ := c.nonempty_supp
      exact ⟨v.1, (ExteriorComponents.mem_vertices G Pᶜ c v.1).mpr
        ⟨v.2, (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv⟩⟩
    · intro heq
      obtain ⟨p, hp⟩ := hP
      have hmem : p ∈ ExteriorComponents.vertices G Pᶜ c := by rw [heq]; exact Finset.mem_univ _
      exact (Finset.mem_compl.mp (ExteriorComponents.vertices_subset G Pᶜ c hmem)) hp
  calc
    2 * Fintype.card (ExteriorComponents.Component G Pᶜ) =
        ∑ _c : ExteriorComponents.Component G Pᶜ, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ c : ExteriorComponents.Component G Pᶜ,
        (G.cutEdges (ExteriorComponents.vertices G Pᶜ c)).card :=
      Finset.sum_le_sum (fun c _ => hcomp c)
    _ ≤ (G.cutEdges Pᶜ).card := ExteriorComponents.sum_cut_card_le G Pᶜ
    _ = (G.cutEdges P).card := by rw [G.cutEdges_compl]

/-- Exact cubic incidence and Euler ledgers give the general doubled rank loss. -/
theorem twice_exterior_rank_add_card_le (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀ v, G.degree v = 3)
    (hP : P.Nonempty)
    (hcuts : ∀ U : Finset G.Vertex, U.Nonempty → U ≠ Finset.univ →
      2 ≤ (G.cutEdges U).card) :
    2 * (PieceCore.Induced.graph G Pᶜ).cycleRank + P.card + 2 ≤ 2 * G.cycleRank := by
  have hb := twice_components_le_cut G P hP hcuts
  have he := (PieceCore.Induced.graph G Pᶜ).euler_formula
  rw [PieceCore.Induced.vertexCount, PieceCore.Induced.edgeCount] at he
  have hd := G.sum_region_degree Pᶜ
  have hs : (∑ v ∈ Pᶜ, G.degree v) = 3 * Pᶜ.card := by simp [hcubic, Nat.mul_comm]
  rw [hs, G.cutEdges_compl] at hd
  have hall := G.sum_degree
  have hsall : (∑ v : G.Vertex, G.degree v) = 3 * G.vertexCount := by
    simp [hcubic, FiniteMultiGraph.Vertex, Nat.mul_comm]
  rw [hsall] at hall
  have hg := G.connected_euler hG
  have hv : P.card + Pᶜ.card = G.vertexCount := by
    simpa [FiniteMultiGraph.Vertex] using Finset.card_add_card_compl P
  omega

/-- Eight actual deleted vertices cost at least five ranks under the physical cut condition. -/
theorem eight_vertex_rank_loss_of_cut_bound (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀ v, G.degree v = 3)
    (hP : P.card = 8)
    (hcuts : ∀ U : Finset G.Vertex, U.Nonempty → U ≠ Finset.univ →
      2 ≤ (G.cutEdges U).card) :
    (PieceCore.Induced.graph G Pᶜ).cycleRank + 5 ≤ G.cycleRank := by
  have hp : P.Nonempty := Finset.card_pos.mp (by omega)
  have h := twice_exterior_rank_add_card_le G P hG hcubic hp hcuts
  omega

/-- The loopless network retains exactly the physical crossing labels. -/
theorem cutSize_looplessNetwork (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (U : Finset G.Vertex) :
    (looplessNetwork G).cutSize (fun v => v ∈ U) = (G.cutEdges U).card := by
  let f : {e : NonloopEdge G // (looplessNetwork G).crosses (fun v => v ∈ U) e} →
      {e : G.Edge // e ∈ G.cutEdges U} :=
    fun e => ⟨e.1.1, (G.mem_cutEdges_iff_crosses U e.1).mpr e.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun e => e.1) hab
    · intro e
      refine ⟨⟨⟨e.1, hloop e.1⟩, ?_⟩, rfl⟩
      exact (G.mem_cutEdges_iff_crosses U ⟨e.1, hloop e.1⟩).mp e.2
  calc
    _ = Nat.card {e : G.Edge // e ∈ G.cutEdges U} := Nat.card_eq_of_bijective f hf
    _ = _ := by simp

/-- In a loopless cubic graph, every nonempty proper cut of size at most two is cyclic. -/
theorem cyclic_of_cut_card_le_two (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (hcubic : ∀ v, G.degree v = 3)
    (U : Finset G.Vertex) (hne : U.Nonempty) (hproper : U ≠ Finset.univ)
    (hcut : (G.cutEdges U).card ≤ 2) : G.IsCyclicCut U := by
  let N := looplessNetwork G
  have hc : N.IsCubic := by
    intro v
    rw [← G.degree_eq_deg hloop v]
    exact hcubic v
  obtain ⟨u, hu⟩ := hne
  have hex : ∃ v : G.Vertex, v ∉ U := by
    by_contra h
    push_neg at h
    exact hproper (Finset.eq_univ_of_forall h)
  obtain ⟨v, hv⟩ := hex
  have hcyc := N.isCyclicCut_of_cutSize_le_two hc (fun v => v ∈ U) hu hv
    (by simpa only [N, cutSize_looplessNetwork G hloop U] using hcut)
  constructor
  · apply (G.hasCycleIn_iff_looplessNetwork hloop U).mpr
    have h := hcyc.1
    rw [BoundaryTrace.Network.numCycles_sub] at h
    obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.mp h
    exact ⟨x, hx, hw⟩
  · apply (G.hasCycleIn_iff_looplessNetwork hloop Uᶜ).mpr
    have h := hcyc.2
    rw [BoundaryTrace.Network.numCycles_sub] at h
    obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.mp h
    refine ⟨x, hx, ?_⟩
    intro e he
    exact ⟨Finset.mem_compl.mpr (hw e he).1, Finset.mem_compl.mpr (hw e he).2⟩

/-- No cyclic cut of size at most four rules out physical zero-, one-, and two-edge cuts. -/
theorem cut_card_ge_three (G : FiniteMultiGraph)
    (hloop : ¬ G.HasLoop) (hcubic : ∀ v, G.degree v = 3)
    (hnocut : ¬ G.HasCyclicCutLE 4)
    (U : Finset G.Vertex) (hne : U.Nonempty) (hproper : U ≠ Finset.univ) :
    3 ≤ (G.cutEdges U).card := by
  by_contra hn
  have hcyc := cyclic_of_cut_card_le_two G (G.isLoopless_iff_not_hasLoop.mpr hloop)
    hcubic U hne hproper (by omega)
  exact hnocut ⟨U, hcyc, by omega⟩

/-- The actual eight-vertex marker rank loss used in the large-girth case.
Marker connectedness is unnecessary for this rank estimate. -/
theorem eight_vertex_rank_loss (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀ v, G.degree v = 3)
    (hloop : ¬ G.HasLoop) (hnocut : ¬ G.HasCyclicCutLE 4) (hP : P.card = 8) :
    (PieceCore.Induced.graph G Pᶜ).cycleRank + 5 ≤ G.cycleRank := by
  apply eight_vertex_rank_loss_of_cut_bound G P hG hcubic hP
  intro U hne hproper
  exact le_trans (by decide : 2 ≤ 3) (cut_card_ge_three G hloop hcubic hnocut U hne hproper)

end Erdos1016.ExactMaximumSupport.LargeGirth.MarkerRankLoss

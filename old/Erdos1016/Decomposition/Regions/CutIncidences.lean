import Erdos1016.Graph.CutPacking
import Erdos1016.Cleanup.Corridors.TreeIncidenceCount

set_option autoImplicit false

/-!
# Comparing physical cuts with external adjacency incidences

The corridor arguments count outside neighbors at vertices of a region,
whereas the probability bounds use the labelled physical edge cut.  In a
simple physical graph, every crossing edge determines a distinct ordered
inside-to-outside adjacency.  This gives the needed comparison without
changing the host-edge cut convention.
-/

noncomputable section

namespace Erdos1016.Proof.PhysicalCutBoundaryCount

open Erdos1016
open SimpleGraph

variable (G : PhysicalGraph) (U : Finset G.Vertex)

/-- The total number of outside-neighbor incidences based at vertices in
`U`. -/
noncomputable def externalIncidenceCount
    [DecidableRel G.toSimpleGraph.Adj] : ℕ :=
  ∑ v ∈ U, (G.toSimpleGraph.neighborFinset v \ U).card

private abbrev OutgoingPair :=
  Σ v : {v : G.Vertex // v ∈ U},
    {w : G.Vertex // w ∉ U ∧ G.toSimpleGraph.Adj v.1 w}



private theorem outgoingPair_card [DecidableRel G.toSimpleGraph.Adj] :
    Nat.card (OutgoingPair G U) = externalIncidenceCount G U := by
  classical
  let fiber (v : G.Vertex) :=
    {w : G.Vertex // w ∉ U ∧ G.toSimpleGraph.Adj v w}
  have hfiber (v : G.Vertex) :
      Nat.card (fiber v) =
        (G.toSimpleGraph.neighborFinset v \ U).card := by
    have e : fiber v ≃
        {w : G.Vertex // w ∈ G.toSimpleGraph.neighborFinset v \ U} :=
      Equiv.subtypeEquivRight (fun w => by
        simp [fiber, SimpleGraph.mem_neighborFinset, and_comm])
    calc
      Nat.card (fiber v) = Nat.card {w : G.Vertex //
          w ∈ G.toSimpleGraph.neighborFinset v \ U} := Nat.card_congr e
      _ = (G.toSimpleGraph.neighborFinset v \ U).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  change Nat.card (Σ v : {v : G.Vertex // v ∈ U}, fiber v.1) = _
  rw [Nat.card_sigma]
  simp_rw [hfiber]
  let f : G.Vertex → ℕ := fun v =>
    (G.toSimpleGraph.neighborFinset v \ U).card
  have hsum := Finset.sum_subtype_eq_sum_filter
    (s := (Finset.univ : Finset G.Vertex)) f (p := fun v => v ∈ U)
  simpa [externalIncidenceCount, f] using hsum

/-- The labelled-edge cut has size at most the number of outside-neighbor
incidences based in the region. -/
theorem actualCut_le_externalIncidenceCount
    [DecidableRel G.toSimpleGraph.Adj] :
    G.actualCut U ≤ externalIncidenceCount G U := by
  classical
  let f : {e : G.Edge // e ∈ G.cutEdges U} → OutgoingPair G U := fun e => by
    have hcut := (Finset.mem_filter.mp e.2).2
    by_cases hs : G.src e.1 ∈ U
    · have ht : G.dst e.1 ∉ U := by
        rcases hcut with hleft | hright
        · exact hleft.2
        · exact (hright.1 hs).elim
      have hadj : G.toSimpleGraph.Adj (G.src e.1) (G.dst e.1) := by
        exact ⟨e.1, by simp [PhysicalGraph.toSimpleGraph,
          PhysicalGraph.selectedGraph], Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨⟨G.src e.1, hs⟩, ⟨G.dst e.1, ht, hadj⟩⟩
    · have ht : G.dst e.1 ∈ U := by
        rcases hcut with hleft | hright
        · exact (hs hleft.1).elim
        · exact hright.2
      have hadj : G.toSimpleGraph.Adj (G.dst e.1) (G.src e.1) := by
        exact ⟨e.1, by simp [PhysicalGraph.toSimpleGraph,
          PhysicalGraph.selectedGraph], Or.inr ⟨rfl, rfl⟩⟩
      exact ⟨⟨G.dst e.1, ht⟩, ⟨G.src e.1, hs, hadj⟩⟩
  have hinj : Function.Injective f := by
    intro e g h
    have h' := h
    by_cases he : G.src e.1 ∈ U <;> by_cases hg : G.src g.1 ∈ U
    · simp only [f, dif_pos he, dif_pos hg] at h'
      have hsrc := congrArg (fun p : OutgoingPair G U => p.1.1) h'
      have hdst := congrArg (fun p : OutgoingPair G U => p.2.1) h'
      change G.src e.1 = G.src g.1 at hsrc
      change G.dst e.1 = G.dst g.1 at hdst
      apply Subtype.ext
      apply G.simple
      exact Or.inl ⟨hsrc, hdst⟩
    · simp only [f, dif_pos he, dif_neg hg] at h'
      have hsrc := congrArg (fun p : OutgoingPair G U => p.1.1) h'
      have hdst := congrArg (fun p : OutgoingPair G U => p.2.1) h'
      change G.src e.1 = G.dst g.1 at hsrc
      change G.dst e.1 = G.src g.1 at hdst
      apply Subtype.ext
      apply G.simple
      exact Or.inr ⟨hsrc, hdst⟩
    · simp only [f, dif_neg he, dif_pos hg] at h'
      have hsrc := congrArg (fun p : OutgoingPair G U => p.2.1) h'
      have hdst := congrArg (fun p : OutgoingPair G U => p.1.1) h'
      change G.src e.1 = G.dst g.1 at hsrc
      change G.dst e.1 = G.src g.1 at hdst
      apply Subtype.ext
      apply G.simple
      exact Or.inr ⟨hsrc, hdst⟩
    · simp only [f, dif_neg he, dif_neg hg] at h'
      have hsrc := congrArg (fun p : OutgoingPair G U => p.2.1) h'
      have hdst := congrArg (fun p : OutgoingPair G U => p.1.1) h'
      change G.src e.1 = G.src g.1 at hsrc
      change G.dst e.1 = G.dst g.1 at hdst
      apply Subtype.ext
      apply G.simple
      exact Or.inl ⟨hsrc, hdst⟩
  have hcard : Nat.card {e : G.Edge // e ∈ G.cutEdges U} ≤
      Nat.card (OutgoingPair G U) :=
    Finite.card_le_of_injective f hinj
  rw [outgoingPair_card G U] at hcard
  simpa only [PhysicalGraph.actualCut, Nat.card_eq_fintype_card,
    Fintype.card_coe] using hcard







end Erdos1016.Proof.PhysicalCutBoundaryCount

end

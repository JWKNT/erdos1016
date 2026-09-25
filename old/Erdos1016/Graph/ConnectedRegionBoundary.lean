import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

/-!
# Boundary endpoints for finite corridor regions

This module isolates an endpoint/exhaustion fact needed before a global
degree-two corridor decomposition can be built.  A connected graph cannot
have a nonempty proper vertex region with no edge leaving it.  In particular,
the connected region grown from any unprotected start must eventually reach a
protected vertex or another vertex outside the region.

The result does not construct the maximal corridors themselves; that remains
the open construction gap recorded by `RecordedChainConstructionFacts`.
-/

namespace Erdos1016.Proof.ConnectedRegionBoundary

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- A walk from a vertex in `S` to a vertex outside `S` contains a boundary
edge, oriented from its endpoint in `S` to its endpoint outside `S`. -/
theorem Walk.exists_adj_boundary
    {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab tail ih =>
      by_cases hb : b ∈ S
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

/-- Every nonempty proper region of a connected graph has a boundary edge.
This endpoint/exhaustion lemma is useful for a component grown through
unprotected degree-two vertices: it rules out exhaustion inside that proper
region while a protected vertex remains outside. -/
theorem Connected.exists_adj_boundary
    (hconn : G.Connected) (hS : S.Nonempty) (hproper : S ≠ Set.univ) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ : ∃ b, b ∉ S := by
    by_contra h
    push_neg at h
    apply hproper
    ext x
    simp only [Set.mem_univ, iff_true]
    exact h x
  obtain ⟨p, _hp⟩ := hconn.exists_isPath a b
  exact Erdos1016.Proof.ConnectedRegionBoundary.Walk.exists_adj_boundary
    p ha hb

end Erdos1016.Proof.ConnectedRegionBoundary

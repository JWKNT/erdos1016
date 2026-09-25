import Erdos1016.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

/-!
# Restricting a marked physical cycle

A proper induced restriction of a connected two-regular support is a forest.
This supplies the graph-specific implication used when a safe core avoids
an endpoint of the marked edge. No forest-restriction oracle is an input.
-/

noncomputable section
namespace Erdos1016.Extremal
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The edge-labelled degree bounds the number of distinct selected neighbours.
Simplicity is not needed for this direction; actual endpoints are retained. -/
theorem selected_neighbor_ncard_le (G : PhysicalGraph) (x : G.Word) (v : G.Vertex) :
    ((G.selectedGraph x).neighborSet v).ncard ≤ G.selectedDegree x v := by
  let F : Finset G.Edge := Finset.univ.filter (fun e => x e ≠ 0 ∧ G.incident e v)
  have hex : ∀ w : (G.selectedGraph x).neighborSet v,
      ∃ e : G.Edge, x e ≠ 0 ∧
        ((G.src e = v ∧ G.dst e = w.1) ∨
         (G.src e = w.1 ∧ G.dst e = v)) := by
    intro w
    exact w.2
  choose edge hsel hends using hex
  have hmem (w : (G.selectedGraph x).neighborSet v) : edge w ∈ F := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hsel w, ?_⟩
    rcases hends w with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  let f : (G.selectedGraph x).neighborSet v → {e // e ∈ F} :=
    fun w => ⟨edge w, hmem w⟩
  have hf : Function.Injective f := by
    intro u w heq
    have he : edge u = edge w := congrArg Subtype.val heq
    have hu := hends u
    have hw := hends w
    rw [← he] at hw
    apply Subtype.ext
    rcases hu with hu | hu <;> rcases hw with hw | hw
    · exact hu.2.symm.trans hw.2
    · exact False.elim (G.noLoops (edge u) (hu.1.trans hw.2.symm))
    · exact False.elim (G.noLoops (edge u) (hw.1.trans hu.2.symm))
    · exact hu.1.symm.trans hw.1
  have hcard := Fintype.card_le_of_injective f hf
  change Nat.card ((G.selectedGraph x).neighborSet v) ≤ _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, F,
    PhysicalGraph.selectedDegree] using hcard

/-- A cycle inside a maximum-degree-two graph is a whole connected component.
This is proved by equality of its two-element neighbour sets. -/
theorem cycle_subgraph_closed {V : Type*} [Fintype V] (J : SimpleGraph V)
    (hdeg : ∀ v, (J.neighborSet v).ncard ≤ 2)
    {u : V} (p : J.Walk u u) (hp : p.IsCycle) :
    ∀ v ∈ p.toSubgraph.verts, ∀ w, J.Adj v w → p.toSubgraph.Adj v w := by
  intro v hv w hvw
  have hsupport : v ∈ p.support := (p.mem_verts_toSubgraph).1 hv
  have hcard := hp.ncard_neighborSet_toSubgraph_eq_two hsupport
  have hsub : p.toSubgraph.neighborSet v ⊆ J.neighborSet v := by
    intro a ha
    exact p.toSubgraph.adj_sub ha
  have heq : p.toSubgraph.neighborSet v = J.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hdeg v)
  change w ∈ p.toSubgraph.neighborSet v
  rw [heq]
  exact hvw













end Erdos1016.Extremal

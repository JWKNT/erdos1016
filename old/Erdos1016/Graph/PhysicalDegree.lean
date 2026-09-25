import Erdos1016.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge

open Erdos1016
open SimpleGraph

/-- A chosen finite instance for a neighbor set. Kept as a named constructor
so callers can set it locally without fixing the degree theorem to one
particular Fintype instance. -/
noncomputable def neighborFintype (G : PhysicalGraph) (v : G.Vertex) :
    Fintype (G.toSimpleGraph.neighborSet v) := by
  classical
  exact G.toSimpleGraph.neighborSetFintype v


/-- Physical edge labels incident to a fixed vertex. -/
def incidentEdges (G : PhysicalGraph) (v : G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => G.incident e v

private def other (G : PhysicalGraph) (v : G.Vertex) (e : G.Edge) : G.Vertex :=
  if G.src e = v then G.dst e else G.src e

private theorem other_adj (G : PhysicalGraph) (v : G.Vertex) (e : G.Edge)
    (he : G.incident e v) : G.toSimpleGraph.Adj v (other G v e) := by
  rcases he with hs | hd
  · refine ⟨e, by simp, Or.inl ⟨hs, ?_⟩⟩
    simp [other, hs]
  · have hne : G.src e ≠ v := by
      intro h
      exact G.noLoops e (h.trans hd.symm)
    refine ⟨e, by simp, Or.inr ⟨?_, hd⟩⟩
    simp [other, hne]

private theorem edge_eq_of_other_eq (G : PhysicalGraph) (v : G.Vertex)
    (e f : G.Edge) (he : G.incident e v) (hf : G.incident f v)
    (hout : other G v e = other G v f) : e = f := by
  rcases he with hs | hd
  · rcases hf with hs' | hd'
    · apply G.simple
      exact Or.inl ⟨hs.trans hs'.symm, by simpa [other, hs, hs'] using hout⟩
    · apply G.simple
      have hfne : G.src f ≠ v := by
        intro h
        exact G.noLoops f (h.trans hd'.symm)
      have h : G.dst e = G.src f := by simpa [other, hs, hfne] using hout
      exact Or.inr ⟨hs.trans hd'.symm, h⟩
  · rcases hf with hs' | hd'
    · apply G.simple
      have hne : G.src e ≠ v := by
        intro h
        exact G.noLoops e (h.trans hd.symm)
      have h : G.src e = G.dst f := by simpa [other, hne, hs'] using hout
      exact Or.inr ⟨h, hd.trans hs'.symm⟩
    · apply G.simple
      have hne : G.src e ≠ v := by
        intro h
        exact G.noLoops e (h.trans hd.symm)
      have hne' : G.src f ≠ v := by
        intro h
        exact G.noLoops f (h.trans hd'.symm)
      have h : G.src e = G.src f := by simpa [other, hne, hne'] using hout
      exact Or.inl ⟨h, hd.trans hd'.symm⟩

/-- Incident labeled edges and neighboring vertices are in bijection in a
physical simple graph. -/
def incidentNeighborEquiv (G : PhysicalGraph) (v : G.Vertex)
    [Fintype (G.toSimpleGraph.neighborSet v)] :
    {e : G.Edge // e ∈ incidentEdges G v} ≃
      {w : G.Vertex // w ∈ G.toSimpleGraph.neighborFinset v} := by
  classical
  let f : {e : G.Edge // e ∈ incidentEdges G v} →
      {w : G.Vertex // w ∈ G.toSimpleGraph.neighborFinset v} := fun e =>
    ⟨other G v e.1, by
      have hi : G.incident e.1 v := (Finset.mem_filter.mp e.2).2
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 (other_adj G v e.1 hi)⟩
  have hinj : Function.Injective f := by
    intro e f' h
    apply Subtype.ext
    apply edge_eq_of_other_eq G v e.1 f'.1
      ((Finset.mem_filter.mp e.2).2) ((Finset.mem_filter.mp f'.2).2)
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro w
    have hadj : G.toSimpleGraph.Adj v w.1 :=
      (SimpleGraph.mem_neighborFinset _ _ _).1 w.2
    rcases hadj with ⟨e, he, heq | heq⟩
    · refine ⟨⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl heq.1⟩⟩, ?_⟩
      apply Subtype.ext
      change other G v e = w.1
      simp [other, heq.1, heq.2]
    · refine ⟨⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr heq.2⟩⟩, ?_⟩
      apply Subtype.ext
      change other G v e = w.1
      have hne : G.src e ≠ v := by
        intro hh
        exact G.noLoops e (hh.trans heq.2.symm)
      change (if G.src e = v then G.dst e else G.src e) = w.1
      rw [if_neg hne]
      exact heq.1
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- Physical degree equals the simple-graph neighbor count. -/
theorem degree_eq_neighborFinset_card (G : PhysicalGraph) (v : G.Vertex)
    [Fintype (G.toSimpleGraph.neighborSet v)] :
    G.degree v = (G.toSimpleGraph.neighborFinset v).card := by
  classical
  have hcard := Fintype.card_congr (incidentNeighborEquiv G v)
  calc
    G.degree v = (incidentEdges G v).card := by
      unfold PhysicalGraph.degree PhysicalGraph.selectedDegree
      apply congrArg Finset.card
      ext e
      simp [incidentEdges, PhysicalGraph.incident]
    _ = Fintype.card {e : G.Edge // e ∈ incidentEdges G v} :=
      (Fintype.card_coe (incidentEdges G v)).symm
    _ = Fintype.card {w : G.Vertex // w ∈ G.toSimpleGraph.neighborFinset v} := hcard
    _ = (G.toSimpleGraph.neighborFinset v).card := Fintype.card_coe _

end Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge

end

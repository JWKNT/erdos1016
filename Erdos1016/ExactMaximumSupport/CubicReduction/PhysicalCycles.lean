import Erdos1016.ExactMaximum.Cycles
import Erdos1016.Graph.Pruning.MarkedCore

set_option autoImplicit false

/-!
# Physical cycles in the labelled multigraph model

The two models use the same edge labels. Their degree and connectivity
definitions differ. These lemmas identify the cycle predicates explicitly.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof.CycleCore
open BoundaryDecay

variable (G : PhysicalGraph)

theorem asMultigraph_selectedDegree (x : G.Word) (v : G.Vertex) :
    (asMultigraph G).selectedDegree x v = G.selectedDegree x v := by
  classical
  let S := Finset.univ.filter fun e : G.Edge => x e ≠ 0 ∧ G.src e = v
  let T := Finset.univ.filter fun e : G.Edge => x e ≠ 0 ∧ G.dst e = v
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro e hs ht
    exact G.noLoops e
      ((Finset.mem_filter.mp hs).2.2.trans (Finset.mem_filter.mp ht).2.2.symm)
  have hs : (asMultigraph G).selectedDegree x v = S.card + T.card := by
    simp only [FiniteMultiGraph.selectedDegree, asMultigraph, Finset.filter_filter]
    rfl
  rw [hs, ← Finset.card_union_of_disjoint hd]
  unfold PhysicalGraph.selectedDegree
  congr 1
  ext e
  simp [S, T, PhysicalGraph.incident, and_or_left]

theorem asMultigraph_selectedGraph (x : G.Word) :
    (asMultigraph G).selectedGraph x = G.selectedGraph x := by
  ext u v
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact (G.selectedGraph x).ne_of_adj h

theorem usedVertices_iff_selectedDegree_pos (x : G.Word) (v : G.Vertex) :
    v ∈ G.usedVertices x ↔ 0 < G.selectedDegree x v := by
  classical
  simp [PhysicalGraph.usedVertices, PhysicalGraph.selectedDegree,
    Finset.card_pos, Finset.Nonempty]

private theorem reachable_used (x : G.Word) {u v : G.Vertex}
    (p : (G.selectedGraph x).Walk u v)
    (hu : u ∈ G.usedVertices x) (hv : v ∈ G.usedVertices x) :
    ((G.selectedGraph x).induce (↑(G.usedVertices x) : Set G.Vertex)).Reachable
      ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w v huw p ih =>
    have hw : w ∈ G.usedVertices x := by
      obtain ⟨e, he, h | h⟩ := huw
      · exact (mem_usedVertices x w).2 ⟨e, he, Or.inr h.2⟩
      · exact (mem_usedVertices x w).2 ⟨e, he, Or.inl h.1⟩
    obtain ⟨q⟩ := ih hw hv
    have hadj : ((G.selectedGraph x).induce
        (↑(G.usedVertices x) : Set G.Vertex)).Adj ⟨u, hu⟩ ⟨w, hw⟩ := huw
    exact ⟨q.cons hadj⟩

theorem asMultigraph_isCycleWord_iff (x : G.Word) :
    (asMultigraph G).IsCycleWord x ↔ G.IsCycleWord x := by
  classical
  constructor
  · intro hx
    have hconn : ((G.selectedGraph x).induce
        (↑(G.usedVertices x) : Set G.Vertex)).Connected := by
      have hne := usedVertices_nonempty_of_ne_zero x hx.1
      refine { nonempty := ⟨⟨hne.choose, hne.choose_spec⟩⟩, preconnected := ?_ }
      intro u v
      have hu := (usedVertices_iff_selectedDegree_pos G x u.1).1 u.2
      have hv := (usedVertices_iff_selectedDegree_pos G x v.1).1 v.2
      rw [← asMultigraph_selectedDegree G] at hu hv
      have hp := hx.2.2 u.1 v.1 hu hv
      rw [asMultigraph_selectedGraph G] at hp
      obtain ⟨p⟩ := hp
      exact reachable_used G x p u.2 v.2
    refine ⟨hx.1, hx.boundary_eq_zero, hconn, ?_⟩
    intro v hv
    have hpos := (usedVertices_iff_selectedDegree_pos G x v).1 hv
    have hd := hx.2.1 v
    rw [asMultigraph_selectedDegree G] at hd
    omega
  · intro hx
    refine ⟨hx.1, ?_, ?_⟩
    · intro v
      rw [asMultigraph_selectedDegree G]
      by_cases hv : v ∈ G.usedVertices x
      · exact Or.inr (hx.2.2.2 v hv)
      · exact Or.inl (selectedDegree_zero_of_not_used x v hv)
    · intro u v hu hv
      rw [asMultigraph_selectedDegree G] at hu hv
      have hu' := (usedVertices_iff_selectedDegree_pos G x u).2 hu
      have hv' := (usedVertices_iff_selectedDegree_pos G x v).2 hv
      have hp := hx.2.2.1.preconnected ⟨u, hu'⟩ ⟨v, hv'⟩
      let incl : (G.selectedGraph x).induce (↑(G.usedVertices x) : Set G.Vertex) →g
          G.selectedGraph x :=
        { toFun := Subtype.val, map_rel' := fun h => h }
      rw [asMultigraph_selectedGraph G]
      exact hp.map incl

def physicalCycleEquiv : G.CycleWord ≃
    {x : (asMultigraph G).EdgeWord // (asMultigraph G).IsCycleWord x} where
  toFun x := ⟨x.1, (asMultigraph_isCycleWord_iff G x.1).2 x.2⟩
  invFun x := ⟨x.1, (asMultigraph_isCycleWord_iff G x.1).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem asMultigraph_numCycles :
    (asMultigraph G).numCycles = Fintype.card G.CycleWord := by
  unfold FiniteMultiGraph.numCycles
  rw [← Nat.card_congr (physicalCycleEquiv G), Nat.card_eq_fintype_card]

end Erdos1016.ExactMaximumSupport.CubicReduction

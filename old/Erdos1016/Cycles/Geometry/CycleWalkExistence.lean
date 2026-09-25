import Erdos1016.Nonbacktracking.Walks.CycleWords
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking
open BoundaryDecay

variable (G : PhysicalGraph)

local instance cycleWordToWalkDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every physical cycle word is represented by an ordinary simple closed
walk on the same selected edge support. -/
theorem exists_cycle_walk_of_cycleWord (C : G.CycleWord) :
    ∃ u : G.Vertex, ∃ (p : G.toSimpleGraph.Walk u u) (hp : p.IsCycle),
      cycleWordOfWalk G p hp = C := by
  classical
  let U := G.usedVertices C.1
  let S := G.selectedGraph C.1
  let H := S.induce (↑U : Set G.Vertex)
  have hHconn : H.Connected := C.2.2.2.1
  have hneighbor_subset (v : U) : S.neighborSet v.1 ⊆ (↑U : Set G.Vertex) := by
    intro w hw
    rcases hw with ⟨e, he, h | h⟩
    · exact (mem_usedVertices C.1 w).2 ⟨e, he, Or.inr h.2⟩
    · exact (mem_usedVertices C.1 w).2 ⟨e, he, Or.inl h.1⟩
  have hneighbor_ncard (v : U) : (H.neighborSet v).ncard = 2 := by
    let e : H.neighborSet v ≃ S.neighborSet v.1 := {
      toFun := fun w => ⟨w.1.1, by
        change S.Adj v.1 w.1.1
        exact w.2⟩
      invFun := fun w => ⟨⟨w.1, hneighbor_subset v w.2⟩, by
        change S.Adj v.1 w.1
        exact w.2⟩
      left_inv := by intro w; apply Subtype.ext; rfl
      right_inv := by intro w; apply Subtype.ext; rfl }
    have hc : Fintype.card (H.neighborSet v) = Fintype.card (S.neighborSet v.1) :=
      Fintype.card_congr e
    calc
      (H.neighborSet v).ncard = Fintype.card (H.neighborSet v) := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      _ = Fintype.card (S.neighborSet v.1) := hc
      _ = (S.neighborSet v.1).ncard := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      _ = G.selectedDegree C.1 v.1 := (selectedDegree_eq_neighbor_ncard G C.1 v.1).symm
      _ = 2 := C.2.2.2.2 v.1 v.2
  have hcycles : H.IsCycles := by
    intro v hv
    exact hneighbor_ncard v
  obtain ⟨root, hreach⟩ := (SimpleGraph.connected_iff_exists_forall_reachable H).1 hHconn
  let c : H.ConnectedComponent := H.connectedComponentMk root
  have hcomp : root ∈ c.supp := by simp [c]
  have hall (w : U) : w ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound (hreach w).symm
  have hnonempty : (H.neighborSet root).Nonempty := by
    have hcard := hneighbor_ncard root
    exact (Set.ncard_pos (Set.toFinite _)).1 (by rw [hcard]; norm_num)
  obtain ⟨p, hp, hverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hcomp hnonempty
  let inc : H →g G.toSimpleGraph := {
    toFun := fun v => v.1
    map_rel' := by
      intro a b hab
      change S.Adj a.1 b.1 at hab
      rcases hab with ⟨e, he, h | h⟩
      · exact ⟨e, by simp, Or.inl h⟩
      · exact ⟨e, by simp, Or.inr h⟩ }
  let q := p.map inc
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
  have hpverts (x : U) : x ∈ p.toSubgraph.verts := by
    rw [hverts]
    exact hall x
  have hpAdj (x y : U) : p.toSubgraph.Adj x y ↔ H.Adj x y :=
    hp.adj_toSubgraph_iff_of_isCycles hcycles (hpverts x) y
  have hselected (e : G.Edge) :
      S.Adj (G.src e) (G.dst e) ↔ C.1 e ≠ 0 := by
    constructor
    · rintro ⟨f, hf, h | h⟩
      · have hef : f = e := G.simple f e (Or.inl ⟨h.1, h.2⟩)
        simpa [hef] using hf
      · have hef : f = e := G.simple f e (Or.inr h)
        simpa [hef] using hf
    · intro he
      exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have hword (e : G.Edge) :
      physicalPair G e ∈ q.edges ↔ C.1 e ≠ 0 := by
    constructor
    · intro hqedge
      have hqadj : q.toSubgraph.Adj (G.src e) (G.dst e) := by
        apply SimpleGraph.Subgraph.mem_edgeSet.1
        exact (q.mem_edges_toSubgraph).2 hqedge
      rw [SimpleGraph.Walk.toSubgraph_map] at hqadj
      rw [SimpleGraph.Subgraph.map_adj] at hqadj
      obtain ⟨x, y, hxy, hx, hy⟩ := hqadj
      have hxyS : S.Adj (G.src e) (G.dst e) := by
        have hxyH : H.Adj x y := (hpAdj x y).1 hxy
        change S.Adj x.1 y.1 at hxyH
        rw [← hx, ← hy]
        exact hxyH
      exact (hselected e).1 hxyS
    · intro he
      have hends : G.src e ∈ U ∧ G.dst e ∈ U := by
        constructor
        · exact (mem_usedVertices C.1 (G.src e)).2 ⟨e, he, Or.inl rfl⟩
        · exact (mem_usedVertices C.1 (G.dst e)).2 ⟨e, he, Or.inr rfl⟩
      have hH : H.Adj ⟨G.src e, hends.1⟩ ⟨G.dst e, hends.2⟩ :=
        (hselected e).2 he
      have hP := (hpAdj ⟨G.src e, hends.1⟩ ⟨G.dst e, hends.2⟩).2 hH
      have hmap : (p.toSubgraph.map inc).Adj (G.src e) (G.dst e) := by
        rw [SimpleGraph.Subgraph.map_adj]
        exact ⟨⟨G.src e, hends.1⟩, ⟨G.dst e, hends.2⟩, hP, rfl, rfl⟩
      have hqedge : physicalPair G e ∈ q.toSubgraph.edgeSet := by
        change s(G.src e, G.dst e) ∈ q.toSubgraph.edgeSet
        rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Walk.toSubgraph_map]
        exact hmap
      exact (q.mem_edges_toSubgraph).mp hqedge
  have hword_eq : walkWord G q = C.1 := by
    funext e
    have hbin (x : F₂) : x = 0 ∨ x = 1 := by
      fin_cases x <;> simp
    by_cases he : C.1 e ≠ 0
    · have hqedge := (hword e).2 he
      have hv : C.1 e = 1 := by
        rcases hbin (C.1 e) with hz | hone
        · exact False.elim (he (by rw [hz]))
        · exact hone
      simp [walkWord, hqedge, hv]
    · have hqedge : physicalPair G e ∉ q.edges := fun hh =>
        he ((hword e).1 hh)
      have hv : C.1 e = 0 := by
        exact not_ne_iff.mp he
      simp [walkWord, hqedge, hv]
  have hcycleWord : cycleWordOfWalk G q hq = C := Subtype.ext hword_eq
  exact ⟨root.1, q, hq, hcycleWord⟩

end Erdos1016.Nonbacktracking
end

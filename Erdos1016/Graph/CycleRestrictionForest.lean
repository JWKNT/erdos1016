import Erdos1016.Extremal.Capacity.LinearForestRestriction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

/-! A proper edge restriction of a physical cycle is acyclic. The argument
uses connectivity and degree two of that cycle; no nonbacktracking estimates
or asymptotic graph theorem is imported. -/

noncomputable section
namespace Erdos1016.ShortProof.CycleRestrictionForest
open Erdos1016.PhysicalGraph

private theorem mem_usedVertices (G : PhysicalGraph) (x : G.Word) (v : G.Vertex) :
    v ∈ G.usedVertices x ↔ ∃ e, x e ≠ 0 ∧ G.incident e v := by
  simp [PhysicalGraph.usedVertices]

private theorem src_mem_used_of_ne_zero (G : PhysicalGraph) (x : G.Word)
    (e : G.Edge) (he : x e ≠ 0) : G.src e ∈ G.usedVertices x :=
  (mem_usedVertices G x _).2 ⟨e, he, Or.inl rfl⟩

private theorem dst_mem_used_of_ne_zero (G : PhysicalGraph) (x : G.Word)
    (e : G.Edge) (he : x e ≠ 0) : G.dst e ∈ G.usedVertices x :=
  (mem_usedVertices G x _).2 ⟨e, he, Or.inr rfl⟩

private theorem selectedDegree_zero_of_not_used (G : PhysicalGraph) (x : G.Word)
    (v : G.Vertex) (hv : v ∉ G.usedVertices x) : G.selectedDegree x v = 0 := by
  classical
  unfold PhysicalGraph.selectedDegree
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_not_mem.2
  intro e he
  obtain ⟨_, hne, hi⟩ := Finset.mem_filter.1 he
  exact hv ((mem_usedVertices G x v).2 ⟨e, hne, hi⟩)

/-- The edge-labelled degree bounds the number of distinct selected neighbours.
Simplicity is not needed for this direction; actual endpoints are retained. -/
private theorem selected_neighbor_ncard_le (G : PhysicalGraph) (x : G.Word) (v : G.Vertex) :
    ((G.selectedGraph x).neighborSet v).ncard ≤ G.selectedDegree x v := by
  classical
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
private theorem cycle_subgraph_closed {V : Type*} [Fintype V] (J : SimpleGraph V)
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


/-- If a selected cycle edge is omitted, the selected graph on the retained
edges is acyclic. The proof uses that any cycle in a subgraph of a connected
two-regular graph must contain every selected edge. -/
theorem restrictedCycle_isAcyclic (G : PhysicalGraph) (C : G.CycleWord)
    (E : Finset G.Edge)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    (G.restrictedSelectedGraph E (G.restrictWord E C.1)).IsAcyclic := by
  classical
  let S := G.selectedGraph C.1
  let H := G.restrictedSelectedGraph E (G.restrictWord E C.1)
  have hdeg : ∀ v, (S.neighborSet v).ncard ≤ 2 := by
    intro v
    apply (selected_neighbor_ncard_le G C.1 v).trans
    by_cases hv : v ∈ G.usedVertices C.1
    · rw [C.2.2.2.2 v hv]
    · rw [selectedDegree_zero_of_not_used G C.1 v hv]
      omega
  intro u p hp
  let hom : H →g S := {
    toFun := id
    map_rel' := by
      intro a b hab
      exact G.restrictedSelectedGraph_le_host E C.1 hab
  }
  let q : S.Walk u u := by simpa [hom] using p.map hom
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective (by intro a b h; exact h)).2 hp
  have hclosed := cycle_subgraph_closed S hdeg q hq
  have hstart : u ∈ G.usedVertices C.1 := by
    have hpos : 0 < (q.toSubgraph.neighborSet u).ncard := by
      rw [hq.ncard_neighborSet_toSubgraph_eq_two q.start_mem_support]
      norm_num
    obtain ⟨v, hv⟩ := (Set.ncard_pos).1 hpos
    have huv : S.Adj u v := q.toSubgraph.adj_sub hv
    rcases huv with ⟨f, hf, h | h⟩
    · exact (mem_usedVertices G C.1 u).2 ⟨f, hf, Or.inl h.1⟩
    · exact (mem_usedVertices G C.1 u).2 ⟨f, hf, Or.inr h.2⟩
  have hall : ∀ v, v ∈ G.usedVertices C.1 → v ∈ q.toSubgraph.verts := by
    intro v hv
    let incl : S.induce (↑(G.usedVertices C.1) : Set G.Vertex) →g S := {
      toFun := Subtype.val
      map_rel' := by intro a b hab; exact hab
    }
    have hr : S.Reachable u v :=
      (C.2.2.2.1 ⟨u, hstart⟩ ⟨v, hv⟩).map incl
    exact hr.mem_subgraphVerts hclosed q.start_mem_verts_toSubgraph
  obtain ⟨e, heout, hex⟩ := hout
  have husrc : G.src e ∈ G.usedVertices C.1 :=
    src_mem_used_of_ne_zero G C.1 e hex
  have hudst : G.dst e ∈ G.usedVertices C.1 :=
    dst_mem_used_of_ne_zero G C.1 e hex
  have hsrc : G.src e ∈ q.toSubgraph.verts := hall _ husrc
  have houtAdj : S.Adj (G.src e) (G.dst e) := ⟨e, hex, Or.inl ⟨rfl, rfl⟩⟩
  have hqAdj : q.toSubgraph.Adj (G.src e) (G.dst e) :=
    hclosed (G.src e) hsrc (G.dst e) houtAdj
  have hmem : s(G.src e, G.dst e) ∈ q.edges :=
    (q.mem_edges_toSubgraph).1
      ((SimpleGraph.Subgraph.mem_edgeSet).2 hqAdj)
  have hedges : q.edges = p.edges := by
    change (p.map hom).edges = p.edges
    rw [SimpleGraph.Walk.edges_map]
    change List.map (Sym2.map id) p.edges = p.edges
    rw [Sym2.map_id]
    exact List.map_id _
  have hmem' : s(G.src e, G.dst e) ∈ p.edges := by rw [hedges] at hmem; exact hmem
  have hpAdj : p.toSubgraph.Adj (G.src e) (G.dst e) := by
    exact (SimpleGraph.Subgraph.mem_edgeSet).1
      ((p.mem_edges_toSubgraph).2 hmem')
  have hHAdj : H.Adj (G.src e) (G.dst e) := p.toSubgraph.adj_sub hpAdj
  rcases hHAdj with ⟨f, hf, hend | hend⟩
  · have hfe : f.1 = e := G.simple f.1 e (Or.inl ⟨hend.1, hend.2⟩)
    exact heout (hfe ▸ f.2)
  · have hfe : f.1 = e := G.simple f.1 e (Or.inr ⟨hend.1, hend.2⟩)
    exact heout (hfe ▸ f.2)


end Erdos1016.ShortProof.CycleRestrictionForest

import Erdos1016.Extremal.Capacity.EdgePartitionRank
import Erdos1016.Cycles.Geometry.ForestRestriction
import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.Extremal.Capacity.CompositionArithmetic

set_option autoImplicit false

/-!
# Cycle restrictions across an edge partition

These lemmas supply the graph-theoretic input for the numerical composition
bound: a proper edge restriction of a physical cycle is a linear forest, and
the two restrictions have the same boundary and additive lengths.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

open Erdos1016.Extremal
open Erdos1016.BoundaryDecay

private theorem nonzero_F₂_eq_one (a : F₂) (ha : a ≠ 0) : a = 1 := by
  fin_cases a <;> simp_all

private theorem boundaryZero_subword_eq_cycle (G : PhysicalGraph)
    (C : G.CycleWord) (y : G.Word)
    (hsub : ∀ e, y e ≠ 0 → C.1 e ≠ 0)
    (hzero : G.boundary y = 0) (hne : y ≠ 0) : y = C.1 := by
  classical
  let S := G.selectedGraph C.1
  let Y := G.selectedGraph y
  have husedSub : ∀ v, v ∈ G.usedVertices y → v ∈ G.usedVertices C.1 := by
    intro v hv
    rcases (mem_usedVertices y v).1 hv with ⟨e, he, hi⟩
    exact (mem_usedVertices C.1 v).2 ⟨e, hsub e he, hi⟩
  have hdegree_two : ∀ v, v ∈ G.usedVertices y → G.selectedDegree y v = 2 := by
    intro v hv
    have hpos : 0 < G.selectedDegree y v := by
      rcases (mem_usedVertices y v).1 hv with ⟨e, he, hi⟩
      unfold PhysicalGraph.selectedDegree
      apply Finset.card_pos.mpr
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hi⟩⟩
    have hle : G.selectedDegree y v ≤ G.selectedDegree C.1 v := by
      unfold PhysicalGraph.selectedDegree
      apply Finset.card_le_card
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      exact ⟨hsub e he.1, he.2⟩
    have hvC := husedSub v hv
    rw [C.2.2.2.2 v hvC] at hle
    have hzv := congrFun hzero v
    have hcast : (G.selectedDegree y v : F₂) = 0 := by
      rw [← Nonbacktracking.boundary_eq_selectedDegree_cast]
      exact hzv
    have hdiv : 2 ∣ G.selectedDegree y v :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd (G.selectedDegree y v) 2).mp hcast
    omega
  have hneighbors : ∀ v, v ∈ G.usedVertices y →
      Y.neighborSet v = S.neighborSet v := by
    intro v hv
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (by toFinite_tac)
    · intro w hw
      rcases hw with ⟨e, he, h | h⟩
      · exact ⟨e, hsub e he, Or.inl h⟩
      · exact ⟨e, hsub e he, Or.inr h⟩
    · rw [← Nonbacktracking.selectedDegree_eq_neighbor_ncard G y v,
        hdegree_two v hv,
        ← Nonbacktracking.selectedDegree_eq_neighbor_ncard G C.1 v,
        C.2.2.2.2 v (husedSub v hv)]
  let K : S.Subgraph := (⊤ : S.Subgraph).induce (↑(G.usedVertices y) : Set G.Vertex)
  have hclosed : ∀ a ∈ K.verts, ∀ b, S.Adj a b → K.Adj a b := by
    intro a ha b hab
    have ha' : a ∈ G.usedVertices y := by simpa [K] using ha
    have hbS : b ∈ S.neighborSet a := hab
    have hbY : b ∈ Y.neighborSet a := by rw [hneighbors a ha']; exact hbS
    have habY : Y.Adj a b := hbY
    rcases habY with ⟨e, he, h | h⟩
    · have hb' := (mem_usedVertices y b).2 ⟨e, he, Or.inr h.2⟩
      change a ∈ G.usedVertices y ∧ b ∈ G.usedVertices y ∧ S.Adj a b
      exact ⟨ha', hb', hab⟩
    · have hb' := (mem_usedVertices y b).2 ⟨e, he, Or.inl h.1⟩
      change a ∈ G.usedVertices y ∧ b ∈ G.usedVertices y ∧ S.Adj a b
      exact ⟨ha', hb', hab⟩
  obtain ⟨u, hu⟩ := usedVertices_nonempty_of_ne_zero y hne
  let hincl : S.induce (↑(G.usedVertices C.1) : Set G.Vertex) →g S := {
    toFun := Subtype.val
    map_rel' := by intro a b hab; exact hab
  }
  have hall : ∀ v, v ∈ G.usedVertices C.1 → v ∈ G.usedVertices y := by
    intro v hv
    let uC : {w : G.Vertex // w ∈ (↑(G.usedVertices C.1) : Set G.Vertex)} :=
      ⟨u, husedSub u hu⟩
    let vC : {w : G.Vertex // w ∈ (↑(G.usedVertices C.1) : Set G.Vertex)} :=
      ⟨v, hv⟩
    have huincl : hincl uC = u := by change uC.1 = u; rfl
    have hvincl : hincl vC = v := by change vC.1 = v; rfl
    have hr0 := (C.2.2.2.1 uC vC).map hincl
    rw [huincl, hvincl] at hr0
    have hr : S.Reachable u v := hr0
    have huK : u ∈ K.verts := by simpa [K] using hu
    have hv' := hr.mem_subgraphVerts hclosed huK
    simpa [K] using hv'
  have hword : ∀ e, C.1 e ≠ 0 → y e ≠ 0 := by
    intro e he
    have hsrc : G.src e ∈ G.usedVertices y :=
      hall _ (src_mem_used_of_ne_zero C.1 e he)
    have hadj : S.Adj (G.src e) (G.dst e) := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    have hneigh : G.dst e ∈ Y.neighborSet (G.src e) := by
      rw [hneighbors (G.src e) hsrc]
      exact hadj
    rcases hneigh with ⟨f, hf, hend | hend⟩
    · have hfe := G.simple f e (Or.inl ⟨hend.1, hend.2⟩)
      simpa [hfe] using hf
    · have hfe := G.simple f e (Or.inr ⟨hend.1, hend.2⟩)
      simpa [hfe] using hf
  funext e
  by_cases hc : C.1 e = 0
  · have hy : y e = 0 := by
      by_cases hy0 : y e = 0
      · exact hy0
      · exact False.elim ((hsub e hy0) hc)
    rw [hy, hc]
  · have hy := hword e hc
    have hy1 : y e = 1 := nonzero_F₂_eq_one (y e) hy
    have hc1 : C.1 e = 1 := nonzero_F₂_eq_one (C.1 e) hc
    rw [hy1, hc1]

def outsideEdgeEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    G.OutsideEdge E ≃ G.RestrictedEdge Eᶜ where
  toFun e := ⟨e.1, Finset.mem_compl.mpr e.2⟩
  invFun e := ⟨e.1, Finset.mem_compl.mp e.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; rfl

theorem extendOutside_eq_extendComplement (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    G.extendOutsideWord E (G.restrictOutsideWord E x) =
      G.extendWord Eᶜ (G.restrictWord Eᶜ x) := by
  funext e
  by_cases he : e ∈ E
  · simp [extendOutsideWord, restrictOutsideWord, extendWord, restrictWord, he]
  · simp [extendOutsideWord, restrictOutsideWord, extendWord, restrictWord, he]

theorem outsideBoundary_eq_complementBoundary (G : PhysicalGraph)
    (E : Finset G.Edge) (x : G.Word) :
    G.outsideBoundary E (G.restrictOutsideWord E x) =
      G.restrictedBoundary Eᶜ (G.restrictWord Eᶜ x) := by
  change G.boundary (G.extendOutsideWord E (G.restrictOutsideWord E x)) =
    G.boundary (G.extendWord Eᶜ (G.restrictWord Eᶜ x))
  rw [G.extendOutside_eq_extendComplement E x]

theorem outsideWordLength_eq_complementRestrictedLength
    (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.outsideWordLength E (G.restrictOutsideWord E x) =
      G.restrictedWordLength Eᶜ (G.restrictWord Eᶜ x) := by
  classical
  change (Finset.univ.filter fun a : G.OutsideEdge E => x a.1 ≠ 0).card =
    (Finset.univ.filter fun a : G.RestrictedEdge Eᶜ => x a.1 ≠ 0).card
  apply Finset.card_bijective (G.outsideEdgeEquiv E)
    (G.outsideEdgeEquiv E).bijective
  intro a
  simp [outsideEdgeEquiv]

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
    · rw [selectedDegree_zero_of_not_used C.1 v hv]
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
    · exact (mem_usedVertices C.1 u).2 ⟨f, hf, Or.inl h.1⟩
    · exact (mem_usedVertices C.1 u).2 ⟨f, hf, Or.inr h.2⟩
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
    src_mem_used_of_ne_zero C.1 e hex
  have hudst : G.dst e ∈ G.usedVertices C.1 :=
    dst_mem_used_of_ne_zero C.1 e hex
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

theorem restrictCycle_isLinearForest (G : PhysicalGraph) (C : G.CycleWord)
    (E : Finset G.Edge)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    G.IsRestrictedLinearForest E (G.restrictWord E C.1) := by
  refine ⟨G.restrictedCycle_isAcyclic C E hout, ?_⟩
  intro v
  have hcard : G.restrictedSelectedDegree E (G.restrictWord E C.1) v ≤
      G.selectedDegree C.1 v := by
    unfold restrictedSelectedDegree PhysicalGraph.selectedDegree
    apply Finset.card_le_card_of_injOn (fun e : G.RestrictedEdge E => e.1)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rcases he with ⟨he, hi⟩
      refine ⟨?_, hi⟩
      simpa [restrictWord] using he
    · intro e he f hf hef
      exact Subtype.ext hef
  by_cases hv : v ∈ G.usedVertices C.1
  · calc
      G.restrictedSelectedDegree E (G.restrictWord E C.1) v ≤
          G.selectedDegree C.1 v := hcard
      _ = 2 := C.2.2.2.2 v hv
  · calc
      G.restrictedSelectedDegree E (G.restrictWord E C.1) v ≤
          G.selectedDegree C.1 v := hcard
      _ = 0 := selectedDegree_zero_of_not_used C.1 v hv
      _ ≤ 2 := by omega

theorem restrictCycle_boundary_eq (G : PhysicalGraph) (C : G.CycleWord)
    (E : Finset G.Edge) :
    G.restrictedBoundary E (G.restrictWord E C.1) =
      G.outsideBoundary E (G.restrictOutsideWord E C.1) :=
  G.boundaryParts_eq_of_cycle E ⟨C.1, C.2.2.1⟩



theorem restrictCycle_outside_ne_zero (G : PhysicalGraph) (C : G.CycleWord)
    (E : Finset G.Edge)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    G.restrictOutsideWord E C.1 ≠ 0 := by
  intro hz
  obtain ⟨e, he, hx⟩ := hout
  have h := congrFun hz ⟨e, he⟩
  exact hx (by simpa [restrictOutsideWord] using h)

theorem restrictCycle_complement_isLinearForest (G : PhysicalGraph)
    (C : G.CycleWord) (E : Finset G.Edge)
    (hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0) :
    G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ C.1) := by
  obtain ⟨e, he, hx⟩ := hin
  apply G.restrictCycle_isLinearForest C Eᶜ
  exact ⟨e, by simpa using he, hx⟩

theorem restrictCycle_inside_isLinearForest (G : PhysicalGraph)
    (C : G.CycleWord) (E : Finset G.Edge)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    G.IsRestrictedLinearForest E (G.restrictWord E C.1) :=
  G.restrictCycle_isLinearForest C E hout

theorem restrictCycle_boundary_ne_zero (G : PhysicalGraph) (C : G.CycleWord)
    (E : Finset G.Edge)
    (hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    G.restrictedBoundary E (G.restrictWord E C.1) ≠ 0 := by
  intro hzero
  let y := G.extendWord E (G.restrictWord E C.1)
  have hboundary : G.boundary y = 0 := by
    change G.boundary (G.extendWord E (G.restrictWord E C.1)) = 0
    rw [G.restrictedBoundary_eq_hostBoundary_extend]
    exact hzero
  have hsub : ∀ e, y e ≠ 0 → C.1 e ≠ 0 := by
    intro e hy
    by_cases he : e ∈ E
    · simpa [y, extendWord, restrictWord, he] using hy
    · simp [y, extendWord, he] at hy
  have hyne : y ≠ 0 := by
    intro hz
    obtain ⟨e, he, hx⟩ := hin
    have h := congrFun hz e
    exact hx (by simpa [y, extendWord, restrictWord, he] using h)
  have hyC := boundaryZero_subword_eq_cycle G C y hsub hboundary hyne
  obtain ⟨e, heout, hex⟩ := hout
  have hyzero : y e = 0 := by simp [y, extendWord, heout]
  have heq := congrFun hyC e
  rw [hyzero] at heq
  exact hex heq.symm

/-- A cycle meeting both sides contributes its length to the sumset of the
two local linear-forest length sets, indexed by their common nonzero demand. -/
theorem crossingCycle_length_mem_naturalSumset (G : PhysicalGraph)
    (C : G.CycleWord) (E : Finset G.Edge)
    (hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0)
    (hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0) :
    G.wordLength C.1 ∈ Capacity.naturalSumset
      (G.restrictedLinearForestLengths E
        (G.restrictedBoundary E (G.restrictWord E C.1)))
      (G.restrictedLinearForestLengths Eᶜ
        (G.restrictedBoundary E (G.restrictWord E C.1))) := by
  classical
  let t := G.restrictedBoundary E (G.restrictWord E C.1)
  have htnz : t ≠ 0 := G.restrictCycle_boundary_ne_zero C E hin hout
  have hinsideLF := G.restrictCycle_inside_isLinearForest C E hout
  have houtsideLF := G.restrictCycle_complement_isLinearForest C E hin
  have hshared : G.restrictedBoundary Eᶜ (G.restrictWord Eᶜ C.1) = t := by
    rw [← G.outsideBoundary_eq_complementBoundary E C.1,
      ← G.restrictCycle_boundary_eq C E]
  have hinsideLen : G.restrictedWordLength E (G.restrictWord E C.1) ∈
      G.restrictedLinearForestLengths E t := by
    unfold restrictedLinearForestLengths
    apply Finset.mem_image.mpr
    refine ⟨⟨G.restrictWord E C.1, ?_⟩, Finset.mem_univ _, rfl⟩
    exact ⟨rfl, hinsideLF⟩
  have houtsideLen : G.restrictedWordLength Eᶜ (G.restrictWord Eᶜ C.1) ∈
      G.restrictedLinearForestLengths Eᶜ t := by
    unfold restrictedLinearForestLengths
    apply Finset.mem_image.mpr
    refine ⟨⟨G.restrictWord Eᶜ C.1, ?_⟩, Finset.mem_univ _, rfl⟩
    exact ⟨hshared, houtsideLF⟩
  change G.wordLength C.1 ∈ Capacity.naturalSumset
    (G.restrictedLinearForestLengths E t)
    (G.restrictedLinearForestLengths Eᶜ t)
  unfold Capacity.naturalSumset
  apply Finset.mem_image.mpr
  refine ⟨(G.restrictedWordLength E (G.restrictWord E C.1),
      G.restrictedWordLength Eᶜ (G.restrictWord Eᶜ C.1)),
    Finset.mem_product.mpr ⟨hinsideLen, houtsideLen⟩, ?_⟩
  calc
    _ = G.restrictedWordLength E (G.restrictWord E C.1) +
        G.outsideWordLength E (G.restrictOutsideWord E C.1) := by
      rw [G.outsideWordLength_eq_complementRestrictedLength]
    _ = G.wordLength C.1 := (G.wordLength_partition E C.1).symm



end Erdos1016.PhysicalGraph

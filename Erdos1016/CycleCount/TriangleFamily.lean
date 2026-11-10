import Erdos1016.CycleCount.IndependentEdges

set_option autoImplicit false

/-!
# A family of triangles through chosen edges

Let `D` be a set of edges that lie on even subgraphs. Each edge of `D` has a
third vertex next to its head. This module adds the missing third sides as
chords. In the extended graph every edge of `D` lies on a triangle, and every
new chord lies on a triangle whose other two sides are old edges.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.CycleCount
open PhysicalGraph

/-- Three pairwise adjacent vertices carry a cycle word with exactly their
three edges. -/
theorem exists_triangle_cycleWord (H : PhysicalGraph) {u v w : H.Vertex}
    (huv : H.toSimpleGraph.Adj u v) (hvw : H.toSimpleGraph.Adj v w)
    (hwu : H.toSimpleGraph.Adj w u) :
    ∃ T : H.CycleWord, H.wordLength T.1 = 3 ∧
      ∀ f : H.Edge, T.1 f ≠ 0 ↔
        (Nonbacktracking.physicalPair H f = s(u, v) ∨
          Nonbacktracking.physicalPair H f = s(v, w) ∨
          Nonbacktracking.physicalPair H f = s(w, u)) := by
  classical
  have h1 : u ≠ v := huv.ne
  have h2 : v ≠ w := hvw.ne
  have h3 : w ≠ u := hwu.ne
  let p : H.toSimpleGraph.Walk u u :=
    SimpleGraph.Walk.cons huv
      (SimpleGraph.Walk.cons hvw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil))
  have hp : p.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
      simp [h1, h2, h3, h3.symm, h2.symm, h1.symm]
    · simp [h1, h2, h3, h3.symm, h2.symm, h1.symm]
  refine ⟨Nonbacktracking.cycleWordOfWalk H p hp, ?_, ?_⟩
  · have hlen := Nonbacktracking.cycleWordOfWalk_length H p hp
    simpa [p] using hlen
  · intro f
    change Nonbacktracking.walkWord H p f ≠ 0 ↔ _
    rw [Nonbacktracking.walkWord_nonzero_iff]
    simp [p]

/-- The triangle family in a chord extension of `G`. -/
theorem exists_triangle_family (G : PhysicalGraph) (D : Finset G.Edge)
    (hD : ∀ e ∈ D, ∃ y : G.CycleSpace, y.1 e ≠ 0) :
    ∃ (C : Chords G) (F : Finset (addChords G C).CycleWord)
      (y : Fin C.count → (addChords G C).CycleWord),
      F.card ≤ D.card ∧ (D.Nonempty → F.Nonempty) ∧
      (∀ T ∈ F, (addChords G C).wordLength T.1 = 3) ∧
      (∀ e ∈ D, ∃ T ∈ F, T.1 (oldEdge G C e) ≠ 0) ∧
      (∀ j, y j ∈ F) ∧
      (∀ i j, (y j).1 (newEdge G C i) ≠ 0 ↔ i = j) := by
  classical
  have hap : ∀ e : G.Edge, ∃ w : G.Vertex,
      e ∈ D → (w ≠ G.src e ∧ G.toSimpleGraph.Adj (G.dst e) w) := by
    intro e
    by_cases he : e ∈ D
    · obtain ⟨y, hy⟩ := hD e he
      obtain ⟨w, hw⟩ := exists_apex G y e hy
      exact ⟨w, fun _ => hw⟩
    · exact ⟨G.src e, fun h => absurd h he⟩
  choose apex hapex using hap
  let pairs : Finset (Sym2 G.Vertex) :=
    (D.image fun e => s(G.src e, apex e)).filter fun q => q ∉ G.toSimpleGraph.edgeSet
  let pr : Fin pairs.card → Sym2 G.Vertex := fun j => (pairs.equivFin.symm j).1
  have hpr : ∀ j, pr j ∈ pairs := fun j => (pairs.equivFin.symm j).2
  have hprinj : ∀ i j, pr i = pr j → i = j := by
    intro i j h
    exact pairs.equivFin.symm.injective (Subtype.ext h)
  have hrepex : ∀ q : Sym2 G.Vertex, ∃ ab : G.Vertex × G.Vertex, s(ab.1, ab.2) = q := by
    intro q
    exact Sym2.inductionOn q (fun a b => ⟨(a, b), rfl⟩)
  choose rep hrep using hrepex
  have hsrc : ∀ j, ∃ e, e ∈ D ∧ s(G.src e, apex e) = pr j := by
    intro j
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (hpr j)).1
    exact ⟨e, he, heq⟩
  choose ε hεmem hεeq using hsrc
  have hfreshpr : ∀ j, pr j ∉ G.toSimpleGraph.edgeSet :=
    fun j => (Finset.mem_filter.mp (hpr j)).2
  let C : Chords G :=
    { count := pairs.card
      cs := fun j => (rep (pr j)).1
      cd := fun j => (rep (pr j)).2
      ne := by
        intro j hcd
        have h := (hrep (pr j)).trans (hεeq j).symm
        rw [hcd] at h
        rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact (hapex (ε j) (hεmem j)).1 (h2.symm.trans h1)
        · exact (hapex (ε j) (hεmem j)).1 (h1.symm.trans h2)
      fresh := by
        intro j hadj
        apply hfreshpr j
        rw [← hrep (pr j)]
        exact (SimpleGraph.mem_edgeSet _).2 hadj
      distinct := by
        intro i j h
        apply hprinj
        rw [← hrep (pr i), ← hrep (pr j)]
        exact h }
  have hCs : ∀ j : Fin C.count, s(C.cs j, C.cd j) = pr j := fun j => hrep (pr j)
  have htri : ∀ e, e ∈ D → ∃ T : (addChords G C).CycleWord,
      (addChords G C).wordLength T.1 = 3 ∧
      ∀ f : (addChords G C).Edge, T.1 f ≠ 0 ↔
        (Nonbacktracking.physicalPair (addChords G C) f = s(G.src e, G.dst e) ∨
          Nonbacktracking.physicalPair (addChords G C) f = s(G.dst e, apex e) ∨
          Nonbacktracking.physicalPair (addChords G C) f = s(apex e, G.src e)) := by
    intro e he
    have huv : (addChords G C).toSimpleGraph.Adj (G.src e) (G.dst e) :=
      adj_of_endpoints (addChords G C) (oldEdge G C e)
        (Or.inl ⟨src_oldEdge G C e, dst_oldEdge G C e⟩)
    have hvw : (addChords G C).toSimpleGraph.Adj (G.dst e) (apex e) :=
      toSimpleGraph_le_addChords G C (hapex e he).2
    have hwu : (addChords G C).toSimpleGraph.Adj (apex e) (G.src e) := by
      by_cases hadj : s(G.src e, apex e) ∈ G.toSimpleGraph.edgeSet
      · exact (toSimpleGraph_le_addChords G C
          ((SimpleGraph.mem_edgeSet _).1 hadj)).symm
      · have hmem : s(G.src e, apex e) ∈ pairs :=
          Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨e, he, rfl⟩, hadj⟩
        let j : Fin C.count := pairs.equivFin ⟨s(G.src e, apex e), hmem⟩
        have hj : s(C.cs j, C.cd j) = s(G.src e, apex e) := by
          rw [hCs j]
          show (pairs.equivFin.symm (pairs.equivFin ⟨s(G.src e, apex e), hmem⟩)).1 = _
          rw [Equiv.symm_apply_apply]
        have h2 : s(C.cs j, C.cd j) ∈ (addChords G C).toSimpleGraph.edgeSet :=
          (SimpleGraph.mem_edgeSet _).2 (adj_newEdge G C j)
        rw [hj] at h2
        exact ((SimpleGraph.mem_edgeSet _).1 h2).symm
    exact exists_triangle_cycleWord (addChords G C) huv hvw hwu
  choose T hT3 hTval using htri
  let F : Finset (addChords G C).CycleWord := D.attach.image fun e => T e.1 e.2
  refine ⟨C, F, fun j => T (ε j) (hεmem j), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by rw [Finset.card_attach])
  · intro h
    exact (Finset.attach_nonempty_iff.2 h).image _
  · intro T' hT'
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.1 hT'
    exact hT3 e.1 e.2
  · intro e he
    refine ⟨T e he, Finset.mem_image.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact (hTval e he (oldEdge G C e)).2 (Or.inl (physicalPair_oldEdge G C e))
  · intro j
    exact Finset.mem_image.2 ⟨⟨ε j, hεmem j⟩, Finset.mem_attach _ _, rfl⟩
  · intro i j
    rw [hTval, physicalPair_newEdge, hCs i]
    constructor
    · rintro (h | h | h)
      · exfalso
        apply hfreshpr i
        rw [h]
        exact (SimpleGraph.mem_edgeSet _).2
          (adj_of_endpoints G (ε j) (Or.inl ⟨rfl, rfl⟩))
      · exfalso
        apply hfreshpr i
        rw [h]
        exact (SimpleGraph.mem_edgeSet _).2 (hapex (ε j) (hεmem j)).2
      · apply hprinj
        rw [h, ← hεeq j]
        exact Sym2.eq_swap
    · rintro rfl
      right
      right
      rw [← hεeq i]
      exact Sym2.eq_swap

end Erdos1016.CycleCount

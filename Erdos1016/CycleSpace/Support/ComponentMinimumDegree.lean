import Erdos1016.CycleSpace.Support.ActiveComponents

set_option autoImplicit false

/-!
# Minimum degree in the active-edge support

An edge that occurs in a cycle-space word cannot be the only supported edge at
either endpoint: the zero-boundary equation forces the incident support to
have even cardinality.
-/

noncomputable section

namespace Erdos1016.Proof.ActiveComponentMinimumDegree

open Erdos1016
open Erdos1016.Proof.ActiveEdgeUniform
open Erdos1016.Proof.ActivePhysicalComponents

local notation "F₂" => ZMod 2

/-- If an active edge is incident to a vertex, another distinct edge at that
vertex occurs in a witnessing cycle-space word. -/
theorem exists_other_active_incident (H : PhysicalGraph) (e : H.Edge)
    (v : H.Vertex) (hactive : ActiveEdge H e) (hinc : H.incident e v) :
    ∃ f : H.Edge, f ≠ e ∧ H.incident f v ∧ ∃ x : H.CycleSpace, x.1 f ≠ 0 := by
  obtain ⟨x, hxe⟩ := hactive
  by_contra hno
  have hzero : ∀ f : H.Edge, f ≠ e → H.incident f v → x.1 f = 0 := by
    intro f hne hfi
    by_contra hval
    exact hno ⟨f, hne, hfi, x, hval⟩
  have hterm (f : H.Edge) :
      ((if H.src f = v then x.1 f else 0) +
       (if H.dst f = v then x.1 f else 0)) =
      (if f = e then x.1 e else 0) := by
    by_cases hfe : f = e
    · subst f
      rcases hinc with hs | ht
      · have hdst : H.dst e ≠ v := by
          intro h
          exact H.noLoops e (hs.trans h.symm)
        simp [hs, hdst]
      · have hsrc : H.src e ≠ v := by
          intro h
          exact H.noLoops e (h.trans ht.symm)
        simp [hsrc, ht]
    · by_cases hs : H.src f = v <;> by_cases ht : H.dst f = v
      · have hxzero := hzero f hfe (Or.inl hs)
        simp [hfe, hs, ht, hxzero]
      · have hxzero := hzero f hfe (Or.inl hs)
        simp [hfe, hs, ht, hxzero]
      · have hxzero := hzero f hfe (Or.inr ht)
        simp [hfe, hs, ht, hxzero]
      · simp [hfe, hs, ht]
  have hboundary : H.boundary x.1 v = x.1 e := by
    dsimp [PhysicalGraph.boundary]
    calc
      (∑ f : H.Edge,
          ((if H.src f = v then x.1 f else 0) +
           (if H.dst f = v then x.1 f else 0))) =
          ∑ f : H.Edge, if f = e then x.1 e else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        exact hterm f
      _ = x.1 e := by simp
  have hzeroBoundary := congrFun x.2 v
  rw [hboundary] at hzeroBoundary
  rw [hxe] at hzeroBoundary
  exact one_ne_zero hzeroBoundary

/-- Every active edge incident to `v` forces degree at least two. -/
theorem degree_ge_two_of_active_incident (H : PhysicalGraph) (e : H.Edge)
    (v : H.Vertex) (hactive : ActiveEdge H e) (hinc : H.incident e v) :
    2 ≤ H.degree v := by
  obtain ⟨f, hfe, hfi, x, hxf⟩ :=
    exists_other_active_incident H e v hactive hinc
  classical
  let S : Finset H.Edge := Finset.univ.filter fun g =>
    (fun _ : H.Edge => (1 : F₂)) g ≠ 0 ∧ H.incident g v
  have he : e ∈ S := by
    simp [S, hinc]
  have hf : f ∈ S := by
    simp [S, hfi]
  have hsub : ({e, f} : Finset H.Edge) ⊆ S := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  have hcard : ({e, f} : Finset H.Edge).card = 2 := Finset.card_pair hfe.symm
  change 2 ≤ (Finset.univ.filter fun g : H.Edge =>
    (fun _ : H.Edge => (1 : F₂)) g ≠ 0 ∧ H.incident g v).card
  calc
    2 = ({e, f} : Finset H.Edge).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hsub



/-- Every physical edge retained by `activeSubgraph G` remains active in the
cycle space of that restricted graph. -/
theorem activeSubgraph_edge_active (G : PhysicalGraph)
    (e : (activeSubgraph G).Edge) :
    ActiveEdge (activeSubgraph G) e := by
  classical
  let E := activeEdges G
  let e₀ := G.restrictedEdgeEquiv E e
  have hglobal : ActiveEdge G e₀.1 := by
    apply (mem_activeEdges_iff G e₀.1).1
    exact e₀.2
  obtain ⟨x, hx⟩ := hglobal
  have hext : G.extendWord E (G.restrictWord E x.1) = x.1 := by
    funext a
    by_cases ha : a ∈ E
    · simp [PhysicalGraph.extendWord, PhysicalGraph.restrictWord, ha]
    · have hz := cycle_word_zero_off_active_edges G x a (by simpa [E] using ha)
      simp [PhysicalGraph.extendWord, ha, hz]
  have hboundary : G.restrictedBoundary E (G.restrictWord E x.1) = 0 := by
    change G.boundary (G.extendWord E (G.restrictWord E x.1)) = 0
    rw [hext]
    exact x.2
  let z : G.RestrictedCycleSpace E := ⟨G.restrictWord E x.1, hboundary⟩
  let y : (activeSubgraph G).CycleSpace :=
    (G.restrictPhysicalCycleEquiv E).symm z
  refine ⟨y, ?_⟩
  have hy := congrArg Subtype.val
    ((G.restrictPhysicalCycleEquiv E).apply_symm_apply z)
  have hcoord := congrFun hy e₀
  change y.1 e = 1
  dsimp [y, z] at hcoord ⊢
  simpa [PhysicalGraph.restrictPhysicalWordEquiv,
    PhysicalGraph.restrictedEdgeEquiv] using hcoord.trans hx

/-- Every vertex incident to an edge of the active subgraph has degree at
least two there. -/
theorem activeSubgraph_degree_ge_two_of_incident (G : PhysicalGraph)
    (e : (activeSubgraph G).Edge) (v : (activeSubgraph G).Vertex)
    (hinc : (activeSubgraph G).incident e v) :
    2 ≤ (activeSubgraph G).degree v :=
  degree_ge_two_of_active_incident (activeSubgraph G) e v
    (activeSubgraph_edge_active G e) hinc

end Erdos1016.Proof.ActiveComponentMinimumDegree

end

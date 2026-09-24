import Erdos1016.Boundary.PhysicalGraph

set_option autoImplicit false

/-!
# Actual cut-edge labels versus degree-two boundary vertices

For a cubic owner and a min-degree-two induced shore, each boundary vertex has
exactly one missing incidence. This module proves the bijection between the
pin coordinates of the one-apex construction and the degree-two vertices used
by the manuscript's boundary-average notation.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

open BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def traceInsideEdgesAt (G : PhysicalGraph) (S : Finset G.Vertex) (v : G.Vertex) :
    Finset G.Edge :=
  Finset.univ.filter fun e => G.incident e v ∧ G.src e ∈ S ∧ G.dst e ∈ S

def traceCutEdgesAt (G : PhysicalGraph) (S : Finset G.Vertex) (v : G.Vertex) :
    Finset G.Edge :=
  Finset.univ.filter fun e => G.incident e v ∧
    ((G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S))

def traceInsideDegree (G : PhysicalGraph) (S : Finset G.Vertex) (v : G.Vertex) : ℕ :=
  (G.traceInsideEdgesAt S v).card

def traceCutDegree (G : PhysicalGraph) (S : Finset G.Vertex) (v : G.Vertex) : ℕ :=
  (G.traceCutEdgesAt S v).card

theorem trace_degree_split (G : PhysicalGraph) (S : Finset G.Vertex)
    (v : G.Vertex) (hv : v ∈ S) :
    G.traceInsideDegree S v + G.traceCutDegree S v = G.degree v := by
  have hd : Disjoint (G.traceInsideEdgesAt S v) (G.traceCutEdgesAt S v) := by
    apply Finset.disjoint_left.2
    intro e he hf
    simp only [traceInsideEdgesAt, traceCutEdgesAt, Finset.mem_filter,
      Finset.mem_univ, true_and] at he hf
    rcases hf.2 with h | h
    · exact h.2 he.2.2
    · exact h.1 he.2.1
  have hu : G.traceInsideEdgesAt S v ∪ G.traceCutEdgesAt S v =
      Finset.univ.filter (fun e => G.incident e v) := by
    ext e
    simp only [traceInsideEdgesAt, traceCutEdgesAt, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hi
      have hm : G.src e ∈ S ∨ G.dst e ∈ S := by
        rcases hi with h | h
        · exact Or.inl (h.symm ▸ hv)
        · exact Or.inr (h.symm ▸ hv)
      by_cases hs : G.src e ∈ S <;> by_cases ht : G.dst e ∈ S <;> tauto
  unfold traceInsideDegree traceCutDegree
  rw [← Finset.card_union_of_disjoint hd, hu]
  simp [degree, selectedDegree]

theorem traceCutDegree_le_one (G : PhysicalGraph) (S : Finset G.Vertex)
    (v : G.Vertex) (hv : v ∈ S) (hc : G.degree v = 3)
    (hmin : 2 ≤ G.traceInsideDegree S v) :
    G.traceCutDegree S v ≤ 1 := by
  have h := G.trace_degree_split S v hv
  omega

theorem traceCutDegree_pos_iff_insideDegree_two (G : PhysicalGraph)
    (S : Finset G.Vertex) (v : G.Vertex) (hv : v ∈ S)
    (hc : G.degree v = 3) (hmin : 2 ≤ G.traceInsideDegree S v) :
    0 < G.traceCutDegree S v ↔ G.traceInsideDegree S v = 2 := by
  have h := G.trace_degree_split S v hv
  omega

/-- A cut edge meets exactly one shore vertex. -/
theorem insidePin_eq_iff_incident (G : PhysicalGraph) (S : Finset G.Vertex)
    (e : Network.Shore.CutEdge G.traceNetwork S)
    (v : Network.Shore.InsideVertex S) :
    Network.Shore.insidePin G.traceNetwork S e = v ↔ G.incident e.1 v.1 := by
  by_cases hs : G.src e.1 ∈ S
  · have hd : G.dst e.1 ∉ S := by
      rcases e.2 with h | h
      · exact h.2
      · exact False.elim (h.1 hs)
    constructor
    · intro h
      left
      have heq := congrArg Subtype.val h
      simpa [Network.Shore.insidePin, traceNetwork, hs] using heq
    · intro h
      apply Subtype.ext
      rcases h with h | h
      · simpa [Network.Shore.insidePin, traceNetwork, hs] using h
      · exact False.elim (hd (h.symm ▸ v.2))
  · have hd : G.dst e.1 ∈ S := by
      rcases e.2 with h | h
      · exact False.elim (hs h.1)
      · exact h.2
    constructor
    · intro h
      right
      have heq := congrArg Subtype.val h
      simpa [Network.Shore.insidePin, traceNetwork, hs] using heq
    · intro h
      apply Subtype.ext
      rcases h with h | h
      · exact False.elim (hs (h.symm ▸ v.2))
      · simpa [Network.Shore.insidePin, traceNetwork, hs] using h

/-- The one-missing-incidence fact is proved from ORIGINAL owner degree. -/
theorem insidePin_injective_of_cubic (G : PhysicalGraph) (S : Finset G.Vertex)
    (hc : ∀ v ∈ S, G.degree v = 3)
    (hmin : ∀ v ∈ S, 2 ≤ G.traceInsideDegree S v) :
    Function.Injective (Network.Shore.insidePin G.traceNetwork S) := by
  intro e f hef
  let v := Network.Shore.insidePin G.traceNetwork S e
  have he : e.1 ∈ G.traceCutEdgesAt S v.1 := by
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _,
      (G.insidePin_eq_iff_incident S e v).1 rfl, e.2⟩
  have hf : f.1 ∈ G.traceCutEdgesAt S v.1 := by
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_univ _,
      (G.insidePin_eq_iff_incident S f v).1 hef.symm, f.2⟩
  have hbound := G.traceCutDegree_le_one S v.1 v.2 (hc _ v.2) (hmin _ v.2)
  apply Subtype.ext
  by_contra hne
  have hsub : ({e.1, f.1} : Finset G.Edge) ⊆ G.traceCutEdgesAt S v.1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hcard
  change (G.traceCutEdgesAt S v.1).card ≤ 1 at hbound
  omega

/-- Image of the actual cut-edge endpoint map is precisely the degree-two
vertex set of the induced shore. -/
theorem exists_pin_iff_insideDegree_two (G : PhysicalGraph)
    (S : Finset G.Vertex) (hc : ∀ v ∈ S, G.degree v = 3)
    (hmin : ∀ v ∈ S, 2 ≤ G.traceInsideDegree S v)
    (v : Network.Shore.InsideVertex S) :
    (∃ e : Network.Shore.CutEdge G.traceNetwork S,
      Network.Shore.insidePin G.traceNetwork S e = v) ↔
      G.traceInsideDegree S v.1 = 2 := by
  rw [← G.traceCutDegree_pos_iff_insideDegree_two S v.1 v.2 (hc _ v.2) (hmin _ v.2)]
  change (∃ e : Network.Shore.CutEdge G.traceNetwork S, _) ↔
    0 < (G.traceCutEdgesAt S v.1).card
  rw [Finset.card_pos]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.1, Finset.mem_filter.2 ?_⟩
    exact ⟨Finset.mem_univ _, (G.insidePin_eq_iff_incident S e v).1 he, e.2⟩
  · rintro ⟨e, he⟩
    obtain ⟨_, hi, hcut⟩ := Finset.mem_filter.1 he
    refine ⟨⟨e, hcut⟩, ?_⟩
    exact (G.insidePin_eq_iff_incident S ⟨e, hcut⟩ v).2 hi

/-- The actual pins and the degree-two vertices are bijective, not merely
of the same dimension or asymptotic size. -/
def cutPinEquivDegreeTwo (G : PhysicalGraph) (S : Finset G.Vertex)
    (hc : ∀ v ∈ S, G.degree v = 3)
    (hmin : ∀ v ∈ S, 2 ≤ G.traceInsideDegree S v) :
    Network.Shore.CutEdge G.traceNetwork S ≃
      {v : Network.Shore.InsideVertex S // G.traceInsideDegree S v.1 = 2} :=
  Equiv.ofBijective
    (fun e => ⟨Network.Shore.insidePin G.traceNetwork S e,
      (G.exists_pin_iff_insideDegree_two S hc hmin _).1 ⟨e, rfl⟩⟩)
    ⟨by
      intro e f h
      apply G.insidePin_injective_of_cubic S hc hmin
      exact congrArg Subtype.val h,
     by
      intro v
      obtain ⟨e, he⟩ := (G.exists_pin_iff_insideDegree_two S hc hmin v.1).2 v.2
      exact ⟨e, Subtype.ext he⟩⟩

end Erdos1016.PhysicalGraph

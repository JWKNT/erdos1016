import Erdos1016.Graph.CutPacking
import Erdos1016.Extremal.Capacity.CycleLengths

set_option autoImplicit false

noncomputable section
open scoped BigOperators
namespace Erdos1016

private theorem boundary_eq_selectedDegree_cast (G : PhysicalGraph) (x : G.Word)
    (v : G.Vertex) : G.boundary x v = (G.selectedDegree x v : F₂) := by
  have binary (a : F₂) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  change (∑ e, ((if G.src e = v then x e else 0) +
    (if G.dst e = v then x e else 0))) = _
  unfold PhysicalGraph.selectedDegree
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rcases binary (x e) with hx | hx
  · simp [hx]
  · by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v
    all_goals try simp [hx, hs, hd, PhysicalGraph.incident]
    all_goals exact False.elim (G.noLoops e (hs.trans hd.symm))

/-- Edge set in the union of a finite family of cycle supports. -/
def witnessSupportEdges (G : PhysicalGraph) (F : Finset G.CycleWord) : Finset G.Edge :=
  F.biUnion fun C => G.edgeSupport C.1

/-- Literal physical support graph on the host vertex set, with just the
physical edge labels used by at least one witness. -/
def witnessSupportGraph (G : PhysicalGraph) (F : Finset G.CycleWord) : PhysicalGraph where
  vertexCount := G.vertexCount
  edgeCount := (witnessSupportEdges G F).card
  src := fun e => G.src ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
  dst := fun e => G.dst ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
  noLoops e := G.noLoops ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
  simple e f h := by
    have he := G.simple ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
        ((Finset.equivFin (witnessSupportEdges G F)).symm f).1
    apply (Finset.equivFin (witnessSupportEdges G F)).symm.injective
    apply Subtype.ext
    rcases h with h | h
    · exact he (Or.inl h)
    · exact he (Or.inr h)

/-- The union graph is an actual edge subgraph of its host; its vertex map is
identity and its edge map records each chosen support label. -/
def witnessSupportSubgraph (G : PhysicalGraph) (F : Finset G.CycleWord) :
    ActualSubgraph G where
  graph := witnessSupportGraph G F
  vertexMap := Function.Embedding.refl _
  edgeMap := {
    toFun := fun e => ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
    inj' := by
      intro e f h
      apply (Finset.equivFin (witnessSupportEdges G F)).symm.injective
      exact Subtype.ext h
  }
  src_commutes := by intro e; rfl
  dst_commutes := by intro e; rfl

/-- Every edge of a chosen witness occurs among the support graph's edges. -/
theorem witnessSupport_edge_mem (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) {e : G.Edge}
    (he : e ∈ G.edgeSupport C.1) : e ∈ witnessSupportEdges G F := by
  exact Finset.mem_biUnion.mpr ⟨C, hC, he⟩

/-- Restrict a chosen host word to the literal union support graph. -/
def restrictWitness (G : PhysicalGraph) (F : Finset G.CycleWord)
    (C : G.CycleWord) : (witnessSupportGraph G F).Word :=
  (witnessSupportSubgraph G F).restrict C.1

@[simp] theorem restrictWitness_edge (G : PhysicalGraph) (F : Finset G.CycleWord)
    (C : G.CycleWord) (e : (witnessSupportGraph G F).Edge) :
    restrictWitness G F C e =
      C.1 (((Finset.equivFin (witnessSupportEdges G F)).symm e).1) := rfl

/-- The restricted word remains nonzero: every nonzero host edge of a witness
is included in the support graph. -/
theorem restrictWitness_ne_zero (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) : restrictWitness G F C ≠ 0 := by
  intro hz
  have hnonzero := C.2.1
  have hex : ∃ e : G.Edge, C.1 e ≠ 0 := by
    by_contra hn
    apply hnonzero
    funext e
    have he := not_exists.mp hn e
    exact not_ne_iff.mp he
  obtain ⟨e, he⟩ := hex
  have hm := witnessSupport_edge_mem G F hC
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
  let ew : (witnessSupportGraph G F).Edge := (Finset.equivFin (witnessSupportEdges G F)) ⟨e, hm⟩
  have hval : restrictWitness G F C ew = C.1 e := by
    simp [restrictWitness, ActualSubgraph.restrict, witnessSupportSubgraph, ew]
  rw [hz] at hval
  exact he (hval.symm.trans (by simp))

/-- Adjacency in the restricted word is exactly adjacency in the host word. -/
theorem restrictWitness_selectedGraph (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) :
    (witnessSupportGraph G F).selectedGraph (restrictWitness G F C) =
      G.selectedGraph C.1 := by
  classical
  ext u v
  constructor
  · rintro ⟨e, he, h | h⟩
    · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
      exact ⟨q, by simpa [restrictWitness_edge] using he,
        Or.inl ⟨h.1, h.2⟩⟩
    · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
      exact ⟨q, by simpa [restrictWitness_edge] using he,
        Or.inr ⟨h.1, h.2⟩⟩
  · rintro ⟨e, he, h | h⟩
    · have hes : e ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      let q : (witnessSupportGraph G F).Edge :=
        (Finset.equivFin (witnessSupportEdges G F)) ⟨e, hes⟩
      exact ⟨q, by simpa [restrictWitness, ActualSubgraph.restrict,
        witnessSupportSubgraph, q] using he,
        Or.inl ⟨by simpa [witnessSupportGraph, q] using h.1,
          by simpa [witnessSupportGraph, q] using h.2⟩⟩
    · have hes : e ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      let q : (witnessSupportGraph G F).Edge :=
        (Finset.equivFin (witnessSupportEdges G F)) ⟨e, hes⟩
      exact ⟨q, by simpa [restrictWitness, ActualSubgraph.restrict,
        witnessSupportSubgraph, q] using he,
        Or.inr ⟨by simpa [witnessSupportGraph, q] using h.1,
          by simpa [witnessSupportGraph, q] using h.2⟩⟩

/-- The used vertex set is unchanged by restriction to the support graph. -/
theorem restrictWitness_usedVertices (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) :
    (witnessSupportGraph G F).usedVertices (restrictWitness G F C) =
      G.usedVertices C.1 := by
  classical
  ext v
  change v ∈ Finset.univ.filter
      (fun v => ∃ e : (witnessSupportGraph G F).Edge,
        restrictWitness G F C e ≠ 0 ∧ (witnessSupportGraph G F).incident e v) ↔
    v ∈ Finset.univ.filter
      (fun v => ∃ e : G.Edge, C.1 e ≠ 0 ∧ G.incident e v)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he, h | h⟩
    · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
      exact ⟨q, by simpa [restrictWitness_edge] using he,
        Or.inl (by simpa [witnessSupportGraph] using h)⟩
    · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
      exact ⟨q, by simpa [restrictWitness_edge] using he,
        Or.inr (by simpa [witnessSupportGraph] using h)⟩
  · rintro ⟨e, he, h | h⟩
    · have hes : e ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      let q : (witnessSupportGraph G F).Edge :=
        (Finset.equivFin (witnessSupportEdges G F)) ⟨e, hes⟩
      exact ⟨q, by simpa [restrictWitness, ActualSubgraph.restrict,
        witnessSupportSubgraph, q] using he,
        Or.inl (by simpa [witnessSupportGraph, q] using h)⟩
    · have hes : e ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      let q : (witnessSupportGraph G F).Edge :=
        (Finset.equivFin (witnessSupportEdges G F)) ⟨e, hes⟩
      exact ⟨q, by simpa [restrictWitness, ActualSubgraph.restrict,
        witnessSupportSubgraph, q] using he,
        Or.inr (by simpa [witnessSupportGraph, q] using h)⟩

/-- The edge-degree of the restricted word agrees with the host degree. -/
theorem restrictWitness_selectedDegree (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) (v : G.Vertex) :
    (witnessSupportGraph G F).selectedDegree (restrictWitness G F C) v =
      G.selectedDegree C.1 v := by
  classical
  let W := witnessSupportGraph G F
  let D := witnessSupportSubgraph G F
  let y := restrictWitness G F C
  let f : {e : W.Edge // y e ≠ 0 ∧ W.incident e v} →
      {e : G.Edge // C.1 e ≠ 0 ∧ G.incident e v} := fun e =>
    ⟨D.edgeMap e.1, by
      constructor
      · simpa [y, restrictWitness, D, ActualSubgraph.restrict,
          witnessSupportSubgraph] using e.2.1
      · rcases e.2.2 with h | h
        · exact Or.inl (D.src_commutes e.1 |>.symm.trans h)
        · exact Or.inr (D.dst_commutes e.1 |>.symm.trans h)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply (Finset.equivFin (witnessSupportEdges G F)).symm.injective
      apply Subtype.ext
      have hmap := congrArg Subtype.val hab
      simpa [D, witnessSupportSubgraph] using hmap
    · intro e
      have hes : e.1 ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2.1⟩)
      let q : W.Edge := (Finset.equivFin (witnessSupportEdges G F)) ⟨e.1, hes⟩
      refine ⟨⟨q, ?_, ?_⟩, ?_⟩
      · simpa [y, restrictWitness, D, ActualSubgraph.restrict,
          witnessSupportSubgraph, q] using e.2.1
      · rcases e.2.2 with h | h
        · exact Or.inl (by simpa [W, witnessSupportGraph, q] using h)
        · exact Or.inr (by simpa [W, witnessSupportGraph, q] using h)
      · apply Subtype.ext
        change ((Finset.equivFin (witnessSupportEdges G F)).symm q).1 = e.1
        simp [q]
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  have hcard' : Fintype.card {e : W.Edge // y e ≠ 0 ∧ W.incident e v} =
      Fintype.card {e : G.Edge // C.1 e ≠ 0 ∧ G.incident e v} := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  change (Finset.univ.filter (fun e : W.Edge => y e ≠ 0 ∧ W.incident e v)).card =
    (Finset.univ.filter (fun e : G.Edge => C.1 e ≠ 0 ∧ G.incident e v)).card
  rw [← Fintype.card_coe (Finset.univ.filter
      (fun e : W.Edge => y e ≠ 0 ∧ W.incident e v)),
    ← Fintype.card_coe (Finset.univ.filter
      (fun e : G.Edge => C.1 e ≠ 0 ∧ G.incident e v))]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcard'

/-- Restriction preserves the number of selected physical edges. -/
theorem restrictWitness_wordLength (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) :
    (witnessSupportGraph G F).wordLength (restrictWitness G F C) =
      G.wordLength C.1 := by
  classical
  let W := witnessSupportGraph G F
  let D := witnessSupportSubgraph G F
  let y := restrictWitness G F C
  let f : {e : W.Edge // y e ≠ 0} → {e : G.Edge // C.1 e ≠ 0} := fun e =>
    ⟨D.edgeMap e.1, by
      simpa [y, restrictWitness, D, ActualSubgraph.restrict,
        witnessSupportSubgraph] using e.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply (Finset.equivFin (witnessSupportEdges G F)).symm.injective
      apply Subtype.ext
      have hmap := congrArg Subtype.val hab
      simpa [D, witnessSupportSubgraph] using hmap
    · intro e
      have hes : e.1 ∈ witnessSupportEdges G F :=
        witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩)
      let q : W.Edge := (Finset.equivFin (witnessSupportEdges G F)) ⟨e.1, hes⟩
      refine ⟨⟨q, ?_⟩, ?_⟩
      · simpa [y, restrictWitness, D, ActualSubgraph.restrict,
          witnessSupportSubgraph, q] using e.2
      · apply Subtype.ext
        change ((Finset.equivFin (witnessSupportEdges G F)).symm q).1 = e.1
        simp [q]
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  have hcard' : Fintype.card {e : W.Edge // y e ≠ 0} =
      Fintype.card {e : G.Edge // C.1 e ≠ 0} := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  change (Finset.univ.filter (fun e : W.Edge => y e ≠ 0)).card =
    (Finset.univ.filter (fun e : G.Edge => C.1 e ≠ 0)).card
  rw [← Fintype.card_coe (Finset.univ.filter (fun e : W.Edge => y e ≠ 0)),
    ← Fintype.card_coe (Finset.univ.filter (fun e : G.Edge => C.1 e ≠ 0))]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hcard'

/-- A selected witness cycle transports to a cycle word on its support graph. -/
def restrictWitnessCycle (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) : (witnessSupportGraph G F).CycleWord := by
  let W := witnessSupportGraph G F
  let y := restrictWitness G F C
  refine ⟨y, ?_⟩
  refine ⟨restrictWitness_ne_zero G F hC, ?_, ?_, ?_⟩
  · funext v
    rw [boundary_eq_selectedDegree_cast, restrictWitness_selectedDegree G F hC,
      ← boundary_eq_selectedDegree_cast]
    exact congrArg (fun b : G.Demand => b v) C.2.2.1
  · rw [restrictWitness_selectedGraph G F hC,
      restrictWitness_usedVertices G F hC]
    exact C.2.2.2.1
  · intro v hv
    rw [restrictWitness_selectedDegree G F hC]
    have hv' : v ∈ G.usedVertices C.1 := by
      rw [← restrictWitness_usedVertices G F hC]
      exact hv
    exact C.2.2.2.2 v hv'

/-- Chosen witnesses in the finite family survive with their lengths on the
literal support graph. -/
theorem initialCoverage_of_witnessFamily (G : PhysicalGraph)
    (F : Finset G.CycleWord) (L : ℕ)
    (witness : ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ L →
      ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ) :
    (witnessSupportGraph G F).InitialCoverage L := by
  classical
  intro ℓ hℓ
  rcases Finset.mem_Icc.1 hℓ with ⟨hlo, hhi⟩
  obtain ⟨C, hC, hlen⟩ := witness ℓ hlo hhi
  have hlen' := restrictWitness_wordLength G F hC
  unfold PhysicalGraph.cycleLengths
  exact Finset.mem_image.2 ⟨restrictWitnessCycle G F hC,
    Finset.mem_univ _, by
      change (witnessSupportGraph G F).wordLength
        (restrictWitness G F C) = ℓ
      exact hlen'.trans hlen⟩



@[simp] theorem witnessSupportSubgraph_vertexMap (G : PhysicalGraph)
    (F : Finset G.CycleWord) (v : (witnessSupportGraph G F).Vertex) :
    (witnessSupportSubgraph G F).vertexMap v = v := rfl

@[simp] theorem witnessSupportSubgraph_edgeMap_val (G : PhysicalGraph)
    (F : Finset G.CycleWord) (e : (witnessSupportGraph G F).Edge) :
    ((witnessSupportSubgraph G F).edgeMap e).1 =
      ((Finset.equivFin (witnessSupportEdges G F)).symm e).1 := rfl

end Erdos1016

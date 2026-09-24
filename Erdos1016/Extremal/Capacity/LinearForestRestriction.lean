import Erdos1016.Extremal.Capacity.LinearForestCapacity

set_option autoImplicit false

/-!
# Edge restriction lemmas for local linear-forest capacity

An edge restriction is represented by a finite subtype of the host's physical
edge labels. This avoids identifying parallel labels and keeps all endpoint
data inherited from the host.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

abbrev RestrictedEdge (G : PhysicalGraph) (E : Finset G.Edge) := {e : G.Edge // e ∈ E}

abbrev RestrictedWord (G : PhysicalGraph) (E : Finset G.Edge) :=
  G.RestrictedEdge E → F₂

def restrictWord (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.RestrictedWord E := fun e => x e.1

def extendWord (G : PhysicalGraph) (E : Finset G.Edge) (x : G.RestrictedWord E) :
    G.Word := fun e => if h : e ∈ E then x ⟨e, h⟩ else 0

def extendWordLinear (G : PhysicalGraph) (E : Finset G.Edge) :
    G.RestrictedWord E →ₗ[F₂] G.Word where
  toFun := G.extendWord E
  map_add' x y := by
    funext e
    by_cases h : e ∈ E <;> simp [extendWord, h]
  map_smul' a x := by
    funext e
    by_cases h : e ∈ E <;> simp [extendWord, h]

/-- Boundary on the edge-subgraph is the host boundary after extension by zero.
This definition uses the exact inherited endpoint labels. -/
def restrictedBoundary (G : PhysicalGraph) (E : Finset G.Edge) :
    G.RestrictedWord E →ₗ[F₂] G.Demand :=
  G.boundary.comp (G.extendWordLinear E)

abbrev RestrictedCycleSpace (G : PhysicalGraph) (E : Finset G.Edge) :=
  LinearMap.ker (G.restrictedBoundary E)

def restrictedCycleRank (G : PhysicalGraph) (E : Finset G.Edge) : ℕ :=
  Module.finrank F₂ (G.RestrictedCycleSpace E)

abbrev OutsideEdge (G : PhysicalGraph) (E : Finset G.Edge) :=
  {e : G.Edge // e ∉ E}

abbrev OutsideWord (G : PhysicalGraph) (E : Finset G.Edge) :=
  G.OutsideEdge E → F₂

def restrictOutsideWord (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.OutsideWord E := fun e => x e.1

def extendOutsideWord (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.OutsideWord E) : G.Word := fun e =>
  if h : e ∈ E then 0 else x ⟨e, h⟩

def extendOutsideLinear (G : PhysicalGraph) (E : Finset G.Edge) :
    G.OutsideWord E →ₗ[F₂] G.Word where
  toFun := G.extendOutsideWord E
  map_add' x y := by
    funext e
    by_cases h : e ∈ E <;> simp [extendOutsideWord, h]
  map_smul' a x := by
    funext e
    by_cases h : e ∈ E <;> simp [extendOutsideWord, h]

def outsideBoundary (G : PhysicalGraph) (E : Finset G.Edge) :
    G.OutsideWord E →ₗ[F₂] G.Demand :=
  G.boundary.comp (G.extendOutsideLinear E)

theorem extend_inside_add_outside (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    G.extendWord E (G.restrictWord E x) +
      G.extendOutsideWord E (G.restrictOutsideWord E x) = x := by
  funext e
  by_cases h : e ∈ E
  · simp [extendWord, extendOutsideWord, restrictWord, h]
  · simp [extendWord, extendOutsideWord, restrictOutsideWord, h]

theorem boundary_inside_add_outside (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    G.restrictedBoundary E (G.restrictWord E x) +
      G.outsideBoundary E (G.restrictOutsideWord E x) = G.boundary x := by
  change G.boundary (G.extendWord E (G.restrictWord E x)) +
    G.boundary (G.extendOutsideWord E (G.restrictOutsideWord E x)) = _
  rw [← map_add]
  congr 1
  exact G.extend_inside_add_outside E x

def restrictOutsideLinear (G : PhysicalGraph) (E : Finset G.Edge) :
    G.Word →ₗ[F₂] G.OutsideWord E where
  toFun := G.restrictOutsideWord E
  map_add' x y := by funext e; rfl
  map_smul' a x := by funext e; rfl

def outsideCycleProjection (G : PhysicalGraph) (E : Finset G.Edge) :
    G.CycleSpace →ₗ[F₂] G.OutsideWord E :=
  (G.restrictOutsideLinear E).comp G.CycleSpace.subtype

@[simp] theorem outsideCycleProjection_apply (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.CycleSpace) (e : G.OutsideEdge E) :
    G.outsideCycleProjection E x e = x.1 e.1 := rfl

def extendCycleLinear (G : PhysicalGraph) (E : Finset G.Edge) :
    G.RestrictedCycleSpace E →ₗ[F₂] G.CycleSpace :=
  LinearMap.codRestrict G.CycleSpace
    ((G.extendWordLinear E).comp (G.RestrictedCycleSpace E).subtype)
    (fun x => by
      change G.restrictedBoundary E x.1 = 0
      exact x.2)

theorem extend_restrict_of_outside_zero (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) (hx : ∀ e, e ∉ E → x e = 0) :
    G.extendWord E (G.restrictWord E x) = x := by
  funext e
  by_cases he : e ∈ E
  · simp [extendWord, restrictWord, he]
  · simp [extendWord, he, hx e he]

theorem outsideCycleProjection_extendCycle (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedCycleSpace E) : G.outsideCycleProjection E
      (G.extendCycleLinear E x) = 0 := by
  change G.restrictOutsideWord E (G.extendWord E x.1) = 0
  funext e
  simp [restrictOutsideWord, extendWord, e.2]

def restrictedCycleSpaceEquivOutsideKernel (G : PhysicalGraph) (E : Finset G.Edge) :
    G.RestrictedCycleSpace E ≃ₗ[F₂] LinearMap.ker (G.outsideCycleProjection E) where
  toFun x := ⟨G.extendCycleLinear E x, G.outsideCycleProjection_extendCycle E x⟩
  invFun y := ⟨G.restrictWord E y.1.1, by
    change G.boundary (G.extendWord E (G.restrictWord E y.1.1)) = 0
    have hout : ∀ e, e ∉ E → y.1.1 e = 0 := by
      intro e he
      have h := congrFun y.2 ⟨e, he⟩
      rw [G.outsideCycleProjection_apply] at h
      exact h
    rw [G.extend_restrict_of_outside_zero E y.1.1 hout]
    exact y.1.2⟩
  left_inv x := by
    apply Subtype.ext
    change G.restrictWord E (G.extendWord E x.1) = x.1
    funext e
    simp [restrictWord, extendWord]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact G.extend_restrict_of_outside_zero E y.1.1 (by
      intro e he
      have h := congrFun y.2 ⟨e, he⟩
      rw [G.outsideCycleProjection_apply] at h
      exact h)
  map_add' x z := Subtype.ext (map_add (G.extendCycleLinear E) x z)
  map_smul' a x := Subtype.ext (map_smul (G.extendCycleLinear E) a x)

theorem outsideProjection_rank_add_restrictedCycleRank
    (G : PhysicalGraph) (E : Finset G.Edge) :
    Module.finrank F₂ (LinearMap.range (G.outsideCycleProjection E)) +
      G.restrictedCycleRank E = G.cycleRank := by
  have heq := (G.restrictedCycleSpaceEquivOutsideKernel E).finrank_eq
  unfold restrictedCycleRank PhysicalGraph.cycleRank
  rw [heq]
  exact LinearMap.finrank_range_add_finrank_ker (G.outsideCycleProjection E)





/-- The restricted selected graph and degree retain the host's vertices and
the individual host labels in `E`. -/
def restrictedSelectedGraph (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) : SimpleGraph G.Vertex where
  Adj u v := ∃ e : G.RestrictedEdge E, x e ≠ 0 ∧
    ((G.src e.1 = u ∧ G.dst e.1 = v) ∨ (G.src e.1 = v ∧ G.dst e.1 = u))
  symm := by
    intro u v h
    rcases h with ⟨e, hx, h | h⟩
    · exact ⟨e, hx, Or.inr h⟩
    · exact ⟨e, hx, Or.inl h⟩
  loopless := by
    intro v h
    rcases h with ⟨e, _, h | h⟩
    · exact G.noLoops e.1 (h.1.trans h.2.symm)
    · exact G.noLoops e.1 (h.1.trans h.2.symm)

def restrictedSelectedDegree (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) (v : G.Vertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : G.RestrictedEdge E =>
    x e ≠ 0 ∧ G.incident e.1 v).card

def IsRestrictedLinearForest (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) : Prop :=
  (G.restrictedSelectedGraph E x).IsAcyclic ∧
    ∀ v, G.restrictedSelectedDegree E x v ≤ 2

def RestrictedLinearForestWord (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.RestrictedWord E // G.restrictedBoundary E x = t ∧
    G.IsRestrictedLinearForest E x}

noncomputable instance restrictedLinearForestWordFintype (G : PhysicalGraph)
    (E : Finset G.Edge) (t : G.Demand) : Fintype (G.RestrictedLinearForestWord E t) := by
  classical
  letI : Fintype (G.RestrictedWord E) := inferInstance
  haveI : Finite (G.RestrictedLinearForestWord E t) :=
    Finite.of_injective (fun x : G.RestrictedLinearForestWord E t => x.1) (by
      intro x y h
      exact Subtype.ext h)
  exact Fintype.ofFinite _

def restrictedWordLength (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => x e ≠ 0).card

def outsideWordLength (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.OutsideWord E) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => x e ≠ 0).card

private theorem restrictedSupport_card_eq (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    (Finset.univ.filter fun e : G.RestrictedEdge E => x e.1 ≠ 0).card =
      ((G.edgeSupport x).filter (fun e => e ∈ E)).card := by
  classical
  let s : Finset (G.RestrictedEdge E) := Finset.univ.filter fun e => x e.1 ≠ 0
  let t : Finset G.Edge := (G.edgeSupport x).filter fun e => e ∈ E
  have himage : s.image Subtype.val = t := by
    ext e
    simp [s, t, PhysicalGraph.edgeSupport]
  calc
    s.card = (s.image Subtype.val).card := by
      rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)]
    _ = t.card := congrArg Finset.card himage

private theorem outsideSupport_card_eq (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    (Finset.univ.filter fun e : G.OutsideEdge E => x e.1 ≠ 0).card =
      ((G.edgeSupport x).filter (fun e => e ∉ E)).card := by
  classical
  let s : Finset (G.OutsideEdge E) := Finset.univ.filter fun e => x e.1 ≠ 0
  let t : Finset G.Edge := (G.edgeSupport x).filter fun e => e ∉ E
  have himage : s.image Subtype.val = t := by
    ext e
    simp [s, t, PhysicalGraph.edgeSupport]
  calc
    s.card = (s.image Subtype.val).card := by
      rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)]
    _ = t.card := congrArg Finset.card himage

theorem wordLength_partition (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.wordLength x = G.restrictedWordLength E (G.restrictWord E x) +
      G.outsideWordLength E (G.restrictOutsideWord E x) := by
  classical
  change (G.edgeSupport x).card =
    (Finset.univ.filter fun e : G.RestrictedEdge E => x e.1 ≠ 0).card +
      (Finset.univ.filter fun e : G.OutsideEdge E => x e.1 ≠ 0).card
  rw [restrictedSupport_card_eq G E x, outsideSupport_card_eq G E x]
  unfold PhysicalGraph.edgeSupport
  have hdisj : Disjoint
      ((Finset.univ.filter fun e : G.Edge => x e ≠ 0).filter fun e => e ∈ E)
      ((Finset.univ.filter fun e : G.Edge => x e ≠ 0).filter fun e => e ∉ E) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    exact he₂.2 he₁.2
  have hunion :
      ((Finset.univ.filter fun e : G.Edge => x e ≠ 0).filter fun e => e ∈ E) ∪
        ((Finset.univ.filter fun e : G.Edge => x e ≠ 0).filter fun e => e ∉ E) =
        Finset.univ.filter fun e : G.Edge => x e ≠ 0 := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hnotzero, _⟩ | ⟨hnotzero, _⟩) <;> exact hnotzero
    · intro hnotzero
      by_cases hE : e ∈ E
      · exact Or.inl ⟨hnotzero, hE⟩
      · exact Or.inr ⟨hnotzero, hE⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

def restrictedLinearForestLengths (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) : Finset ℕ :=
  Finset.univ.image fun x : G.RestrictedLinearForestWord E t =>
    G.restrictedWordLength E x.1

def restrictedLinearForestMultiplicity (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) : ℕ := (G.restrictedLinearForestLengths E t).card

def maxRestrictedLinearForestMultiplicity (G : PhysicalGraph) (E : Finset G.Edge) : ℕ :=
  Finset.univ.sup (G.restrictedLinearForestMultiplicity E)

def normalizedRestrictedLinearForestCapacity (G : PhysicalGraph) (E : Finset G.Edge) : ℝ :=
  (G.maxRestrictedLinearForestMultiplicity E : ℝ) / (2 : ℝ) ^ G.restrictedCycleRank E

theorem restrictedWordLength_le_edgeSetCard (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) : G.restrictedWordLength E x ≤ E.card := by
  classical
  unfold restrictedWordLength
  simpa only [Fintype.card_coe] using
    (Finset.card_le_univ (Finset.univ.filter fun e : G.RestrictedEdge E => x e ≠ 0))

theorem restrictedLinearForestMultiplicity_le_edgeSetCard_add_one
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand) :
    G.restrictedLinearForestMultiplicity E t ≤ E.card + 1 := by
  classical
  unfold restrictedLinearForestMultiplicity restrictedLinearForestLengths
  calc
    (Finset.univ.image fun x : G.RestrictedLinearForestWord E t =>
        G.restrictedWordLength E x.1).card ≤ (Finset.range (E.card + 1)).card := by
      apply Finset.card_le_card
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (G.restrictedWordLength_le_edgeSetCard E x.1))
    _ = E.card + 1 := Finset.card_range _

@[simp] theorem restrict_extendWord (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedWord E) : G.restrictWord E (G.extendWord E x) = x := by
  funext e
  simp [restrictWord, extendWord]



theorem restrictedBoundary_eq_hostBoundary_extend
    (G : PhysicalGraph) (E : Finset G.Edge) (x : G.RestrictedWord E) :
    G.boundary (G.extendWord E x) = G.restrictedBoundary E x := by
  rfl

theorem extendWord_cycleSpace (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.RestrictedCycleSpace E) : G.extendWord E x.1 ∈ G.CycleSpace := by
  change G.boundary (G.extendWord E x.1) = 0
  rw [G.restrictedBoundary_eq_hostBoundary_extend]
  exact x.2

theorem restrictedSelectedGraph_le_host (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    G.restrictedSelectedGraph E (G.restrictWord E x) ≤ G.selectedGraph x := by
  intro u v h
  rcases h with ⟨e, he, h | h⟩
  · exact ⟨e.1, by simpa [restrictWord] using he, Or.inl h⟩
  · exact ⟨e.1, by simpa [restrictWord] using he, Or.inr h⟩

theorem restrictWord_linearForest (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) (hx : G.IsLinearForest x) :
    G.IsRestrictedLinearForest E (G.restrictWord E x) := by
  classical
  constructor
  · let hom : G.restrictedSelectedGraph E (G.restrictWord E x) →g
        G.selectedGraph x := {
      toFun := id
      map_rel' := by
        intro a b h
        exact G.restrictedSelectedGraph_le_host E x h
    }
    intro v c hc
    have hc' : (c.map hom).IsCycle :=
      SimpleGraph.Walk.IsCycle.map (f := hom)
        (by intro a b h; simpa [hom] using h) hc
    exact hx.1 (c.map hom) hc'
  · intro v
    have hcard : G.restrictedSelectedDegree E (G.restrictWord E x) v ≤
        G.selectedDegree x v := by
      unfold restrictedSelectedDegree PhysicalGraph.selectedDegree
      apply Finset.card_le_card_of_injOn (fun e : G.RestrictedEdge E => e.1)
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rcases he with ⟨he, hi⟩
        refine ⟨?_, hi⟩
        simpa [restrictWord] using he
      · intro e he f hf hef
        exact Subtype.ext hef
    exact hcard.trans (hx.2 v)

theorem restrictedCycleRank_le (G : PhysicalGraph) (E : Finset G.Edge) :
    G.restrictedCycleRank E ≤ G.cycleRank := by
  classical
  let f : ↥(G.RestrictedCycleSpace E) →ₗ[F₂] ↥G.CycleSpace :=
    LinearMap.codRestrict G.CycleSpace
      ((G.extendWordLinear E).comp (G.RestrictedCycleSpace E).subtype)
      (fun x => G.extendWord_cycleSpace E x)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have h' : G.extendWord E x.1 = G.extendWord E y.1 :=
      congrArg Subtype.val h
    have := congrArg (G.restrictWord E) h'
    simpa using this
  exact LinearMap.finrank_le_finrank_of_injective hf

end Erdos1016.PhysicalGraph

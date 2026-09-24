import Erdos1016.Extremal.Capacity.RestrictedPhysical

set_option autoImplicit false

/-!
# Capacity invariance under physical edge reindexing

The restricted edge words are exactly the words of `restrictPhysical`. This
module transports their linear-forest predicates and length sets, completing
the adapter from a restricted capacity to the capacity of an actual physical
subgraph.
-/

noncomputable section
namespace Erdos1016.PhysicalGraph

private theorem restrictPhysical_selectedGraph_eq (G : PhysicalGraph)
    (E : Finset G.Edge) (x : (G.restrictPhysical E).Word) :
    (G.restrictPhysical E).selectedGraph x =
      G.restrictedSelectedGraph E (G.restrictPhysicalWordEquiv E x) := by
  ext u v
  constructor
  · rintro ⟨i, hx, hadj | hadj⟩
    · refine ⟨G.restrictedEdgeEquiv E i, ?_, ?_⟩
      · simpa [restrictPhysicalWordEquiv] using hx
      · exact Or.inl ⟨by simpa [restrictPhysical] using hadj.1,
          by simpa [restrictPhysical] using hadj.2⟩
    · refine ⟨G.restrictedEdgeEquiv E i, ?_, ?_⟩
      · simpa [restrictPhysicalWordEquiv] using hx
      · exact Or.inr ⟨by simpa [restrictPhysical] using hadj.1,
          by simpa [restrictPhysical] using hadj.2⟩
  · rintro ⟨e, hx, hadj | hadj⟩
    · refine ⟨(G.restrictedEdgeEquiv E).symm e, ?_, ?_⟩
      · simpa [restrictPhysicalWordEquiv] using hx
      · exact Or.inl ⟨by simpa [restrictPhysical] using hadj.1,
          by simpa [restrictPhysical] using hadj.2⟩
    · refine ⟨(G.restrictedEdgeEquiv E).symm e, ?_, ?_⟩
      · simpa [restrictPhysicalWordEquiv] using hx
      · exact Or.inr ⟨by simpa [restrictPhysical] using hadj.1,
          by simpa [restrictPhysical] using hadj.2⟩

private theorem restrictPhysical_selectedDegree_eq (G : PhysicalGraph)
    (E : Finset G.Edge) (x : (G.restrictPhysical E).Word) (v : G.Vertex) :
    (G.restrictPhysical E).selectedDegree x v =
      G.restrictedSelectedDegree E (G.restrictPhysicalWordEquiv E x) v := by
  classical
  let A := {i : Fin E.card // x i ≠ 0 ∧
    (G.restrictPhysical E).incident i v}
  let B := {e : G.RestrictedEdge E //
    (G.restrictPhysicalWordEquiv E x) e ≠ 0 ∧ G.incident e.1 v}
  let f : A ≃ B := {
    toFun := fun i => ⟨G.restrictedEdgeEquiv E i.1, by
      constructor
      · simpa [restrictPhysicalWordEquiv] using i.2.1
      · simpa [restrictPhysical] using i.2.2⟩
    invFun := fun e => ⟨(G.restrictedEdgeEquiv E).symm e.1, by
      constructor
      · simpa [restrictPhysicalWordEquiv] using e.2.1
      · simpa [PhysicalGraph.incident, restrictPhysical,
          restrictedEdgeEquiv] using e.2.2⟩
    left_inv := by intro i; apply Subtype.ext; simp
    right_inv := by intro e; apply Subtype.ext; simp }
  have hcard := Fintype.card_congr f
  simpa [A, B, PhysicalGraph.selectedDegree, restrictedSelectedDegree,
    Fintype.card_coe, Fintype.card_subtype] using hcard

/-- Linear-forest words correspond exactly under edge reindexing. -/
def restrictPhysicalLinearForestWordEquiv (G : PhysicalGraph)
    (E : Finset G.Edge) (t : G.Demand) :
    (G.restrictPhysical E).LinearForestWord t ≃
      G.RestrictedLinearForestWord E t where
  toFun x := by
    refine ⟨G.restrictPhysicalWordEquiv E x.1, ?_⟩
    constructor
    · change G.restrictedBoundary E (G.restrictPhysicalWordEquiv E x.1) = t
      rw [← G.restrictPhysical_boundary E x.1]
      exact x.2.1
    · constructor
      · change (G.restrictedSelectedGraph E
          (G.restrictPhysicalWordEquiv E x.1)).IsAcyclic
        rw [← G.restrictPhysical_selectedGraph_eq E x.1]
        exact x.2.2.1
      · intro v
        rw [← G.restrictPhysical_selectedDegree_eq E x.1 v]
        exact x.2.2.2 v
  invFun x := by
    refine ⟨(G.restrictPhysicalWordEquiv E).symm x.1, ?_⟩
    constructor
    · have hb := G.restrictPhysical_boundary E
        ((G.restrictPhysicalWordEquiv E).symm x.1)
      rw [hb]
      rw [LinearEquiv.apply_symm_apply]
      exact x.2.1
    · constructor
      · have hg := G.restrictPhysical_selectedGraph_eq E
          ((G.restrictPhysicalWordEquiv E).symm x.1)
        change ((G.restrictPhysical E).selectedGraph
          ((G.restrictPhysicalWordEquiv E).symm x.1)).IsAcyclic
        rw [hg]
        rw [LinearEquiv.apply_symm_apply]
        exact x.2.2.1
      · intro v
        have hd := G.restrictPhysical_selectedDegree_eq E
          ((G.restrictPhysicalWordEquiv E).symm x.1) v
        rw [hd]
        rw [LinearEquiv.apply_symm_apply]
        exact x.2.2.2 v
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- The distinct linear-forest length sets agree under the physical
reindexing. -/
theorem restrictPhysical_linearForestLengths (G : PhysicalGraph)
    (E : Finset G.Edge) (t : G.Demand) :
    (G.restrictPhysical E).linearForestLengths t =
      G.restrictedLinearForestLengths E t := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨x, -, hlen⟩
    refine Finset.mem_image.mpr ⟨G.restrictPhysicalLinearForestWordEquiv E t x,
      Finset.mem_univ _, ?_⟩
    calc
      G.restrictedWordLength E
          (G.restrictPhysicalLinearForestWordEquiv E t x).1 =
          (G.restrictPhysical E).wordLength x.1 := by
            rw [G.restrictPhysical_wordLength]
            rfl
      _ = n := hlen
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨x, -, hlen⟩
    refine Finset.mem_image.mpr ⟨(G.restrictPhysicalLinearForestWordEquiv E t).symm x,
      Finset.mem_univ _, ?_⟩
    rw [G.restrictPhysical_wordLength]
    change G.restrictedWordLength E
      (G.restrictPhysicalWordEquiv E
        ((G.restrictPhysicalWordEquiv E).symm x.1)) = n
    rw [LinearEquiv.apply_symm_apply]
    exact hlen

/-- Every demand has the same distinct-length multiplicity in the restricted
model and the reindexed physical graph. -/
theorem restrictPhysical_linearForestMultiplicity (G : PhysicalGraph)
    (E : Finset G.Edge) (t : G.Demand) :
    (G.restrictPhysical E).linearForestMultiplicity t =
      G.restrictedLinearForestMultiplicity E t := by
  unfold linearForestMultiplicity restrictedLinearForestMultiplicity
  rw [G.restrictPhysical_linearForestLengths E t]

/-- Maximizing over demands preserves the same multiplicity. -/
theorem restrictPhysical_maxLinearForestMultiplicity (G : PhysicalGraph)
    (E : Finset G.Edge) :
    (G.restrictPhysical E).maxLinearForestMultiplicity =
      G.maxRestrictedLinearForestMultiplicity E := by
  unfold maxLinearForestMultiplicity maxRestrictedLinearForestMultiplicity
  apply Finset.sup_congr rfl
  intro t ht
  exact G.restrictPhysical_linearForestMultiplicity E t

/-- A restricted local capacity is exactly the ordinary local capacity of
its physical edge-subgraph. -/
theorem restrictPhysical_normalizedLinearForestCapacity (G : PhysicalGraph)
    (E : Finset G.Edge) :
    (G.restrictPhysical E).normalizedLinearForestCapacity =
      G.normalizedRestrictedLinearForestCapacity E := by
  unfold normalizedLinearForestCapacity normalizedRestrictedLinearForestCapacity
  rw [G.restrictPhysical_maxLinearForestMultiplicity E,
    G.restrictPhysical_cycleRank E]

end Erdos1016.PhysicalGraph
end

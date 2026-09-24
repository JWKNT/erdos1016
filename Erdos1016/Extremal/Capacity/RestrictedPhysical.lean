import Erdos1016.Extremal.Capacity.EdgePartitionRank

set_option autoImplicit false

/-!
# Physical graph on a restricted edge set

This module turns a finite edge restriction of a `PhysicalGraph` into another
`PhysicalGraph`, reindexing the chosen physical labels by `Fin E.card` and
keeping the host vertices unchanged.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

/-- The finite edge-label equivalence used by the physical restriction. -/
def restrictedEdgeEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    Fin E.card ≃ G.RestrictedEdge E := (Finset.equivFin E).symm

/-- The physical edge-subgraph on `E`, with the same vertices as the host. -/
def restrictPhysical (G : PhysicalGraph) (E : Finset G.Edge) : PhysicalGraph where
  vertexCount := G.vertexCount
  edgeCount := E.card
  src i := G.src (G.restrictedEdgeEquiv E i).1
  dst i := G.dst (G.restrictedEdgeEquiv E i).1
  noLoops i := G.noLoops (G.restrictedEdgeEquiv E i).1
  simple i j h := by
    have he := G.simple (G.restrictedEdgeEquiv E i).1
      (G.restrictedEdgeEquiv E j).1
    have h' :
        ((G.src (G.restrictedEdgeEquiv E i).1 =
            G.src (G.restrictedEdgeEquiv E j).1 ∧
          G.dst (G.restrictedEdgeEquiv E i).1 =
            G.dst (G.restrictedEdgeEquiv E j).1) ∨
         (G.src (G.restrictedEdgeEquiv E i).1 =
            G.dst (G.restrictedEdgeEquiv E j).1 ∧
          G.dst (G.restrictedEdgeEquiv E i).1 =
            G.src (G.restrictedEdgeEquiv E j).1)) := by
      change ((G.src (G.restrictedEdgeEquiv E i).1 =
            G.src (G.restrictedEdgeEquiv E j).1 ∧
          G.dst (G.restrictedEdgeEquiv E i).1 =
            G.dst (G.restrictedEdgeEquiv E j).1) ∨
         (G.src (G.restrictedEdgeEquiv E i).1 =
            G.dst (G.restrictedEdgeEquiv E j).1 ∧
          G.dst (G.restrictedEdgeEquiv E i).1 =
            G.src (G.restrictedEdgeEquiv E j).1)) at h
      exact h
    have hij := he h'
    apply (G.restrictedEdgeEquiv E).injective
    apply Subtype.ext
    exact hij

/-- Reindexing edge words on `G ↾ E` is linearly equivalent to words on the
subtype of host edges in `E`. -/
def restrictPhysicalWordEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.restrictPhysical E).Word ≃ₗ[F₂] G.RestrictedWord E where
  toFun x e := x ((G.restrictedEdgeEquiv E).symm e)
  invFun x i := x (G.restrictedEdgeEquiv E i)
  left_inv x := by
    funext i
    simp [restrictedEdgeEquiv]
  right_inv x := by
    funext e
    simp [restrictedEdgeEquiv]
  map_add' x y := by
    funext e
    rfl
  map_smul' a x := by
    funext e
    rfl

/-- A sum over the reindexed edges is the same as a host-edge sum whose terms
vanish outside `E`. -/
private theorem sum_restrictPhysical_edges (G : PhysicalGraph) (E : Finset G.Edge)
    (f : G.RestrictedEdge E → F₂) :
    (∑ i : Fin E.card, f (G.restrictedEdgeEquiv E i)) =
      ∑ e : G.Edge, if h : e ∈ E then f ⟨e, h⟩ else 0 := by
  classical
  calc
    (∑ i : Fin E.card, f (G.restrictedEdgeEquiv E i)) =
        ∑ e : G.RestrictedEdge E, f e := by
      apply Fintype.sum_equiv (G.restrictedEdgeEquiv E)
      intro i
      rfl
    _ = ∑ e : G.Edge, if h : e ∈ E then f ⟨e, h⟩ else 0 := by
      calc
        (∑ e : G.RestrictedEdge E, f e) =
            ∑ e ∈ E.attach, f e := by simp
        _ = ∑ e : G.Edge, if h : e ∈ E then f ⟨e, h⟩ else 0 :=
          Finset.sum_attach_eq_sum_dite E f

/-- The edge-word equivalence preserves the host boundary after extending by
zero outside the selected edge set. -/
theorem restrictPhysical_boundary (G : PhysicalGraph) (E : Finset G.Edge)
    (x : (G.restrictPhysical E).Word) :
    (G.restrictPhysical E).boundary x =
      G.restrictedBoundary E (G.restrictPhysicalWordEquiv E x) := by
  classical
  let y := G.restrictPhysicalWordEquiv E x
  funext v
  change (∑ i : Fin E.card,
      ((if G.src (G.restrictedEdgeEquiv E i).1 = v then x i else 0) +
       (if G.dst (G.restrictedEdgeEquiv E i).1 = v then x i else 0))) =
    (∑ e : G.Edge,
      ((if G.src e = v then G.extendWord E y e else 0) +
       (if G.dst e = v then G.extendWord E y e else 0)))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsrc :
      (∑ i : Fin E.card,
        if G.src (G.restrictedEdgeEquiv E i).1 = v then x i else 0) =
      ∑ e : G.Edge, if G.src e = v then G.extendWord E y e else 0 := by
    calc
      (∑ i : Fin E.card,
          if G.src (G.restrictedEdgeEquiv E i).1 = v then x i else 0) =
          ∑ i : Fin E.card,
            if G.src (G.restrictedEdgeEquiv E i).1 = v then
              x ((G.restrictedEdgeEquiv E).symm (G.restrictedEdgeEquiv E i)) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ e : G.Edge, if h : e ∈ E then
            (if G.src e = v then x ((G.restrictedEdgeEquiv E).symm ⟨e, h⟩) else 0)
          else 0 := G.sum_restrictPhysical_edges E
            (fun a => if G.src a.1 = v then x ((G.restrictedEdgeEquiv E).symm a) else 0)
      _ = ∑ e : G.Edge, if G.src e = v then G.extendWord E y e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e ∈ E <;> by_cases hs : G.src e = v <;>
          simp [extendWord, y, restrictPhysicalWordEquiv, restrictedEdgeEquiv, he, hs]
  have hdst :
      (∑ i : Fin E.card,
        if G.dst (G.restrictedEdgeEquiv E i).1 = v then x i else 0) =
      ∑ e : G.Edge, if G.dst e = v then G.extendWord E y e else 0 := by
    calc
      (∑ i : Fin E.card,
          if G.dst (G.restrictedEdgeEquiv E i).1 = v then x i else 0) =
          ∑ i : Fin E.card,
            if G.dst (G.restrictedEdgeEquiv E i).1 = v then
              x ((G.restrictedEdgeEquiv E).symm (G.restrictedEdgeEquiv E i)) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ e : G.Edge, if h : e ∈ E then
            (if G.dst e = v then x ((G.restrictedEdgeEquiv E).symm ⟨e, h⟩) else 0)
          else 0 := G.sum_restrictPhysical_edges E
            (fun a => if G.dst a.1 = v then x ((G.restrictedEdgeEquiv E).symm a) else 0)
      _ = ∑ e : G.Edge, if G.dst e = v then G.extendWord E y e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e ∈ E <;> by_cases hs : G.dst e = v <;>
          simp [extendWord, y, restrictPhysicalWordEquiv, restrictedEdgeEquiv, he, hs]
  rw [hsrc, hdst]

/-- The reindexing preserves support size (and hence word length). -/
theorem restrictPhysical_wordLength (G : PhysicalGraph) (E : Finset G.Edge)
    (x : (G.restrictPhysical E).Word) :
    (G.restrictPhysical E).wordLength x =
      G.restrictedWordLength E (G.restrictPhysicalWordEquiv E x) := by
  classical
  unfold PhysicalGraph.wordLength PhysicalGraph.edgeSupport restrictedWordLength
  let e := G.restrictedEdgeEquiv E
  have himage :
      (Finset.univ.filter fun i : Fin E.card => x i ≠ 0).image e =
        Finset.univ.filter fun a : G.RestrictedEdge E =>
          (G.restrictPhysicalWordEquiv E x) a ≠ 0 := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa [e, restrictPhysicalWordEquiv, restrictedEdgeEquiv] using hi
    · intro ha
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      simpa [e, restrictPhysicalWordEquiv, restrictedEdgeEquiv] using ha
  calc
    _ = ((Finset.univ.filter fun i : Fin E.card => x i ≠ 0).image e).card := by
      exact (Finset.card_image_of_injective
        (Finset.univ.filter fun i : Fin E.card => x i ≠ 0) e.injective).symm
    _ = (Finset.univ.filter fun a : G.RestrictedEdge E =>
          (G.restrictPhysicalWordEquiv E x) a ≠ 0).card := congrArg Finset.card himage

/-- Cycle spaces of the physical restriction and of the restricted boundary
map are linearly equivalent. -/
def restrictPhysicalCycleEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.restrictPhysical E).CycleSpace ≃ₗ[F₂] G.RestrictedCycleSpace E where
  toFun x := ⟨G.restrictPhysicalWordEquiv E x.1, by
    change G.restrictedBoundary E (G.restrictPhysicalWordEquiv E x.1) = 0
    rw [← G.restrictPhysical_boundary E x.1]
    exact x.2⟩
  invFun x := ⟨(G.restrictPhysicalWordEquiv E).symm x.1, by
    change (G.restrictPhysical E).boundary
      ((G.restrictPhysicalWordEquiv E).symm x.1) = 0
    rw [G.restrictPhysical_boundary E ((G.restrictPhysicalWordEquiv E).symm x.1)]
    simpa using x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    exact (G.restrictPhysicalWordEquiv E).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact (G.restrictPhysicalWordEquiv E).map_smul a x.1

/-- Cycle rank is unchanged when the edge restriction is represented as its
own physical graph. -/
theorem restrictPhysical_cycleRank (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.restrictPhysical E).cycleRank = G.restrictedCycleRank E := by
  unfold PhysicalGraph.cycleRank restrictedCycleRank
  exact (G.restrictPhysicalCycleEquiv E).finrank_eq

end Erdos1016.PhysicalGraph

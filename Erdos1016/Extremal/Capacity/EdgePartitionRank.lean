import Erdos1016.Extremal.Capacity.LinearForestRestriction

set_option autoImplicit false

/-!
# Exact cycle-rank split across an edge partition

For an edge set and its complement, a host cycle word is determined by its
two restrictions. The common boundary is the only coupling between the two
pieces. This module records the resulting exact rank identity, retaining the
actual image dimension instead of replacing it by a vertex-count estimate.
-/

noncomputable section
namespace Erdos1016.PhysicalGraph

/-- The cycle words supported on the outside of `E`. -/
abbrev OutsideCycleSpace (G : PhysicalGraph) (E : Finset G.Edge) :=
  LinearMap.ker (G.outsideBoundary E)

def outsideCycleRank (G : PhysicalGraph) (E : Finset G.Edge) : ℕ :=
  Module.finrank F₂ (G.OutsideCycleSpace E)

/-- The common boundary seen by the two sides of the partition, as a linear
map from the full host cycle space. -/
def commonBoundaryMap (G : PhysicalGraph) (E : Finset G.Edge) :
    G.CycleSpace →ₗ[F₂] G.Demand :=
  (G.outsideBoundary E).comp (G.outsideCycleProjection E)

def commonBoundaryRank (G : PhysicalGraph) (E : Finset G.Edge) : ℕ :=
  Module.finrank F₂ (LinearMap.range (G.commonBoundaryMap E))

@[simp] theorem commonBoundaryMap_apply (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.CycleSpace) :
    G.commonBoundaryMap E x =
      G.outsideBoundary E (G.restrictOutsideWord E x.1) := rfl

private theorem add_eq_zero_binary_iff {a b : F₂} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have hb : b + b = 0 := by
      have htwo : (2 : F₂) = 0 := by decide
      calc
        b + b = (2 : F₂) * b := by ring
        _ = 0 := by rw [htwo]; simp
    have h' := congrArg (fun z : F₂ => z + b) h
    simpa [add_assoc, hb] using h'
  · rintro rfl
    have htwo : (2 : F₂) = 0 := by decide
    calc
      a + a = (2 : F₂) * a := by ring
      _ = 0 := by rw [htwo]; simp

/-- On a host cycle, the two edge restrictions have the same boundary. -/
theorem boundaryParts_eq_of_cycle (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.CycleSpace) :
    G.restrictedBoundary E (G.restrictWord E x.1) =
      G.outsideBoundary E (G.restrictOutsideWord E x.1) := by
  have hsplit := G.boundary_inside_add_outside E x.1
  funext v
  have hv := congrFun hsplit v
  have hsum : G.restrictedBoundary E (G.restrictWord E x.1) v +
      G.outsideBoundary E (G.restrictOutsideWord E x.1) v = 0 := by
    simpa [x.2] using hv
  exact (add_eq_zero_binary_iff).1 hsum

/-- The kernel of the common-boundary map consists exactly of independent
cycles on the two edge pieces. -/
def edgePartitionKernelEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    LinearMap.ker (G.commonBoundaryMap E) ≃ₗ[F₂]
      G.RestrictedCycleSpace E × G.OutsideCycleSpace E where
  toFun x :=
    (⟨G.restrictWord E x.1.1, by
        have hout : G.outsideBoundary E
            (G.restrictOutsideWord E x.1.1) = 0 := x.2
        simpa [hout] using G.boundaryParts_eq_of_cycle E x.1⟩,
      ⟨G.restrictOutsideWord E x.1.1, by
        change G.outsideBoundary E (G.restrictOutsideWord E x.1.1) = 0
        exact x.2⟩)
  invFun x := by
    let z : G.Word := G.extendWord E x.1.1 + G.extendOutsideWord E x.2.1
    have hz : G.boundary z = 0 := by
      have hsplit := G.boundary_inside_add_outside E z
      have hins : G.restrictWord E z = x.1.1 := by
        funext e
        simp [z, restrictWord, extendWord, extendOutsideWord]
      have hout : G.restrictOutsideWord E z = x.2.1 := by
        funext e
        simp [z, restrictOutsideWord, extendWord, extendOutsideWord, e.2]
      rw [hins, hout, x.1.2, x.2.2] at hsplit
      simpa using hsplit.symm
    have hq : G.commonBoundaryMap E ⟨z, hz⟩ = 0 := by
      change G.outsideBoundary E (G.restrictOutsideWord E z) = 0
      rw [show G.restrictOutsideWord E z = x.2.1 by
        funext e
        simp [z, restrictOutsideWord, extendWord, extendOutsideWord, e.2]]
      exact x.2.2
    exact ⟨⟨z, hz⟩, hq⟩
  left_inv x := by
    dsimp
    apply Subtype.ext
    apply Subtype.ext
    exact G.extend_inside_add_outside E x.1.1
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext e
      simp [restrictWord, extendWord, extendOutsideWord]
    · apply Subtype.ext
      funext e
      simp [restrictOutsideWord, extendWord, extendOutsideWord, e.2]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- The host cycle rank is the sum of the two internal ranks and the rank of
the actual common-boundary image. -/
theorem cycleRank_edgePartition (G : PhysicalGraph) (E : Finset G.Edge) :
    G.cycleRank = G.restrictedCycleRank E + G.outsideCycleRank E +
      G.commonBoundaryRank E := by
  have hkernel := (G.edgePartitionKernelEquiv E).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker (G.commonBoundaryMap E)
  unfold PhysicalGraph.cycleRank restrictedCycleRank outsideCycleRank
    commonBoundaryRank
  rw [hkernel, Module.finrank_prod] at hrank
  omega

abbrev RestrictedBoundaryFiber (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.RestrictedWord E // G.restrictedBoundary E x = t}

abbrev OutsideBoundaryFiber (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.OutsideWord E // G.outsideBoundary E x = t}

abbrev CommonBoundaryFiber (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.CycleSpace // G.commonBoundaryMap E x = t}

/-- Fixing the actual common boundary identifies a host cycle fiber with the
product of the two complete edge-piece fibers. -/
def commonBoundaryFiberEquiv (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :
    G.CommonBoundaryFiber E t ≃
      G.RestrictedBoundaryFiber E t × G.OutsideBoundaryFiber E t where
  toFun x :=
    (⟨G.restrictWord E x.1.1,
        (G.boundaryParts_eq_of_cycle E x.1).trans (by
          have hq := x.2
          change G.outsideBoundary E
            (G.restrictOutsideWord E x.1.1) = t at hq
          exact hq)⟩,
      ⟨G.restrictOutsideWord E x.1.1, by
        have hq := x.2
        change G.outsideBoundary E
          (G.restrictOutsideWord E x.1.1) = t at hq
        exact hq⟩)
  invFun x := by
    let z : G.Word := G.extendWord E x.1.1 + G.extendOutsideWord E x.2.1
    have hins : G.restrictWord E z = x.1.1 := by
      funext e
      simp [z, restrictWord, extendWord, extendOutsideWord]
    have hout : G.restrictOutsideWord E z = x.2.1 := by
      funext e
      simp [z, restrictOutsideWord, extendWord, extendOutsideWord, e.2]
    have hz : G.boundary z = 0 := by
      have hsplit := G.boundary_inside_add_outside E z
      rw [hins, hout, x.1.2, x.2.2] at hsplit
      have htt : t + t = (0 : G.Demand) := by
        funext v
        have htwo : (2 : F₂) = 0 := by decide
        calc
          t v + t v = (2 : F₂) * t v := by ring
          _ = 0 := by rw [htwo]; simp
      simpa [htt] using hsplit.symm
    have hq : G.commonBoundaryMap E ⟨z, hz⟩ = t := by
      change G.outsideBoundary E (G.restrictOutsideWord E z) = t
      rw [hout]
      exact x.2.2
    exact ⟨⟨z, hz⟩, hq⟩
  left_inv x := by
    dsimp
    apply Subtype.ext
    apply Subtype.ext
    exact G.extend_inside_add_outside E x.1.1
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext e
      simp [restrictWord, extendWord, extendOutsideWord]
    · apply Subtype.ext
      funext e
      simp [restrictOutsideWord, extendWord, extendOutsideWord, e.2]



end Erdos1016.PhysicalGraph

import Erdos1016.Extremal.Capacity.CycleLengthComposition

set_option autoImplicit false

/-!
# Complementary restricted cycle rank

The outside edge labels of a partition are exactly the restricted edge
labels of its complement. The corresponding boundary kernels therefore have
the same dimension.
-/

noncomputable section
namespace Erdos1016.PhysicalGraph

/-- Reindex outside-edge words as words on the restricted complement. -/
def outsideWordEquivRestrictedComplement (G : PhysicalGraph)
    (E : Finset G.Edge) : G.OutsideWord E ≃ₗ[F₂] G.RestrictedWord Eᶜ where
  toFun x := fun e => x ((G.outsideEdgeEquiv E).symm e)
  invFun x := fun e => x (G.outsideEdgeEquiv E e)
  left_inv x := by
    funext e
    simp [outsideEdgeEquiv]
  right_inv x := by
    funext e
    simp [outsideEdgeEquiv]
  map_add' x y := by
    funext e
    rfl
  map_smul' a x := by
    funext e
    rfl

/-- Extending an outside word by zero is the same host word as extending its
reindexed complementary restricted word by zero. -/
theorem outsideBoundary_eq_restrictedComplement
    (G : PhysicalGraph) (E : Finset G.Edge) (x : G.OutsideWord E) :
    G.outsideBoundary E x =
      G.restrictedBoundary Eᶜ (G.outsideWordEquivRestrictedComplement E x) := by
  change G.boundary (G.extendOutsideWord E x) =
    G.boundary (G.extendWord Eᶜ (G.outsideWordEquivRestrictedComplement E x))
  congr 1
  funext e
  by_cases he : e ∈ E
  · have hc : e ∉ Eᶜ := by simpa using he
    simp [extendOutsideWord, extendWord, he, hc]
  · have hc : e ∈ Eᶜ := by simpa using he
    simp [extendOutsideWord, extendWord, he, hc,
      outsideWordEquivRestrictedComplement, outsideEdgeEquiv]

/-- The outside cycle space and the complement-restricted cycle space are
linearly equivalent through the outside/complement edge equivalence. -/
def outsideCycleSpaceEquivRestrictedComplement (G : PhysicalGraph)
    (E : Finset G.Edge) :
    G.OutsideCycleSpace E ≃ₗ[F₂] G.RestrictedCycleSpace Eᶜ where
  toFun x := ⟨G.outsideWordEquivRestrictedComplement E x.1, by
    change G.restrictedBoundary Eᶜ
      (G.outsideWordEquivRestrictedComplement E x.1) = 0
    rw [← G.outsideBoundary_eq_restrictedComplement E x.1]
    exact x.2⟩
  invFun x := ⟨(G.outsideWordEquivRestrictedComplement E).symm x.1, by
    change G.outsideBoundary E
      ((G.outsideWordEquivRestrictedComplement E).symm x.1) = 0
    rw [G.outsideBoundary_eq_restrictedComplement]
    simpa only [LinearEquiv.apply_symm_apply] using x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (G.outsideWordEquivRestrictedComplement E).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (G.outsideWordEquivRestrictedComplement E).right_inv x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (G.outsideWordEquivRestrictedComplement E) x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (G.outsideWordEquivRestrictedComplement E) a x.1

/-- The cycle-rank contribution of the outside is exactly the restricted
cycle rank of the complement. -/
theorem outsideCycleRank_eq_restrictedCycleRank_compl
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.outsideCycleRank E = G.restrictedCycleRank Eᶜ := by
  exact (G.outsideCycleSpaceEquivRestrictedComplement E).finrank_eq

end Erdos1016.PhysicalGraph

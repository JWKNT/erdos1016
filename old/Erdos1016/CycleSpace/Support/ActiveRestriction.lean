import Erdos1016.CycleSpace.Support.ActiveComponents

set_option autoImplicit false

/-!
# Removing globally inactive physical coordinates

The cycle space of the original physical graph is linearly equivalent to the
cycle space of its active-edge restriction. The forward map restricts words;
the inverse extends them by zero. -/

noncomputable section

namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016
local notation "F₂" => ZMod 2

/-- Restriction of physical words as a linear map. -/
def restrictWordLinear (G : PhysicalGraph) (E : Finset G.Edge) :
    G.Word →ₗ[F₂] G.RestrictedWord E where
  toFun := G.restrictWord E
  map_add' x y := by funext e; rfl
  map_smul' a x := by funext e; rfl

/-- The global cycle space, expressed on the reindexed active physical graph. -/
def activeCycleSpaceRestriction (G : PhysicalGraph) :
    G.CycleSpace →ₗ[F₂] (activeSubgraph G).CycleSpace := by
  let E := activeEdges G
  let A := activeSubgraph G
  let w := ((G.restrictPhysicalWordEquiv E).symm.toLinearMap.comp
    (restrictWordLinear G E)).comp G.CycleSpace.subtype
  refine LinearMap.codRestrict A.CycleSpace w ?_
  intro x
  have hext : G.extendWord E (G.restrictWord E x.1) = x.1 := by
    funext e
    by_cases he : e ∈ E
    · simp [PhysicalGraph.extendWord, PhysicalGraph.restrictWord, he]
    · have hz := cycle_word_zero_off_active_edges G x e (by simpa [E] using he)
      simp [PhysicalGraph.extendWord, he, hz]
  let y : A.Word := (G.restrictPhysicalWordEquiv E).symm
    (G.restrictWord E x.1)
  have hb := G.restrictPhysical_boundary E y
  have hcoord : G.restrictPhysicalWordEquiv E y = G.restrictWord E x.1 := by
    exact (G.restrictPhysicalWordEquiv E).apply_symm_apply _
  change (G.restrictPhysical E).boundary y = 0
  rw [hb, hcoord]
  change G.boundary (G.extendWord E (G.restrictWord E x.1)) = 0
  rw [hext]
  exact x.2

/-- Extend an active-subgraph cycle by zero to the original graph. -/
def activeCycleSpaceExtension (G : PhysicalGraph) :
    (activeSubgraph G).CycleSpace →ₗ[F₂] G.CycleSpace := by
  let E := activeEdges G
  let A := activeSubgraph G
  let w := (G.extendWordLinear E).comp
    ((G.restrictPhysicalWordEquiv E).toLinearMap.comp A.CycleSpace.subtype)
  refine LinearMap.codRestrict G.CycleSpace w ?_
  intro x
  have hb := G.restrictPhysical_boundary E x.1
  change G.restrictedBoundary E (G.restrictPhysicalWordEquiv E x.1) = 0
  rw [← hb]
  exact x.2

/-- The original cycle space is linearly equivalent to the active-subgraph
cycle space. Globally inactive (in particular, bridge) coordinates vanish. -/
def cycleSpaceActiveSubgraphEquiv (G : PhysicalGraph) :
    G.CycleSpace ≃ₗ[F₂] (activeSubgraph G).CycleSpace where
  toFun := activeCycleSpaceRestriction G
  invFun := activeCycleSpaceExtension G
  left_inv x := by
    apply Subtype.ext
    let E := activeEdges G
    change G.extendWord E
      (G.restrictPhysicalWordEquiv E
        ((G.restrictPhysicalWordEquiv E).symm (G.restrictWord E x.1))) = x.1
    rw [(G.restrictPhysicalWordEquiv E).apply_symm_apply]
    funext e
    by_cases he : e ∈ E
    · simp [PhysicalGraph.extendWord, PhysicalGraph.restrictWord, he]
    · have hz := cycle_word_zero_off_active_edges G x e (by simpa [E] using he)
      simp [PhysicalGraph.extendWord, he, hz]
  right_inv x := by
    apply Subtype.ext
    let E := activeEdges G
    change (G.restrictPhysicalWordEquiv E).symm
      (G.restrictWord E
        (G.extendWord E (G.restrictPhysicalWordEquiv E x.1))) = x.1
    have hrestrict (z : G.RestrictedWord E) :
        G.restrictWord E (G.extendWord E z) = z := by
      funext e
      simp [PhysicalGraph.restrictWord, PhysicalGraph.extendWord, e.2]
    rw [hrestrict, (G.restrictPhysicalWordEquiv E).symm_apply_apply]
  map_add' x y := by
    exact (activeCycleSpaceRestriction G).map_add x y
  map_smul' a x := by
    exact (activeCycleSpaceRestriction G).map_smul a x

/-- The global cycle space is equivalent, as a finite type, to the product of
the cycle spaces of the active connected components. This composes the linear
restriction isomorphism with the active-component product decomposition. -/
def cycleSpaceProductEquiv (G : PhysicalGraph) :
    G.CycleSpace ≃
      ((c : ActiveComponent G) →
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) :=
  (cycleSpaceActiveSubgraphEquiv G).toEquiv.trans
    (cycleSpaceProductDecomposition G)

end Erdos1016.Proof.ActivePhysicalComponents

end

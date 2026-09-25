import Erdos1016.CycleSpace.Support.ActiveRestriction
import Erdos1016.Graph.PathExpansion.CycleEquivalence

set_option autoImplicit false

/-!
# Route compression on one selected active component

The auxiliary graph only replaces one active connected component.  This
module projects the full physical cycle space onto that component, applies
route compression with an injective (not necessarily surjective) vertex map,
and constructs a linear section by inserting zero coordinates on all other
active components.
-/

noncomputable section

namespace Erdos1016.Proof.SelectedComponentRoutes

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.ActivePhysicalComponents


local notation "F₂" => ZMod 2

/-- The selected connected component as a finite labelled multigraph. -/
def selectedComponentRouteGraph (G : PhysicalGraph) (c : ActiveComponent G) :
    FiniteMultiGraph where
  vertexCount := ((activeSubgraph G).restrictPhysical (componentEdges G c)).vertexCount
  edgeCount := ((activeSubgraph G).restrictPhysical (componentEdges G c)).edgeCount
  src := ((activeSubgraph G).restrictPhysical (componentEdges G c)).src
  dst := ((activeSubgraph G).restrictPhysical (componentEdges G c)).dst

/-- The restricted physical component and its finite-multigraph encoding have
identical cycle words and boundaries. -/
def selectedComponentToMultiGraphEquiv (G : PhysicalGraph) (c : ActiveComponent G) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace ≃ₗ[F₂]
      (selectedComponentRouteGraph G c).CycleSpace where
  toFun x := ⟨x.1, by
    have hx := x.2
    change (selectedComponentRouteGraph G c).boundary x.1 = 0
    change ((activeSubgraph G).restrictPhysical (componentEdges G c)).boundary x.1 = 0 at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx := x.2
    change ((activeSubgraph G).restrictPhysical (componentEdges G c)).boundary x.1 = 0
    change (selectedComponentRouteGraph G c).boundary x.1 = 0 at hx
    exact hx⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The exact product decomposition of the active cycle space, upgraded to a
linear equivalence. Each coordinate map only reindexes edge words, so it
preserves addition and scalar multiplication pointwise. -/
def activeComponentCycleProductLinearEquiv (G : PhysicalGraph) :
    (activeSubgraph G).CycleSpace ≃ₗ[F₂]
      ((c : ActiveComponent G) →
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) where
  toFun := cycleSpaceProductDecomposition G
  invFun := (cycleSpaceProductDecomposition G).symm
  left_inv := (cycleSpaceProductDecomposition G).left_inv
  right_inv := (cycleSpaceProductDecomposition G).right_inv
  map_add' x y := by
    funext c
    apply Subtype.ext
    funext e
    have hxy := activeCycleSpaceProductEquiv_apply_coordinate G (x + y) c e
    let edge := (edgeSigmaEquiv G).symm
      ⟨c, (activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) e⟩
    change (activeCycleSpaceProductEquiv G (x + y) c).1 e = _
    rw [hxy]
    change (x.1 edge + y.1 edge) = (x.1 edge + y.1 edge)
    rfl
  map_smul' a x := by
    funext c
    apply Subtype.ext
    funext e
    have hax := activeCycleSpaceProductEquiv_apply_coordinate G (a • x) c e
    let edge := (edgeSigmaEquiv G).symm
      ⟨c, (activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) e⟩
    change (activeCycleSpaceProductEquiv G (a • x) c).1 e = _
    rw [hax]
    change (a • x.1 edge) = a • x.1 edge
    rfl

/-- Projection of a full physical cycle onto one active component. -/
def projectToSelectedComponent (G : PhysicalGraph) (c : ActiveComponent G) :
    G.CycleSpace →ₗ[F₂]
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace := by
  classical
  exact (LinearMap.proj c).comp
    ((activeComponentCycleProductLinearEquiv G).toLinearMap.comp
    (cycleSpaceActiveSubgraphEquiv G).toLinearMap)

/-- Insert a local component cycle into the active cycle space with all other
active components zero, then extend it by zero on globally inactive edges. -/
def includeSelectedComponent (G : PhysicalGraph) (c : ActiveComponent G) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace →ₗ[F₂]
      G.CycleSpace := by
  classical
  let single := LinearMap.single F₂
    (fun d : ActiveComponent G =>
      ((activeSubgraph G).restrictPhysical (componentEdges G d)).CycleSpace) c
  exact (cycleSpaceActiveSubgraphEquiv G).symm.toLinearMap.comp
    ((activeComponentCycleProductLinearEquiv G).symm.toLinearMap.comp single)

/-- Projection followed by zero-extension recovers the chosen component
cycle exactly. -/
theorem project_include_selected_component
    (G : PhysicalGraph) (c : ActiveComponent G)
    (x : ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) :
    projectToSelectedComponent G c (includeSelectedComponent G c x) = x := by
  classical
  simp [projectToSelectedComponent, includeSelectedComponent,
    LinearMap.comp_apply, LinearMap.proj_comp_single_same]

/-- A route system whose vertex map is injective is enough for cycle-space
compression. Surjectivity of the vertex map is unnecessary: vertices outside
the image receive no route incidences, and injectivity of pushed demands
still detects a zero auxiliary boundary. -/
theorem cycleExpandMap_bijective_of_injective
    {A P : FiniteMultiGraph} (R : EdgeDisjointRouteSystem A P)
    (hφ : Function.Injective R.vertexMap)
    (hcover : ∀ p : P.Edge, ∃ e : A.Edge, p ∈ R.support e)
    (hconstant : ∀ (y : P.EdgeWord), y ∈ P.CycleSpace →
      ∀ e p q, p ∈ R.support e → q ∈ R.support e → y p = y q) :
    Function.Bijective (cycleExpandMap R) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply expand_injective A P R
    exact congrArg Subtype.val h
  · intro y
    let x : A.EdgeWord := contractWord R y.1
    have hxy : expand A P R x = y.1 :=
      expand_contractWord_eq R hcover hconstant y.1 y.2
    have hboundary : P.boundary (expand A P R x) = 0 := by
      rw [hxy]
      exact y.2
    have hsum : (∑ e, x e • endpointDemand A P R.vertexMap e) = 0 := by
      rw [← boundary_expand_eq_endpoint_sum A P R x]
      exact hboundary
    have hpush : pushDemand A P R.vertexMap (A.boundary x) = 0 := by
      rw [← endpoint_sum_eq_pushDemand_boundary A P R x]
      exact hsum
    have hxzero : A.boundary x = 0 := by
      apply pushDemand_injective_of_injective R.vertexMap hφ
      simpa using hpush
    refine ⟨⟨x, hxzero⟩, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Route expansion is a cycle-space linear equivalence with an injective
vertex map. -/
noncomputable def cycleExpandEquiv_of_injective
    {A P : FiniteMultiGraph} (R : EdgeDisjointRouteSystem A P)
    (hφ : Function.Injective R.vertexMap)
    (hcover : ∀ p : P.Edge, ∃ e : A.Edge, p ∈ R.support e)
    (hconstant : ∀ (y : P.EdgeWord), y ∈ P.CycleSpace →
      ∀ e p q, p ∈ R.support e → q ∈ R.support e → y p = y q) :
    A.CycleSpace ≃ₗ[F₂] P.CycleSpace :=
  LinearEquiv.ofBijective (cycleExpandMap R)
    (cycleExpandMap_bijective_of_injective R hφ hcover hconstant)













end Erdos1016.Proof.SelectedComponentRoutes

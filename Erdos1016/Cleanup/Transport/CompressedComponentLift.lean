import Erdos1016.Cleanup.Compression.CompressedRouteDecomposition
import Erdos1016.Cleanup.Transport.ComponentCorridorReindexing
import Erdos1016.Probability.Conditional.ActiveRestrictionEvents

set_option autoImplicit false

/-!
# Cleanup marginal fields from a compressed component corridor partition

This adapter uses a retained-vertex compressed graph for one active
component, composes its route equivalence with the component cycle projection,
and reindexes corridor paths and representatives back to the original graph.
-/

noncomputable section

namespace Erdos1016.Proof.CompressedComponentLift

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.PartitionRouteDecomposition
open Erdos1016.Proof.CompressedRouteDecomposition
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.SelectedComponentRoutes
open Erdos1016.Proof.ComponentCorridorReindexing
open Erdos1016.Proof.ComponentMarginalData
open Erdos1016.Proof.CleanupSpecification

local notation "F₂" => ZMod 2

variable {G : PhysicalGraph} {c : ActiveComponent G}
variable {P₀ : Finset ((activeSubgraph G).restrictPhysical (componentEdges G c)).Vertex}
variable {W : Finset ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge}

abbrev ComponentPhysicalGraph :=
  (activeSubgraph G).restrictPhysical (componentEdges G c)

abbrev ComponentRouteGraph := selectedComponentRouteGraph G c

/-- Convert the compressed graph's component vertices back to original
physical vertex labels. -/
def compressedComponentVertexMap
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) :
    (compressedCorridorGraph D hendpoints).Vertex → G.Vertex :=
  compressedCorridorVertexMap D hendpoints

/-- The component cycle marginal through the compressed route equivalence. -/
def compressedComponentMarginal
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) :
    G.CycleSpace →ₗ[F₂] (compressedCorridorGraph D hendpoints).CycleSpace := by
  let E := compressedCorridor_cycleEquiv D hnonempty hendpoints
  exact E.symm.toLinearMap.comp
    ((selectedComponentToMultiGraphEquiv G c).toLinearMap.comp
      (projectToSelectedComponent G c))

/-- Lift a compressed cycle along its corridor expansion and zero-extend it
outside the chosen active component. -/
def compressedComponentLift
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) :
    (compressedCorridorGraph D hendpoints).CycleSpace →ₗ[F₂] G.CycleSpace := by
  let E := compressedCorridor_cycleEquiv D hnonempty hendpoints
  exact includeSelectedComponent G c |>.comp
    ((selectedComponentToMultiGraphEquiv G c).symm.toLinearMap.comp E.toLinearMap)

theorem compressedComponentMarginal_lift
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (z : (compressedCorridorGraph D hendpoints).CycleSpace) :
      compressedComponentMarginal D hnonempty hendpoints
      (compressedComponentLift D hnonempty hendpoints z) = z := by
  let E := compressedCorridor_cycleEquiv D hnonempty hendpoints
  change E.symm
    ((selectedComponentToMultiGraphEquiv G c).toLinearMap
      (projectToSelectedComponent G c
        (includeSelectedComponent G c
          ((selectedComponentToMultiGraphEquiv G c).symm (E z))))) = z
  rw [project_include_selected_component]
  have hcomp := (selectedComponentToMultiGraphEquiv G c).apply_symm_apply (E z)
  change E.symm ((selectedComponentToMultiGraphEquiv G c)
    ((selectedComponentToMultiGraphEquiv G c).symm (E z))) = z
  rw [hcomp]
  exact E.symm_apply_apply z

theorem compressedComponentMarginal_surjective
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) :
    Function.Surjective (compressedComponentMarginal D hnonempty hendpoints) := by
  intro z
  exact ⟨compressedComponentLift D hnonempty hendpoints z,
    compressedComponentMarginal_lift D hnonempty hendpoints z⟩

/-- The corridor selected for each compressed edge, reindexed to an original
physical corridor. -/
def compressedComponentEdgePath
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (e : (compressedCorridorGraph D hendpoints).Edge) : PhysicalCorridor G :=
  componentCorridorToOriginal G c (corridorAt D e)

/-- One component representative from each compressed corridor. -/
noncomputable def compressedComponentRepresentative
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (e : (compressedCorridorGraph D hendpoints).Edge) :
    (selectedComponentRouteGraph G c).Edge :=
  Classical.choose
    ((compressedCorridorRouteSystem D hnonempty hendpoints).nonempty e)

theorem compressedComponentRepresentative_mem
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (e : (compressedCorridorGraph D hendpoints).Edge) :
    compressedComponentRepresentative D hnonempty hendpoints e ∈
      (corridorAt D e).support := by
  exact Classical.choose_spec
    ((compressedCorridorRouteSystem D hnonempty hendpoints).nonempty e)

/-- The marginal reads the original physical bit at the selected corridor
representative. -/
theorem compressedComponentMarginal_reads_representative
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (x : G.CycleSpace) (e : (compressedCorridorGraph D hendpoints).Edge) :
    (compressedComponentMarginal D hnonempty hendpoints x).1 e =
      x.1 (componentCorridorEdgeToOriginal G c
        (compressedComponentRepresentative D hnonempty hendpoints e)) := by
  let R := compressedCorridorRouteSystem D hnonempty hendpoints
  let E := compressedCorridor_cycleEquiv D hnonempty hendpoints
  let y := selectedComponentToMultiGraphEquiv G c
    (projectToSelectedComponent G c x)
  have hback := E.apply_symm_apply y
  have hcoord := congrFun (congrArg Subtype.val hback)
    (compressedComponentRepresentative D hnonempty hendpoints e)
  have hcontract :
      (compressedComponentMarginal D hnonempty hendpoints x).1 e =
        y.1 (compressedComponentRepresentative D hnonempty hendpoints e) := by
    change (E.symm y).1 e = _
    change expand (compressedCorridorGraph D hendpoints) (routeGraph ComponentPhysicalGraph)
      R (E.symm y).1 (compressedComponentRepresentative D hnonempty hendpoints e) = _ at hcoord
    rw [expand_apply_of_mem_support (compressedCorridorGraph D hendpoints)
      (routeGraph ComponentPhysicalGraph) R (E.symm y).1 e
      (compressedComponentRepresentative D hnonempty hendpoints e)
      (compressedComponentRepresentative_mem D hnonempty hendpoints e)] at hcoord
    exact hcoord
  rw [hcontract, projectToSelectedComponent_coordinate]
  rfl

/-- Every edge reindexed from the restricted active component is globally
active. -/
theorem componentCorridorEdgeToOriginal_mem_activeEdges
    (p : ComponentRouteGraph.Edge) :
    componentCorridorEdgeToOriginal G c p ∈ activeEdges G := by
  exact ((G.restrictedEdgeEquiv (activeEdges G)
    (((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) p).1)).2)

/-- With pairwise disjoint route supports, expansion has exactly the
indicator support formula used by `CleanupOutput.lift_is_path_expansion`. -/
theorem routeExpansion_eq_indicator
    {A P : FiniteMultiGraph} (R : EdgeDisjointRouteSystem A P)
    (x : A.CycleSpace) (p : P.Edge) :
    expand A P R x.1 p =
      if ∃ e, x.1 e ≠ 0 ∧ p ∈ R.support e then 1 else 0 := by
  classical
  by_cases h : ∃ e, x.1 e ≠ 0 ∧ p ∈ R.support e
  · have hExists := h
    obtain ⟨e, hne, hp⟩ := h
    rw [expand_apply_of_mem_support A P R x.1 e p hp]
    have hbit : x.1 e = 1 := by
      have hpos : 0 < (x.1 e).val := (ZMod.val_pos).2 hne
      have hlt := (x.1 e).val_lt
      have hval : (x.1 e).val = 1 := by omega
      exact (ZMod.val_eq_one (by norm_num) (x.1 e)).1 hval
    have hrhs :
        (if ∃ e, x.1 e ≠ 0 ∧ p ∈ R.support e then (1 : F₂) else 0) = 1 := if_pos hExists
    rw [hbit]
    exact hrhs.symm
  · rw [expand_apply]
    have hz : ∀ e : A.Edge, (if p ∈ R.support e then x.1 e else 0) = 0 := by
      intro e
      by_cases hp : p ∈ R.support e
      · have he : x.1 e = 0 := by
          by_cases heq : x.1 e = 0
          · exact heq
          · exact False.elim (h ⟨e, heq, hp⟩)
        simp [hp, he]
      · simp [hp]
    have hsum : (∑ e : A.Edge, (if p ∈ R.support e then x.1 e else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      exact hz e
    rw [hsum]
    simp [h]

/-- Original-graph representative edges on reindexed component corridors are
active in the global cycle space. -/
theorem compressedComponentPath_edge_active
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (e : (compressedCorridorGraph D hendpoints).Edge)
    (p : G.Edge) (hp : p ∈ (compressedComponentEdgePath D hnonempty hendpoints e).support) :
    ActiveEdge G p := by
  change p ∈ (componentCorridorToOriginal G c (corridorAt D e)).support at hp
  rw [componentCorridorToOriginal_support] at hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, hqp⟩
  have hmem := componentCorridorEdgeToOriginal_mem_activeEdges q
  have hactive := (mem_activeEdges_iff G _).1 hmem
  obtain ⟨x, hx⟩ := hactive
  exact hqp ▸ ⟨x, by rw [hx]; norm_num⟩

/-- Zero-inclusion of a selected component preserves the coordinate of its
component edges after the two physical edge reindexings. -/
theorem includeSelectedComponent_coordinate
    (y : (selectedComponentRouteGraph G c).CycleSpace)
    (p : (selectedComponentRouteGraph G c).Edge) :
    (includeSelectedComponent G c
      ((selectedComponentToMultiGraphEquiv G c).symm y)).1
        (componentCorridorEdgeToOriginal G c p) = y.1 p := by
  classical
  let xComp := (selectedComponentToMultiGraphEquiv G c).symm y
  let one := LinearMap.single F₂
    (fun d : ActiveComponent G =>
      ((activeSubgraph G).restrictPhysical (componentEdges G d)).CycleSpace) c xComp
  let active := (activeComponentCycleProductLinearEquiv G).symm one
  let activeEdge := ((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) p).1
  have hglobal : cycleSpaceActiveSubgraphEquiv G
      (includeSelectedComponent G c xComp) = active := by
    change cycleSpaceActiveSubgraphEquiv G
      ((cycleSpaceActiveSubgraphEquiv G).symm
        ((activeComponentCycleProductLinearEquiv G).symm
          (LinearMap.single F₂
            (fun d : ActiveComponent G =>
              ((activeSubgraph G).restrictPhysical (componentEdges G d)).CycleSpace)
            c xComp))) = active
    exact (cycleSpaceActiveSubgraphEquiv G).apply_symm_apply active
  have hglobalCoord :
      (includeSelectedComponent G c xComp).1
        (componentCorridorEdgeToOriginal G c p) = active.1 activeEdge := by
    have h := activeWordOfCycle_apply G (includeSelectedComponent G c xComp) activeEdge
    change (cycleSpaceActiveSubgraphEquiv G
      (includeSelectedComponent G c xComp)).1 activeEdge = _ at h
    rw [hglobal] at h
    exact h.symm
  have hproduct := (activeComponentCycleProductLinearEquiv G).apply_symm_apply one
  have hcomponent := congrFun hproduct c
  have hcoord := activeCycleSpaceProductEquiv_apply_coordinate G active c p
  have hcomponentCoord :
      (activeComponentCycleProductLinearEquiv G active c).1 p = xComp.1 p := by
    have hcomponent' :
        activeComponentCycleProductLinearEquiv G active c = xComp := by
      simpa [active, one, LinearMap.single_apply, Pi.single_apply] using hcomponent
    exact congrArg (fun z :
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace => z.1 p)
      hcomponent'
  have hactiveCoord : active.1 activeEdge = xComp.1 p := by
    calc
      active.1 activeEdge =
          (activeCycleSpaceProductEquiv G active c).1 p := hcoord.symm
      _ = xComp.1 p := hcomponentCoord
  calc
    (includeSelectedComponent G c xComp).1
        (componentCorridorEdgeToOriginal G c p) = active.1 activeEdge := hglobalCoord
    _ = xComp.1 p := hactiveCoord
    _ = y.1 p := rfl

/-- The selected-component inclusion vanishes on edges assigned to another
active component. -/
theorem includeSelectedComponent_zero_outside_component
    (y : (selectedComponentRouteGraph G c).CycleSpace)
    (a : (activeSubgraph G).Edge)
    (hother : edgeComponent G a ≠ c) :
    (includeSelectedComponent G c
      ((selectedComponentToMultiGraphEquiv G c).symm y)).1
        (originalActiveEdge G a) = 0 := by
  classical
  let xComp := (selectedComponentToMultiGraphEquiv G c).symm y
  let one := LinearMap.single F₂
    (fun d : ActiveComponent G =>
      ((activeSubgraph G).restrictPhysical (componentEdges G d)).CycleSpace) c xComp
  let active := (activeComponentCycleProductLinearEquiv G).symm one
  let d := edgeComponent G a
  let aj := ((activeSubgraph G).restrictedEdgeEquiv (componentEdges G d)).symm
      ⟨a, edgeComponent_mem_componentEdges G a⟩
  have hglobal : cycleSpaceActiveSubgraphEquiv G
      (includeSelectedComponent G c xComp) = active := by
    change cycleSpaceActiveSubgraphEquiv G
      ((cycleSpaceActiveSubgraphEquiv G).symm
        ((activeComponentCycleProductLinearEquiv G).symm
          (LinearMap.single F₂
            (fun j : ActiveComponent G =>
              ((activeSubgraph G).restrictPhysical (componentEdges G j)).CycleSpace)
            c xComp))) = active
    exact (cycleSpaceActiveSubgraphEquiv G).apply_symm_apply active
  have hsingle : one d = 0 := by
    change (LinearMap.single F₂
      (fun j : ActiveComponent G =>
        ((activeSubgraph G).restrictPhysical (componentEdges G j)).CycleSpace)
      c xComp) d = (0 :
        ((activeSubgraph G).restrictPhysical (componentEdges G d)).CycleSpace)
    rw [LinearMap.single_apply]
    simp [Pi.single_apply, d, hother]
  have hprod := (activeComponentCycleProductLinearEquiv G).apply_symm_apply one
  have hcomponent : activeComponentCycleProductLinearEquiv G active d = 0 := by
    exact (congrFun hprod d).trans hsingle
  have hcoord := activeCycleSpaceProductEquiv_apply_coordinate G active d aj
  have hsigma :
      (edgeSigmaEquiv G).symm ⟨d,
        (activeSubgraph G).restrictedEdgeEquiv (componentEdges G d) aj⟩ = a := by
    simp [edgeSigmaEquiv, d, aj]
  have hactive : active.1 a = 0 := by
    calc
      active.1 a = active.1
          ((edgeSigmaEquiv G).symm ⟨d,
            (activeSubgraph G).restrictedEdgeEquiv (componentEdges G d) aj⟩) := by
              rw [hsigma]
      _ = (activeComponentCycleProductLinearEquiv G active d).1 aj := hcoord.symm
      _ = 0 := congrArg (fun z => z.1 aj) hcomponent
  have hglobalCoord :
      (includeSelectedComponent G c xComp).1 (originalActiveEdge G a) = active.1 a := by
    have h := activeWordOfCycle_apply G (includeSelectedComponent G c xComp) a
    change (cycleSpaceActiveSubgraphEquiv G
      (includeSelectedComponent G c xComp)).1 a = _ at h
    rw [hglobal] at h
    exact h.symm
  rw [hglobalCoord, hactive]

/-- On every physical edge represented by the selected component, the
component cleanup lift is exactly the route expansion coordinate. -/
theorem compressedComponentLift_coordinate_on_component_edge
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (z : (compressedCorridorGraph D hendpoints).CycleSpace)
    (p : ComponentRouteGraph.Edge) :
    (compressedComponentLift D hnonempty hendpoints z).1
        (componentCorridorEdgeToOriginal G c p) =
      ((compressedCorridor_cycleEquiv D hnonempty hendpoints) z).1 p := by
  change (includeSelectedComponent G c
      ((selectedComponentToMultiGraphEquiv G c).symm
        ((compressedCorridor_cycleEquiv D hnonempty hendpoints) z))).1
      (componentCorridorEdgeToOriginal G c p) = _
  rw [includeSelectedComponent_coordinate]

/-- The lifted cycle also vanishes on every active edge from a different
physical component. -/
theorem compressedComponentLift_zero_outside_component
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (z : (compressedCorridorGraph D hendpoints).CycleSpace)
    (a : (activeSubgraph G).Edge)
    (hother : edgeComponent G a ≠ c) :
    (compressedComponentLift D hnonempty hendpoints z).1 (originalActiveEdge G a) = 0 := by
  change (includeSelectedComponent G c
      ((selectedComponentToMultiGraphEquiv G c).symm
        ((compressedCorridor_cycleEquiv D hnonempty hendpoints) z))).1
      (originalActiveEdge G a) = 0
  exact includeSelectedComponent_zero_outside_component _ a hother

/-- The same coordinate has the expected selected-route support indicator. -/
theorem compressedComponentLift_indicator_on_component_edge
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (z : (compressedCorridorGraph D hendpoints).CycleSpace)
    (p : ComponentRouteGraph.Edge) :
    (compressedComponentLift D hnonempty hendpoints z).1
        (componentCorridorEdgeToOriginal G c p) =
      if ∃ e, z.1 e ≠ 0 ∧
          p ∈ (compressedCorridorRouteSystem D hnonempty hendpoints).support e
      then 1 else 0 := by
  rw [compressedComponentLift_coordinate_on_component_edge]
  have hword :
      ((compressedCorridor_cycleEquiv D hnonempty hendpoints) z).1 =
        expand (compressedCorridorGraph D hendpoints) ComponentRouteGraph
          (compressedCorridorRouteSystem D hnonempty hendpoints) z.1 := by
    rfl
  rw [hword]
  exact routeExpansion_eq_indicator
    (compressedCorridorRouteSystem D hnonempty hendpoints) z p



/-- The active-component label is c for every edge transported from the
component graph. -/
theorem edgeComponent_componentCorridorEdge (q : ComponentRouteGraph.Edge) :
    edgeComponent G
      (((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) q).1) = c := by
  apply (mem_componentEdges_iff G c _).mp
  exact ((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) q).2

/-- If an original active edge is the reindexing of a component edge, its
active-component label is c. -/
theorem edgeComponent_eq_c_of_componentCorridorEdgeToOriginal
    (p : G.Edge) (hp : p ∈ activeEdges G)
    (q : ComponentRouteGraph.Edge)
    (hqp : componentCorridorEdgeToOriginal G c q = p) :
    edgeComponent G
      ((G.restrictedEdgeEquiv (activeEdges G)).symm ⟨p, hp⟩) = c := by
  let a := (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨p, hp⟩
  let b := ((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) q).1
  have hab : a = b := by
    apply (G.restrictedEdgeEquiv (activeEdges G)).injective
    apply Subtype.ext
    simpa [a, b, componentCorridorEdgeToOriginal, originalActiveEdge] using hqp.symm
  change edgeComponent G a = c
  rw [hab]
  exact edgeComponent_componentCorridorEdge q

/-- Membership of a component-edge image in a reindexed corridor is exactly
membership of the preimage edge in the component corridor. -/
theorem compressedComponentPath_image_support_iff
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (e : (compressedCorridorGraph D hendpoints).Edge)
    (q : ComponentRouteGraph.Edge) :
    componentCorridorEdgeToOriginal G c q ∈
        (compressedComponentEdgePath D hnonempty hendpoints e).support ↔
      q ∈ (corridorAt D e).support := by
  change componentCorridorEdgeToOriginal G c q ∈
      (componentCorridorToOriginal G c (corridorAt D e)).support ↔ _
  rw [componentCorridorToOriginal_support]
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, heq⟩
    have hrq := componentCorridorEdgeToOriginal_injective G c heq
    simpa [hrq] using hr
  · intro hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- Global path expansion for the selected-component cleanup lift. -/
theorem compressedComponentLift_is_path_expansion
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀)
    (z : (compressedCorridorGraph D hendpoints).CycleSpace)
    (p : G.Edge) :
    (compressedComponentLift D hnonempty hendpoints z).1 p =
      if ∃ e, z.1 e ≠ 0 ∧
          p ∈ (compressedComponentEdgePath D hnonempty hendpoints e).support
      then 1 else 0 := by
  classical
  by_cases hpactive : p ∈ activeEdges G
  · let a := (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨p, hpactive⟩
    by_cases hcomponent : edgeComponent G a = c
    · have hmem : a ∈ componentEdges G c :=
        (mem_componentEdges_iff G c a).mpr hcomponent
      let q := ((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c)).symm
        ⟨a, hmem⟩
      have hpq : componentCorridorEdgeToOriginal G c q = p := by
        simp [componentCorridorEdgeToOriginal, originalActiveEdge, a, q]
      rw [← hpq]
      rw [compressedComponentLift_indicator_on_component_edge]
      congr 1
      apply propext
      constructor
      · rintro ⟨e, he, hroute⟩
        refine ⟨e, he, ?_⟩
        exact (compressedComponentPath_image_support_iff D hnonempty hendpoints e q).2 hroute
      · rintro ⟨e, he, hpath⟩
        refine ⟨e, he, ?_⟩
        exact (compressedComponentPath_image_support_iff D hnonempty hendpoints e q).1 hpath
    · have hlift : (compressedComponentLift D hnonempty hendpoints z).1 p = 0 := by
        have hpa : originalActiveEdge G a = p := by
          simp [originalActiveEdge, a]
        rw [← hpa]
        exact compressedComponentLift_zero_outside_component D hnonempty hendpoints z a hcomponent
      have hnot : ¬ ∃ e, z.1 e ≠ 0 ∧
          p ∈ (compressedComponentEdgePath D hnonempty hendpoints e).support := by
        rintro ⟨e, he, hpPath⟩
        change p ∈ (componentCorridorToOriginal G c (corridorAt D e)).support at hpPath
        rw [componentCorridorToOriginal_support] at hpPath
        rcases Finset.mem_image.mp hpPath with ⟨q, hq, hqp⟩
        have hqcomp := edgeComponent_eq_c_of_componentCorridorEdgeToOriginal
          p hpactive q hqp
        exact hcomponent hqcomp
      rw [hlift]
      simp [hnot]
  · have hlift : (compressedComponentLift D hnonempty hendpoints z).1 p = 0 :=
      cycle_word_zero_off_active_edges G
        (compressedComponentLift D hnonempty hendpoints z) p hpactive
    have hnot : ¬ ∃ e, z.1 e ≠ 0 ∧
        p ∈ (compressedComponentEdgePath D hnonempty hendpoints e).support := by
      rintro ⟨e, he, hpPath⟩
      change p ∈ (componentCorridorToOriginal G c (corridorAt D e)).support at hpPath
      rw [componentCorridorToOriginal_support] at hpPath
      rcases Finset.mem_image.mp hpPath with ⟨q, hq, hqp⟩
      have hp' : p ∈ activeEdges G := by
        rw [← hqp]
        exact componentCorridorEdgeToOriginal_mem_activeEdges q
      exact hpactive hp'
    rw [hlift]
    simp [hnot]



/-- Component-level cleanup fields induced by the compressed corridor
partition. -/
structure CompressedComponentCleanupData
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) where
  marginal : G.CycleSpace →ₗ[F₂] (compressedCorridorGraph D hendpoints).CycleSpace
  marginal_surjective : Function.Surjective marginal
  liftCycles : (compressedCorridorGraph D hendpoints).CycleSpace →ₗ[F₂] G.CycleSpace
  marginal_lift : ∀ z, marginal (liftCycles z) = z
  vertexMap : (compressedCorridorGraph D hendpoints).Vertex → G.Vertex
  edgePath : (compressedCorridorGraph D hendpoints).Edge → PhysicalCorridor G
  edgeRepresentative : (compressedCorridorGraph D hendpoints).Edge → G.Edge
  edgeRepresentative_mem : ∀ e, edgeRepresentative e ∈ (edgePath e).support
  marginal_reads_representatives : ∀ x : G.CycleSpace,
    ∀ e : (compressedCorridorGraph D hendpoints).Edge,
      (marginal x).1 e = x.1 (edgeRepresentative e)
  edgePaths_disjoint : ∀ e f, e ≠ f →
    Disjoint (edgePath e).support (edgePath f).support
  path_endpoints : ∀ e,
    (((edgePath e).vertices.head? = some (vertexMap ((compressedCorridorGraph D hendpoints).src e)) ∧
       (edgePath e).vertices.getLast? = some (vertexMap ((compressedCorridorGraph D hendpoints).dst e))) ∨
      ((edgePath e).vertices.head? = some (vertexMap ((compressedCorridorGraph D hendpoints).dst e)) ∧
       (edgePath e).vertices.getLast? = some (vertexMap ((compressedCorridorGraph D hendpoints).src e))))
  path_active : ∀ e p, p ∈ (edgePath e).support → ActiveEdge G p
  lift_is_path_expansion : ∀ x : (compressedCorridorGraph D hendpoints).CycleSpace,
    ∀ p : G.Edge,
      (liftCycles x).1 p =
        if ∃ e, x.1 e ≠ 0 ∧ p ∈ (edgePath e).support then 1 else 0

/-- Assemble the exact selected-component cleanup fields from a compressed
corridor partition. -/
noncomputable def compressedComponentCleanupData
    (D : CorridorPartition ComponentPhysicalGraph P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch ComponentPhysicalGraph P₀ ∧
      corridorFinish C ∈ protectedOrBranch ComponentPhysicalGraph P₀) :
    CompressedComponentCleanupData D hnonempty hendpoints := by
  classical
  refine ⟨compressedComponentMarginal D hnonempty hendpoints, ?_,
    compressedComponentLift D hnonempty hendpoints, ?_,
    compressedComponentVertexMap D hnonempty hendpoints,
    compressedComponentEdgePath D hnonempty hendpoints,
    (fun e => componentCorridorEdgeToOriginal G c
      (compressedComponentRepresentative D hnonempty hendpoints e)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact compressedComponentMarginal_surjective D hnonempty hendpoints
  · exact compressedComponentMarginal_lift D hnonempty hendpoints
  · intro e
    exact componentCorridor_support_mem_transfer G c (corridorAt D e)
      (compressedComponentRepresentative_mem D hnonempty hendpoints e)
  · intro x e
    exact compressedComponentMarginal_reads_representative D hnonempty hendpoints x e
  · intro e f hef
    change Disjoint ((componentCorridorToOriginal G c (corridorAt D e)).support)
      ((componentCorridorToOriginal G c (corridorAt D f)).support)
    rw [componentCorridorToOriginal_support, componentCorridorToOriginal_support]
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    rcases Finset.mem_image.mp hq1 with ⟨p, hp, hpq⟩
    rcases Finset.mem_image.mp hq2 with ⟨r, hr, hrq⟩
    have hpr : p = r := componentCorridorEdgeToOriginal_injective G c (hpq.trans hrq.symm)
    have hget : Function.Injective (corridorFamily D).get :=
      (List.nodup_iff_injective_get).mp (Finset.nodup_toList D.corridors.toFinset)
    have hcorr : corridorAt D e ≠ corridorAt D f := by
      intro h
      exact hef (hget h)
    have hdis := D.edge_disjoint (corridorAt D e) (corridorAt_mem D e)
      (corridorAt D f) (corridorAt_mem D f) hcorr
    have hnot := (Finset.disjoint_left.mp hdis) hp
    exact hnot (hpr ▸ hr)
  · intro e
    left
    constructor
    · change (corridorAt D e).vertices.head? = _
      rw [corridorStart_head?]
      simp [compressedComponentVertexMap, compressedCorridor_src_image]
    · change (corridorAt D e).vertices.getLast? = _
      rw [corridorFinish_getLast?]
      simp [compressedComponentVertexMap, compressedCorridor_dst_image]
  · intro e p hp
    exact compressedComponentPath_edge_active D hnonempty hendpoints e p hp
  · intro x p
    exact compressedComponentLift_is_path_expansion D hnonempty hendpoints x p

end Erdos1016.Proof.CompressedComponentLift

end

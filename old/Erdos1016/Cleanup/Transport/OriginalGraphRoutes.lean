import Erdos1016.Cleanup.Root.ProtectedRootConstruction
import Erdos1016.Cleanup.Transport.OutputFromReducedCertificate
import Erdos1016.Cleanup.Transport.ReducedRouteEndpointLabels

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Erdos1016.Proof.OriginalGraphRoutes

open Erdos1016 FiniteMultiGraph
open ActivePhysicalComponents
open CleanupSpecification PhysicalPartition
open SingleCorridorRoute PhysicalDegreeTwoCoreComponents
open CompressedRouteDecomposition PartitionRouteDecomposition
open RestrictedComponentGraph ComponentCorridorReindexing
open CorridorRouteEquivalence ReducedForestEventTransfer
open ComponentWitnessCorridorGeometry

variable {G : PhysicalGraph} (c : ActiveComponent G)
variable {P : Finset (componentSupportPhysical G c).Vertex}
variable {W : Finset (componentSupportPhysical G c).Edge}
variable (D : CorridorPartition (componentSupportPhysical G c) P W)
variable (hne : ∀ C ∈ D.corridors, C.edges ≠ [])
variable (hend : CorridorParallelPairCount.Endpoints D)

abbrev edgeMap (e : (componentSupportPhysical G c).Edge) : G.Edge :=
  componentCorridorEdgeToOriginal G c (componentSupportEdgeEquiv G c e)

theorem edgeMap_injective : Function.Injective (edgeMap c) :=
  (componentCorridorEdgeToOriginal_injective G c).comp (componentSupportEdgeEquiv G c).injective

abbrev vertexMap (q : (compressedCorridorGraph D hend).Vertex) : G.Vertex :=
  componentSupportVertexMap G c (compressedCorridorVertexMap D hend q)

def edgePath (e : (compressedCorridorGraph D hend).Edge) : PhysicalCorridor G :=
  componentCorridorToOriginal G c (componentSupportCorridorToRestricted G c (corridorAt D e))

theorem edgePath_support (e : (compressedCorridorGraph D hend).Edge) :
    (edgePath c D hend e).support = (corridorAt D e).support.image (edgeMap c) := by
  rw [edgePath, componentCorridorToOriginal_support, componentSupportCorridorToRestricted_support]
  rw [Finset.image_image]
  rfl

include hne in
theorem edgePath_nonempty (e : (compressedCorridorGraph D hend).Edge) :
    (edgePath c D hend e).edges ≠ [] := by
  simpa [edgePath, componentCorridorToOriginal, componentSupportCorridorToRestricted] using
    hne (corridorAt D e) (corridorAt_mem D e)

theorem edgePath_endpoints (e : (compressedCorridorGraph D hend).Edge) :
    (edgePath c D hend e).vertices.head? = some (vertexMap c D hend ((compressedCorridorGraph D hend).src e)) ∧
    (edgePath c D hend e).vertices.getLast? = some (vertexMap c D hend ((compressedCorridorGraph D hend).dst e)) := by
  constructor
  · simp [edgePath, componentCorridorToOriginal, componentSupportCorridorToRestricted,
      vertexMap, corridorStart_head?]
  · simp [edgePath, componentCorridorToOriginal, componentSupportCorridorToRestricted,
      vertexMap, corridorFinish_getLast?]

include hne in
theorem edgePath_disjoint (e f : (compressedCorridorGraph D hend).Edge) (hef : e ≠ f) :
    Disjoint (edgePath c D hend e).support (edgePath c D hend f).support := by
  rw [edgePath_support, edgePath_support]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hq
  have hba := edgeMap_injective c hab
  subst b
  exact Finset.disjoint_left.mp ((compressedCorridorRouteSystem D hne hend).disjoint hef) ha hb

/-- Original paths satisfy the endpoint boundary identity regardless of
inactive edges incident at their interiors. -/
def routeSystem : EdgeDisjointRouteSystem (compressedCorridorGraph D hend) (reducedRouteGraph G) where
  vertexMap := vertexMap c D hend
  support e := (edgePath c D hend e).support
  endpoint := by
    intro e
    have hb := EndpointBoundary.corridorEndpointBoundary (edgePath c D hend e)
    have hs : corridorStart (edgePath c D hend e) = vertexMap c D hend ((compressedCorridorGraph D hend).src e) := by
      exact Option.some.inj ((corridorStart_head? _).symm.trans (edgePath_endpoints c D hend e).1)
    have ht : corridorFinish (edgePath c D hend e) = vertexMap c D hend ((compressedCorridorGraph D hend).dst e) := by
      exact Option.some.inj ((corridorFinish_getLast? _).symm.trans (edgePath_endpoints c D hend e).2)
    unfold CorridorEndpointBoundary at hb
    convert hb using 1
    ext v
    simp [endpointDemand, oneEdgeGraph, hs, ht]
  disjoint := edgePath_disjoint c D hne hend
  nonempty := by
    intro e
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (edgePath_nonempty c D hne hend e)
    exact ⟨p, List.mem_toFinset.mpr hp⟩

def marginal : G.CycleSpace →ₗ[ZMod 2] (compressedCorridorGraph D hend).CycleSpace :=
  (compressedCorridor_cycleEquiv D hne hend).symm.toLinearMap.comp
    ((physicalCycleRouteEquiv (componentSupportPhysical G c)).toLinearMap.comp
      (SupportForestMarginal.marginal G c))

/-- All coordinates of each route, rather than only a chosen representative,
are read exactly by the compressed marginal. -/
theorem marginal_coordinate (x : G.CycleSpace) (e : (compressedCorridorGraph D hend).Edge)
    (p : (componentSupportPhysical G c).Edge) (hp : p ∈ (corridorAt D e).support) :
    (marginal c D hne hend x).1 e = x.1 (edgeMap c p) := by
  let E := compressedCorridor_cycleEquiv D hne hend
  let y := physicalCycleRouteEquiv (componentSupportPhysical G c)
    (SupportForestMarginal.marginal G c x)
  have hcoord := congrFun (congrArg Subtype.val (E.apply_symm_apply y)) p
  change expand (compressedCorridorGraph D hend) (routeGraph (componentSupportPhysical G c))
    (compressedCorridorRouteSystem D hne hend) (E.symm y).1 p = y.1 p at hcoord
  have hexpand := expand_apply_of_mem_support (compressedCorridorGraph D hend)
    (routeGraph (componentSupportPhysical G c)) (compressedCorridorRouteSystem D hne hend)
    (E.symm y).1 e p hp
  rw [hexpand] at hcoord
  exact hcoord.trans (SupportForestMarginal.marginal_coordinate G c x p)

theorem marginal_on_path (x : G.CycleSpace) (e : (compressedCorridorGraph D hend).Edge)
    (p : G.Edge) (hp : p ∈ (edgePath c D hend e).support) :
    (marginal c D hne hend x).1 e = x.1 p := by
  rw [edgePath_support] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact marginal_coordinate c D hne hend x e q hq

/-- The section is actual corridor expansion in the original cycle space. -/
def liftCycles : (compressedCorridorGraph D hend).CycleSpace →ₗ[ZMod 2] G.CycleSpace :=
  (physicalCycleRouteEquiv G).symm.toLinearMap.comp (cycleExpandMap (routeSystem c D hne hend))

theorem lift_is_path_expansion (x : (compressedCorridorGraph D hend).CycleSpace) (p : G.Edge) :
    (liftCycles c D hne hend x).1 p =
      if ∃ e, x.1 e ≠ 0 ∧ p ∈ (edgePath c D hend e).support then 1 else 0 := by
  exact CompressedComponentLift.routeExpansion_eq_indicator
    (routeSystem c D hne hend) x p

theorem marginal_lift (x : (compressedCorridorGraph D hend).CycleSpace) :
    marginal c D hne hend (liftCycles c D hne hend x) = x := by
  apply Subtype.ext
  funext e
  obtain ⟨p, hp⟩ := (compressedCorridorRouteSystem D hne hend).nonempty e
  rw [marginal_coordinate c D hne hend _ e p hp]
  change expand (compressedCorridorGraph D hend) (reducedRouteGraph G)
    (routeSystem c D hne hend) x.1 (edgeMap c p) = x.1 e
  apply expand_apply_of_mem_support
  change edgeMap c p ∈ (edgePath c D hend e).support
  rw [edgePath_support]
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem path_active (e : (compressedCorridorGraph D hend).Edge) (p : G.Edge)
    (hp : p ∈ (edgePath c D hend e).support) : ActiveEdge G p := by
  rw [edgePath_support] at hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have ha := CompressedComponentLift.componentCorridorEdgeToOriginal_mem_activeEdges
    (componentSupportEdgeEquiv G c q)
  obtain ⟨x, hx⟩ := (mem_activeEdges_iff G _).mp ha
  exact ⟨x, by rw [hx]; decide⟩

end Erdos1016.Proof.OriginalGraphRoutes

end

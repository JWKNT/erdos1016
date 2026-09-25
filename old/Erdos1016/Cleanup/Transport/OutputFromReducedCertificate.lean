import Erdos1016.Cleanup.Transport.ReducedForestEventTransfer

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.OutputFromReducedCertificate

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ReducedForestEventTransfer

variable {G : PhysicalGraph} {I : CleanupInput G}

/-- The geometric/ambient remainder of a cleanup certificate after route
transport and the pointwise good-event implication have been constructed. -/
structure CleanupOutputSupplement
    (C : ReducedEventTransportCertificate G I) where
  path_active : ∀ e p, p ∈ (C.edgePath e).support → ActiveEdge G p
  path_endpoints : ∀ e,
    (((C.edgePath e).vertices.head? = some (C.vertexMap (C.Γ.src e)) ∧
       (C.edgePath e).vertices.getLast? = some (C.vertexMap (C.Γ.dst e))) ∨
      ((C.edgePath e).vertices.head? = some (C.vertexMap (C.Γ.dst e)) ∧
       (C.edgePath e).vertices.getLast? = some (C.vertexMap (C.Γ.src e))))
  auxiliary_connected : C.Γ.toSimpleGraph.Connected
  root_proper : C.root.card < C.Γ.vertexCount
  root_order : I.r ≤ C.root.card * 2 ^ (8 * I.R)
  root_cut_bound : (cutEdges C.Γ C.root).card ≤ 2 ^ (5 * I.R)
  exterior_nonempty : 1 ≤ exteriorComponentCount C.Γ C.root
  exterior_bound : ∃ Cext : ℕ,
    exteriorComponentCount C.Γ C.root ≤ Cext * I.R ^ 2

/-- Reduced route data plus the remaining geometric estimates assembles an
actual `CleanupOutput`. In particular, the marginal surjectivity field is
derived from the explicit linear right inverse, and event transport is
supplied by `good_event_maps_of_reduced_routes` rather than assumed. -/
def toCleanupOutput
    (C : ReducedEventTransportCertificate G I)
    (S : CleanupOutputSupplement C) : CleanupOutput I := by
  refine
    { Γ := C.Γ
      root := C.root
      testEdges := C.testEdges
      marginal := C.marginal
      marginal_surjective := ?_
      liftCycles := C.liftCycles
      vertexMap := C.vertexMap
      edgePath := C.edgePath
      edgeRepresentative := C.edgeRepresentative
      edgeRepresentative_mem := C.edgeRepresentative_mem
      marginal_reads_representatives := C.marginal_reads_representatives
      edgePaths_disjoint := C.edgePaths_disjoint
      path_endpoints := S.path_endpoints
      path_active := S.path_active
      lift_is_path_expansion := C.lift_is_path_expansion
      marginal_lift := C.marginal_lift
      testEdges_internal := C.testEdges_internal
      tested_paths_in_complement := C.tested_paths_in_complement
      good_event_maps := ?_
      auxiliary_connected := S.auxiliary_connected
      root_proper := S.root_proper
      root_structure := C.root_structure
      root_cubic_ambient_degree := C.root_cubic_ambient_degree
      root_order := S.root_order
      root_cut_bound := S.root_cut_bound
      exterior_nonempty := S.exterior_nonempty
      exterior_bound := S.exterior_bound }
  · intro z
    exact ⟨C.liftCycles z, C.marginal_lift z⟩
  · exact C.good_event_maps_of_reduced_routes

end Erdos1016.Proof.OutputFromReducedCertificate

end

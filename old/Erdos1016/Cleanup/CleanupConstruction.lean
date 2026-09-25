import Erdos1016.Cleanup.Transport.OriginalGraphRoutes

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CleanupConstruction

open FiniteMultiGraph ActivePhysicalComponents
open CleanupSpecification PhysicalPartition
open SingleCorridorRoute PhysicalDegreeTwoCoreComponents
open PartitionRouteDecomposition
open CompressedRouteDecomposition
open RestrictedComponentGraph
open ComponentWitnessCorridorGeometry
open ProtectedRootConstruction ReducedForestEventTransfer
open OutputFromReducedCertificate
open ComponentExtraction ProtectedExteriorComponents

/-- The cleanup construction, including its probability transport, follows
from the original witness data. The exterior constant is uniform in the
graph and the witness size. -/
theorem exists_cleanup_output (G : PhysicalGraph) (I : CleanupInput G)
    (hR : 3926 ≤ I.R) :
    ∃ O : CleanupOutput I,
      exteriorComponentCount O.Γ O.root ≤ 1487 * I.R ^ 2 := by
  classical
  obtain ⟨c, _, D, hne, hend, s, hconn, _, hroot, hproper, hcubic, horder, hcut, hext⟩ :=
    exists_cleaned_root G I hR
  let Γ := compressedCorridorGraph D hend
  let P := fullProtection I c D hend
  let H := outsideComponentVertices Γ P s
  let A := OriginalGraphRoutes.routeSystem c D hne hend
  have haway : ∀ v ∈ H,
      compressedCorridorVertexMap D hend v ∉ componentWitnessBadProtected G c I := by
    intro v hv hprotected
    have hp : v ∈ componentSupportCompressedProtectedVertices G c D hend :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprotected⟩
    exact Finset.disjoint_left.mp (componentVertexSet_disjoint Γ.toSimpleGraph P s)
      hv (Finset.mem_union_left _ hp)
  have havoid : ∀ e ∈ internalEdges Γ H,
      ∀ p ∈ (OriginalGraphRoutes.edgePath c D hend e).support,
        p ∉ I.witnessEdges := by
    intro e he p hp hpW
    obtain ⟨hs, ht⟩ := (Finset.mem_filter.mp he).2
    have hstart : corridorStart (corridorAt D e) ∉ componentWitnessBadProtected G c I := by
      simpa only [Γ, compressedCorridor_src_image] using haway (Γ.src e) hs
    have hfinish : corridorFinish (corridorAt D e) ∉ componentWitnessBadProtected G c I := by
      simpa only [Γ, compressedCorridor_dst_image] using haway (Γ.dst e) ht
    have hdis := CorridorWitnessAvoidance.corridor_support_disjoint_witnesses
      D (componentWitnessBadProtected G c I) (componentLocalWitnessPullback_endpoints G c I)
      (corridorAt_mem D e) hstart hfinish
    rw [OriginalGraphRoutes.edgePath_support] at hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hqW : q ∈ componentLocalWitnessPullback G c I :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpW⟩
    exact Finset.disjoint_left.mp hdis hq hqW
  let C : ReducedEventTransportCertificate G I :=
    { Γ := Γ
      root := H
      testEdges := internalEdges Γ H
      marginal := OriginalGraphRoutes.marginal c D hne hend
      liftCycles := OriginalGraphRoutes.liftCycles c D hne hend
      vertexMap := OriginalGraphRoutes.vertexMap c D hend
      edgePath := OriginalGraphRoutes.edgePath c D hend
      edgeRepresentative := fun e => (A.nonempty e).choose
      edgeRepresentative_mem := fun e => (A.nonempty e).choose_spec
      marginal_reads_representatives := fun x e =>
        OriginalGraphRoutes.marginal_on_path c D hne hend x e _ (A.nonempty e).choose_spec
      routeSystem := A
      path_cycle_constant := by
        intro x e p q hp hq
        exact (OriginalGraphRoutes.marginal_on_path c D hne hend x e p hp).symm.trans
          (OriginalGraphRoutes.marginal_on_path c D hne hend x e q hq)
      route_support_eq_path := fun _ => rfl
      lift_is_path_expansion := OriginalGraphRoutes.lift_is_path_expansion c D hne hend
      marginal_lift := OriginalGraphRoutes.marginal_lift c D hne hend
      testEdges_internal := rfl
      tested_paths_in_complement := havoid
      endpoint_edges :=
        ReducedRouteEndpointLabels.endpoint_edges_of_corridor_endpoint_options
          (OriginalGraphRoutes.vertexMap c D hend) (OriginalGraphRoutes.edgePath c D hend)
          (OriginalGraphRoutes.edgePath_nonempty c D hne hend)
          (fun e => Or.inl (OriginalGraphRoutes.edgePath_endpoints c D hend e))
      root_structure := hroot
      root_cubic_ambient_degree := hcubic }
  let S : CleanupOutputSupplement C :=
    { path_active := OriginalGraphRoutes.path_active c D hend
      path_endpoints := fun e => Or.inl (OriginalGraphRoutes.edgePath_endpoints c D hend e)
      auxiliary_connected := hconn
      root_proper := hproper
      root_order := horder
      root_cut_bound := hcut
      exterior_nonempty :=
        ProperRootBoundary.exteriorComponentCount_pos_of_proper Γ H hproper
      exterior_bound := ⟨1487, hext⟩ }
  exact ⟨toCleanupOutput C S, hext⟩

/-- Proposition 8.1, with explicit absolute constants. -/
theorem cleanupProposition : CleanupProposition :=
  ⟨1487, 3926, by decide, exists_cleanup_output⟩

end Erdos1016.Proof.CleanupConstruction

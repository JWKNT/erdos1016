import Erdos1016.Cleanup.Transport.SupportForestMarginal
import Erdos1016.Cleanup.Protection.UnprotectedLoopExclusion

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ParallelPairProtection

open Erdos1016
open ActivePhysicalComponents ActiveComponentRankSum
open CleanupSpecification PhysicalPartition
open CorridorPairedPathCertificates PhysicalDegreeTwoCoreComponents
open CompressedRouteDecomposition
open RestrictedComponentGraph
open ComponentWitnessCorridorGeometry
open CorridorParallelPairCount
open ParallelProtectionComplement
open PostProtectionSimplicity
open ParallelEndpointCardinality
open ProtectedDeletionRankLedger

/-- The raw support component has degree two or three away from the actual
witness endpoints and bad vertices selected by the cleanup input. -/
theorem support_degree_two_or_three
    (G : PhysicalGraph) (I : CleanupInput G) (c : ActiveComponent G)
    (hc : c ∈ nonemptyActiveComponents G)
    (v : (componentSupportPhysical G c).Vertex)
    (hv : v ∉ componentWitnessBadProtected G c I) :
    (componentSupportPhysical G c).degree v = 2 ∨
      (componentSupportPhysical G c).degree v = 3 := by
  classical
  have hne : (componentEdges G c).Nonempty := (Finset.mem_filter.mp hc).2
  obtain ⟨e, he⟩ := hne
  have hec := (mem_componentEdges_iff G c e).mp he
  have hnotWitness : componentSupportVertexMap G c v ∉ I.witnessVertices := by
    intro h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_left _ h⟩)
  have hnotBad : componentSupportVertexMap G c v ∉
      BadVertexCardinalityBound.badVertexSet G I.witnessEdges := by
    intro h
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ h⟩)
  have hlocal := active_degree_eq_two_or_three_off_witness_bad G I I.R
    (componentSupportVertexMap G c v) (componentSupportVertex_incident_of_edge G c e hec v)
    hnotWitness hnotBad I.outside_probability
  have hphysical : (componentSupportPhysical G c).degree v =
      (activeSubgraph G).degree (componentSupportVertexMap G c v) := by
    have h := componentSupportPhysical_degree_eq G c
      ((Fintype.equivFin (BoundaryTrace.Network.Shore.InsideVertex
        (componentSupportFinset G c))).symm v)
    calc
      (componentSupportPhysical G c).degree v =
          (activeSubgraph G).toSimpleGraph.degree (componentSupportVertexMap G c v) := by
        simpa [componentSupportVertexMap] using h
      _ = (activeSubgraph G).degree (componentSupportVertexMap G c v) :=
        (Nonbacktracking.FiniteTwoCore.original_degree_eq_graph_degree _ _).symm
  simpa [hphysical] using hlocal

/-- Every eligible pair in a selected cleanup component is counted directly
from the original cleanup input. The absolute constant is uniform in G,I,c,D. -/
theorem pair_count_lt_481_mul_sq
    (G : PhysicalGraph) (I : CleanupInput G) (c : ActiveComponent G)
    (hc : c ∈ nonemptyActiveComponents G) (hR : 5 ≤ I.R)
    (D : CorridorPartition (componentSupportPhysical G c)
      (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I))
    (hne : ∀ C ∈ D.corridors, C.edges ≠ []) (hend : Endpoints D) :
    (eligibleUnorderedParallelPairIndices (compressedCorridorGraph D hend)
      (componentSupportCompressedProtectedVertices G c D hend)).card < 481 * I.R ^ 2 := by
  have hprob := SupportForestMarginal.outside_probability_gt_cutoff G I c
  have hhalf : (1 / 2 : ℝ) <
      (componentSupportPhysical G c).outsideLinearForestProbability
        (componentLocalWitnessPullback G c I) := by
    have hinv : 0 ≤ 1 / (I.R : ℝ) := by positivity
    linarith
  have hW := componentLocalWitnessPullback_endpoints G c I
  have hloop := UnprotectedLoopExclusion.no_unprotected_loop D hne hend hW hhalf
  have hcount := pair_count_lt D hne hend (support_degree_two_or_three G I c hc)
    hW (componentSupportPhysical_connected G c) hloop I.R hR hprob
  change (eligibleUnorderedParallelPairIndices (compressedCorridorGraph D hend)
    (componentSupportCompressedProtectedVertices G c D hend)).card < _ at hcount
  nlinarith

/-- The new endpoint protection has a uniform quadratic cardinality bound. -/
theorem parallel_protection_card_lt
    (G : PhysicalGraph) (I : CleanupInput G) (c : ActiveComponent G)
    (hc : c ∈ nonemptyActiveComponents G) (hR : 5 ≤ I.R)
    (D : CorridorPartition (componentSupportPhysical G c)
      (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I))
    (hne : ∀ C ∈ D.corridors, C.edges ≠ []) (hend : Endpoints D) :
    (protectParallelEndpoints (compressedCorridorGraph D hend)
      (componentSupportCompressedProtectedVertices G c D hend)).card < 2 * 481 * I.R ^ 2 := by
  have hpair := pair_count_lt_481_mul_sq G I c hc hR D hne hend
  have hcard := protectParallelEndpoints_card_le_two_mul_unorderedPairCount
    (compressedCorridorGraph D hend) (componentSupportCompressedProtectedVertices G c D hend)
  nlinarith

/-- The full protected-edge deletion budget, including the otherwise missed
witness incidences, is now derived from the cleanup input. -/
theorem protected_incident_budget
    (G : PhysicalGraph) (I : CleanupInput G) (c : ActiveComponent G)
    (hc : c ∈ nonemptyActiveComponents G) (hR : 5 ≤ I.R)
    (D : CorridorPartition (componentSupportPhysical G c)
      (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I))
    (hne : ∀ C ∈ D.corridors, C.edges ≠ []) (hend : Endpoints D) :
    (protectedIncidentEdges (compressedCorridorGraph D hend)
      (componentSupportCompressedProtectedVertices G c D hend ∪
        protectParallelEndpoints (compressedCorridorGraph D hend)
          (componentSupportCompressedProtectedVertices G c D hend))).card ≤
      (I.R + 1) * (I.witnessEdges.card + 520 * I.R) +
        2 * I.witnessEdges.card + 6 * 481 * I.R ^ 2 := by
  have hpair := (pair_count_lt_481_mul_sq G I c hc hR D hne hend).le
  have hsum := componentSupport_compressed_degree_sum_le_cleanup_budget G c I D hne hend hR
  have hdegree : ∀ q, q ∉ componentSupportCompressedProtectedVertices G c D hend →
      ambientDegree (compressedCorridorGraph D hend) q = 2 ∨
        ambientDegree (compressedCorridorGraph D hend) q = 3 := by
    intro q hq
    right
    apply RankedCubicCompression.compressed_degree_three_off_protected D hne hend q
    exact fun h => hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hbudget := protected_incident_budget_of_degree_sum_and_pair_count
    (compressedCorridorGraph D hend) (componentSupportCompressedProtectedVertices G c D hend)
    I.R I.witnessEdges.card (481 * I.R ^ 2) hsum hdegree hpair
  have hcard := (componentSupportCompressedProtectedVertices_card_le G c D hend).trans
    (componentWitnessBadProtected_card_le_of_cleanup_input G c I hR)
  have hmul := Nat.mul_le_mul_left (I.R + 1) hcard
  nlinarith

end Erdos1016.Proof.ParallelPairProtection

end

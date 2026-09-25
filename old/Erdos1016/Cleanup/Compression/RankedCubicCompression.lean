import Erdos1016.Cleanup.Support.ComponentWitnessCorridorGeometry
import Erdos1016.Cleanup.Support.WitnessActiveComponentCount
import Erdos1016.Cleanup.Transport.CorridorRouteEquivalence

set_option autoImplicit false

/-!
# Constructing the ranked cubic compression from the cleanup input

The active-component count, corridor partition, rank preservation, and degree
bounds are proved from the cleanup input. No reduced-output certificate is
assumed. Protected witness incidences are charged in aggregate by `2m`.
-/

noncomputable section

namespace Erdos1016.Proof.RankedCubicCompression

open Erdos1016
open ActivePhysicalComponents ActiveComponentRankSum
open CleanupSpecification PhysicalPartition
open CorridorPairedPathCertificates PhysicalDegreeTwoCoreComponents
open CompressedRouteDecomposition
open RestrictedComponentGraph
open ComponentWitnessCorridorGeometry
open WitnessActiveComponentCount

/-- Every retained unprotected vertex has degree exactly three: degree-two
vertices are the ones suppressed by the canonical compression. -/
theorem compressed_degree_three_off_protected
    {H : PhysicalGraph} {P : Finset H.Vertex} {W : Finset H.Edge}
    (D : CorridorPartition H P W)
    (hne : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch H P ∧
      corridorFinish C ∈ protectedOrBranch H P)
    (q : (compressedCorridorGraph D hend).Vertex)
    (hq : compressedCorridorVertexMap D hend q ∉ P) :
    ambientDegree (compressedCorridorGraph D hend) q = 3 := by
  rw [EndpointIncidenceBijection.compressedCorridor_ambientDegree_eq_physical_degree
    D hne hend q]
  have hmem : compressedCorridorVertexMap D hend q ∈ protectedOrBranch H P :=
    ((retainedVertexEquiv (G := H) (P₀ := P)) q).2
  rcases Finset.mem_union.mp hmem with hp | hd
  · exact (hq hp).elim
  · exact (Finset.mem_filter.mp hd).2

/-- Suppression preserves the complete component cycle space and its rank. -/
theorem compressed_cycleRank_eq
    {H : PhysicalGraph} {P : Finset H.Vertex} {W : Finset H.Edge}
    (D : CorridorPartition H P W)
    (hne : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch H P ∧
      corridorFinish C ∈ protectedOrBranch H P) :
    (compressedCorridorGraph D hend).cycleRank = H.cycleRank := by
  exact ((compressedCorridor_cycleEquiv D hne hend).trans
    (CorridorRouteEquivalence.physicalCycleRouteEquiv H).symm).finrank_eq

/-- The witness-component budget actually gives the required active-component
screen; it is not an extra hypothesis of the constructor. -/
theorem active_component_count (G : PhysicalGraph) (I : CleanupInput G) :
    (nonemptyActiveComponents G).card < 5 * I.R := by
  classical
  have h := nonempty_active_component_card_lt_five_R I I.witness_components
  simpa [nonemptyActiveComponents, Fintype.card_subtype] using h

/-- An actual compressed component with its rank share, cubic complement,
initial protection cardinality, and correct protected incidence sum. -/
theorem exists_ranked_cubic_compression
    (G : PhysicalGraph) (I : CleanupInput G) (hR : 5 ≤ I.R) :
    ∃ c ∈ nonemptyActiveComponents G,
      ∃ D : CorridorPartition (componentSupportPhysical G c)
          (componentWitnessBadProtected G c I)
          (componentLocalWitnessPullback G c I),
      ∃ hne : ∀ C ∈ D.corridors, C.edges ≠ [],
      ∃ hend : ∀ C ∈ D.corridors,
          corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c)
            (componentWitnessBadProtected G c I) ∧
          corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c)
            (componentWitnessBadProtected G c I),
        (componentWitnessBadProtected G c I).Nonempty ∧
        (compressedCorridorGraph D hend).toSimpleGraph.Connected ∧
        I.r ≤ 5 * I.R * (compressedCorridorGraph D hend).cycleRank ∧
        (∀ q, q ∉ componentSupportCompressedProtectedVertices G c D hend →
          ambientDegree (compressedCorridorGraph D hend) q = 3) ∧
        (componentSupportCompressedProtectedVertices G c D hend).card ≤
          I.witnessEdges.card + 520 * I.R ∧
        (∑ q ∈ componentSupportCompressedProtectedVertices G c D hend,
          ambientDegree (compressedCorridorGraph D hend) q) ≤
          (I.R + 1) * (componentSupportCompressedProtectedVertices G c D hend).card +
            2 * I.witnessEdges.card := by
  classical
  have hrank : 0 < G.cycleRank := by
    rw [I.graph_rank]
    exact (Nat.two_pow_pos _).trans_le I.rank_large
  obtain ⟨c, hc, D, hne, hend, hP, hconn, hshare⟩ :=
    exists_large_rank_component_local_corridor_partition_connected G I
      (active_component_count G I) hrank
  refine ⟨c, hc, D, hne, hend, hP, hconn, ?_, ?_, ?_, ?_⟩
  · rw [compressed_cycleRank_eq D hne hend, ← I.graph_rank]
    exact hshare
  · intro q hq
    apply compressed_degree_three_off_protected D hne hend q
    intro hp
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  · exact (componentSupportCompressedProtectedVertices_card_le G c D hend).trans
      (componentWitnessBadProtected_card_le_of_cleanup_input G c I hR)
  · exact componentSupport_compressed_degree_sum_le_cleanup_budget G c I D hne hend hR

end Erdos1016.Proof.RankedCubicCompression

end

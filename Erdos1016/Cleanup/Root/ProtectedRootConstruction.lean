import Erdos1016.Cleanup.Protection.WitnessComponentProtection
import Erdos1016.Cleanup.Protection.DeletionBudgetBounds
import Erdos1016.Cleanup.Root.ActiveRankExtraction

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Erdos1016.Proof.ProtectedRootConstruction

open Erdos1016
open ActivePhysicalComponents ActiveComponentRankSum
open CleanupSpecification PhysicalPartition
open CorridorPairedPathCertificates PhysicalDegreeTwoCoreComponents
open CompressedRouteDecomposition
open RestrictedComponentGraph
open ComponentWitnessCorridorGeometry
open RankedCubicCompression ParallelPairProtection
open DeletionBudgetBounds WitnessComponentProtection
open ProtectedDeletionRankLedger PostProtectionSimplicity
open ComponentExtraction OutsideComponentPartitions

/-- The full protected set of the actual compression. -/
def fullProtection {G : PhysicalGraph} (I : CleanupInput G) (c : ActiveComponent G)
    (D : CorridorPartition (componentSupportPhysical G c)
      (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I))
    (hend : CorridorParallelPairCount.Endpoints D) :
    Finset (compressedCorridorGraph D hend).Vertex :=
  componentSupportCompressedProtectedVertices G c D hend ∪
    protectParallelEndpoints (compressedCorridorGraph D hend)
      (componentSupportCompressedProtectedVertices G c D hend)

/-- The canonical compression has an actual simple cubic root at the original
rank scale, with the paper's cut bound and a uniform quadratic exterior bound.
Every input here is part of `CleanupInput`; the constants are explicit. -/
theorem exists_cleaned_root (G : PhysicalGraph) (I : CleanupInput G)
    (hR : 3926 ≤ I.R) :
    ∃ c ∈ nonemptyActiveComponents G,
    ∃ D : CorridorPartition (componentSupportPhysical G c)
      (componentWitnessBadProtected G c I) (componentLocalWitnessPullback G c I),
    ∃ hne : ∀ C ∈ D.corridors, C.edges ≠ [],
    ∃ hend : CorridorParallelPairCount.Endpoints D,
    ∃ s : OutsideComponent (compressedCorridorGraph D hend) (fullProtection I c D hend),
      (compressedCorridorGraph D hend).toSimpleGraph.Connected ∧
      0 < outsideComponentRank (compressedCorridorGraph D hend) (fullProtection I c D hend) s ∧
      IsCleanupRoot (compressedCorridorGraph D hend)
        (outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s) ∧
      (outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s).card <
        (compressedCorridorGraph D hend).vertexCount ∧
      (∀ v ∈ outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s,
        ambientDegree (compressedCorridorGraph D hend) v = 3) ∧
      I.r ≤ (outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s).card *
        2 ^ (8 * I.R) ∧
      (cutEdges (compressedCorridorGraph D hend)
        (outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s)).card ≤
        2 ^ (5 * I.R) ∧
      exteriorComponentCount (compressedCorridorGraph D hend)
        (outsideComponentVertices (compressedCorridorGraph D hend) (fullProtection I c D hend) s) ≤
        1487 * I.R ^ 2 := by
  classical
  have hR5 : 5 ≤ I.R := by omega
  obtain ⟨c, hc, D, hne, hend, hP, hconn, hshare, hcubic, _, _⟩ :=
    exists_ranked_cubic_compression G I hR5
  let Γ := compressedCorridorGraph D hend
  let P₀ := componentSupportCompressedProtectedVertices G c D hend
  let P := fullProtection I c D hend
  let A := deletionBudget I.R I.witnessEdges.card
  have hP₀ : P₀.Nonempty := by
    obtain ⟨v, hv⟩ := hP
    let Q := protectedOrBranch (componentSupportPhysical G c) (componentWitnessBadProtected G c I)
    have hvQ : v ∈ Q := Finset.mem_union_left _ hv
    let q : Γ.Vertex := Finset.equivFin Q ⟨v, hvQ⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [q, compressedCorridorVertexMap, retainedVertexEquiv, Q] using hv
  have hPfull : P.Nonempty := hP₀.mono Finset.subset_union_left
  have hm : I.witnessEdges.card < 2 ^ (4 * I.R) := by
    have := I.witness_edges_budget
    omega
  have hinc : (protectedIncidentEdges Γ P).card ≤ A :=
    protected_incident_budget G I c hc hR5 D hne hend
  have hAbound : A ≤ 2 ^ (5 * I.R) := deletionBudget_le _ _ hR hm
  have hscale : 10 * I.R * A ≤ 2 ^ (8 * I.R) := scaled_deletionBudget_le _ _ hR hm
  have hbudget : 10 * I.R * (protectedIncidentEdges Γ P).card ≤ I.r :=
    (Nat.mul_le_mul_left _ hinc).trans (hscale.trans I.rank_large)
  have hcut : (cutEdges Γ P).card ≤ A := by
    apply (Finset.card_le_card ?_).trans hinc
    intro e he
    simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)⟩
  have hprob := SupportForestMarginal.outside_probability_le G I c
  have hhalf : (1 / 2 : ℝ) < (componentSupportPhysical G c).outsideLinearForestProbability
      (componentLocalWitnessPullback G c I) := by
    have hpos : (0 : ℝ) < 1 / (I.R : ℝ) := by positivity
    linarith [I.outside_probability]
  have hnoLoop : ∀ e : Γ.Edge, Γ.src e ∉ P → Γ.dst e ∉ P → Γ.src e ≠ Γ.dst e := by
    intro e hs ht
    exact UnprotectedLoopExclusion.no_unprotected_loop D hne hend
      (componentLocalWitnessPullback_endpoints G c I) hhalf e
      (fun h => hs (Finset.mem_union_left _ h))
      (fun h => ht (Finset.mem_union_left _ h))
  obtain ⟨s, hs⟩ := ActiveRankExtraction.exists_cleanup_root_of_active_share
    Γ P hconn hPfull I.R I.r A 520 481 1487
    (witnessComponentCount G I.witnessVertices I.witnessEdges)
    (fun q hq => hcubic q (fun h => hq (Finset.mem_union_left _ h)))
    hshare hbudget hcut hnoLoop
    (no_parallel_outside_protected_union Γ P₀)
    (by omega) (by dsimp [A, deletionBudget]; positivity) I.rank_large hscale hAbound
    (witnessCore I c D hend) (witnessVertices I c D hend) (badVertices I c D hend)
    (protectParallelEndpoints Γ P₀)
    (by rw [show P = P₀ ∪ protectParallelEndpoints Γ P₀ from rfl,
          show P₀ = witnessVertices I c D hend ∪ badVertices I c D hend from initial_protection_eq I c D hend]
        exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
    (by rw [show P = P₀ ∪ protectParallelEndpoints Γ P₀ from rfl,
          show P₀ = witnessVertices I c D hend ∪ badVertices I c D hend from initial_protection_eq I c D hend])
    (fun _ _ h => witness_core_adj I c D hend h)
    (by simpa only [← Nat.card_eq_fintype_card] using witness_core_component_count_le I c D hend) I.witness_components
    (badVertices_card_lt I c D hend hR5)
    (parallel_protection_card_lt G I c hc hR5 D hne hend) (by omega) (by decide)
  exact ⟨c, hc, D, hne, hend, s, hconn, hs⟩

end Erdos1016.Proof.ProtectedRootConstruction

end

import Erdos1016.Cleanup.Packing.ParallelCorridorGeometry
import Erdos1016.Cleanup.Packing.UnprotectedParallelPacking
import Erdos1016.Cleanup.Packing.LocalPairedPathBound
import Erdos1016.Cleanup.Compression.RankedCubicCompression

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CorridorParallelPairCount

open Erdos1016
open PhysicalPartition CorridorPairedPathCertificates
open PhysicalDegreeTwoCoreComponents CompressedRouteDecomposition
open PartitionRouteDecomposition
open PairedPathRegions ParallelCorridorGeometry
open PairIntersectionEndpoints
open CleanupSpecification UnprotectedParallelPacking
open ParallelProtectionComplement
open GreedyConflictExtraction

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

abbrev Endpoints (D : CorridorPartition G P W) :=
  ∀ C ∈ D.corridors, corridorStart C ∈ protectedOrBranch G P ∧
    corridorFinish C ∈ protectedOrBranch G P

def protection (D : CorridorPartition G P W) (hend : Endpoints D) :
    Finset (compressedCorridorGraph D hend).Vertex := by
  classical
  exact Finset.univ.filter fun v => compressedCorridorVertexMap D hend v ∈ P

def region (D : CorridorPartition G P W) (hend : Endpoints D)
    (i : PairIndex (compressedCorridorGraph D hend) (protection D hend)) :
    Finset G.Vertex := pairedRouteRegion (corridorAt D i.1.1) (corridorAt D i.1.2)

/-- Exact route geometry, local degrees, and witness avoidance for every
unordered pair outside the protected set. All are derived from the partition. -/
theorem pair_probability_geometry
    (D : CorridorPartition G P W) (hend : Endpoints D)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hloop : ∀ e : (compressedCorridorGraph D hend).Edge,
      (compressedCorridorGraph D hend).src e ∉ protection D hend →
      (compressedCorridorGraph D hend).dst e ∉ protection D hend →
      (compressedCorridorGraph D hend).src e ≠ (compressedCorridorGraph D hend).dst e)
    (i : PairIndex (compressedCorridorGraph D hend) (protection D hend)) :
    ∃ cert : PairedPathCertificate G (region D hend i),
      (∀ v, v ∈ region D hend i → G.degree v ≤ 3) ∧
      (∀ v, v ∈ region D hend i → v ≠ cert.source.1 →
        v ≠ cert.target.1 → G.degree v = 2) ∧
      (∀ e, e ∈ SafeCore.internalEdges G (region D hend i) → e ∉ W) := by
  classical
  let Γ := compressedCorridorGraph D hend
  let C := corridorAt D i.1.1
  let E := corridorAt D i.1.2
  have hi := (pair_facts Γ (protection D hend) i).1
  have hC := corridorAt_mem D i.1.1
  have hE := corridorAt_mem D i.1.2
  have hCE : C ≠ E := by
    intro h
    exact hi.1 ((List.nodup_iff_injective_get.mp
      (Finset.nodup_toList D.corridors.toFinset)) h)
  have hne : corridorStart C ≠ corridorFinish C := by
    intro h
    apply hloop i.1.1 hi.2.1 hi.2.2.1
    apply compressedCorridorVertexMap_injective D hend
    simpa [C] using h
  have halign :
      (corridorStart C = corridorStart E ∧ corridorFinish C = corridorFinish E) ∨
      (corridorStart C = corridorFinish E ∧ corridorFinish C = corridorStart E) := by
    rcases hi.2.2.2.2.2 with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨by simpa [Γ, C, E] using congrArg (compressedCorridorVertexMap D hend) hs,
        by simpa [Γ, C, E] using congrArg (compressedCorridorVertexMap D hend) ht⟩
    · exact Or.inr ⟨by simpa [Γ, C, E] using congrArg (compressedCorridorVertexMap D hend) hs,
        by simpa [Γ, C, E] using congrArg (compressedCorridorVertexMap D hend) ht⟩
  have hCs : corridorStart C ∉ P := by
    intro hp
    exact hi.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Γ, C] using hp⟩)
  have hCt : corridorFinish C ∉ P := by
    intro hp
    exact hi.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Γ, C] using hp⟩)
  have hEs : corridorStart E ∉ P := by
    intro hp
    exact hi.2.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Γ, E] using hp⟩)
  have hEt : corridorFinish E ∉ P := by
    intro hp
    exact hi.2.2.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Γ, E] using hp⟩)
  have havoidCorridor (L : PhysicalCorridor G) (hL : L ∈ D.corridors)
      (hs : corridorStart L ∉ P) (ht : corridorFinish L ∉ P) :
      ∀ v ∈ L.vertices, v ∉ P := by
    intro v hv
    by_cases hvs : v = corridorStart L
    · simpa [hvs] using hs
    by_cases hvt : v = corridorFinish L
    · simpa [hvt] using ht
    exact (corridor_vertex_facts D L hL hv hvs hvt).1
  have havoid : ∀ v ∈ region D hend i, v ∉ P := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact havoidCorridor C hC hCs hCt v (List.mem_toFinset.mp hv)
    · exact havoidCorridor E hE hEs hEt v (List.mem_toFinset.mp hv)
  obtain ⟨cert, hsource, htarget⟩ := paired_certificate D hdegree C E hC hE hCE hne halign
  refine ⟨cert, ?_, ?_, ?_⟩
  · intro v hv
    rcases hdegree v (havoid v hv) with h2 | h3 <;> omega
  · intro v hv hs ht
    rw [hsource] at hs
    rw [htarget] at ht
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (corridor_vertex_facts D C hC (List.mem_toFinset.mp hv) hs ht).2
    · have hsE : v ≠ corridorStart E := by
        rcases halign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simpa [← h1] using hs
        · simpa [← h2] using ht
      have htE : v ≠ corridorFinish E := by
        rcases halign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simpa [← h2] using ht
        · simpa [← h1] using hs
      exact (corridor_vertex_facts D E hE (List.mem_toFinset.mp hv) hsE htE).2
  · intro e he heW
    exact havoid (G.src e) ((Finset.mem_filter.mp he).2.1) (hW e heW).1

/-- A canonical quadratic bound for all eligible pairs, before endpoint
protection. No cleanup output, global cubic bound, disjointness assumption,
or individually supplied paired-path certificate is required. -/
theorem pair_count_lt
    (D : CorridorPartition G P W)
    (hne : ∀ C ∈ D.corridors, C.edges ≠ []) (hend : Endpoints D)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.IsConnected)
    (hloop : ∀ e : (compressedCorridorGraph D hend).Edge,
      (compressedCorridorGraph D hend).src e ∉ protection D hend →
      (compressedCorridorGraph D hend).dst e ∉ protection D hend →
      (compressedCorridorGraph D hend).src e ≠ (compressedCorridorGraph D hend).dst e)
    (R : ℕ) (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) < G.outsideLinearForestProbability W) :
    (eligibleUnorderedParallelPairIndices (compressedCorridorGraph D hend)
      (protection D hend)).card < 3 * (160 * R ^ 2 + 1) := by
  classical
  let Γ := compressedCorridorGraph D hend
  let Q := protection D hend
  let U := region D hend
  have hcubic : ∀ v, v ∉ Q → ambientDegree Γ v ≤ 3 := by
    intro v hv
    have hp : compressedCorridorVertexMap D hend v ∉ P := by
      intro hp
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    exact Nat.le_of_eq (RankedCubicCompression.compressed_degree_three_off_protected
      D hne hend v hp)
  have hbridge : ∀ i j, ¬ Disjoint (U i) (U j) →
      ¬ Disjoint ({Γ.src i.1.1, Γ.dst i.1.1} : Finset Γ.Vertex)
        {Γ.src j.1.1, Γ.dst j.1.1} := by
    intro i j h
    exact canonical_parallel_pair_route_intersection_implies_endpoint_intersection D hend
      i.1.1 i.1.2 j.1.1 j.1.2 (pair_facts Γ Q i).1.2.2.2.2.2
      (pair_facts Γ Q j).1.2.2.2.2.2 h
  by_contra hnot
  obtain ⟨T, _, hdisj, hsize⟩ := exists_disjoint_subfamily Γ Q hcubic hloop U hbridge
    (160 * R ^ 2 + 1) (Nat.le_of_not_gt hnot)
  let certs := fun i => Classical.choose (pair_probability_geometry D hend hdegree hW hloop i)
  have hspec := fun i => Classical.choose_spec (pair_probability_geometry D hend hdegree hW hloop i)
  have hbound := LocalPairedPathBound.card_le_160_mul_sq G
    (ι := {i // i ∈ T}) (fun i => U i.1) (fun i => certs i.1)
    (by
      intro i j hij
      exact hdisj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)))
    (fun i => (hspec i.1).1)
    (fun i => (hspec i.1).2.1)
    W (fun i => (hspec i.1).2.2) hconn R hR hprob
  have hcard : Fintype.card {i // i ∈ T} = T.card := Fintype.card_coe T
  rw [hcard] at hbound
  omega

end Erdos1016.Proof.CorridorParallelPairCount

end

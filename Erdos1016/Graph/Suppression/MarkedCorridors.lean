import Erdos1016.Graph.Pruning.MarkedCore
import Erdos1016.Cleanup.Compression.EndpointIncidenceBijection
import Erdos1016.Cleanup.Compression.AssembledCorridorCompression

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Suppressing unmarked degree-two vertices

The canonical corridor construction supplies the actual partition. The
retained vertices are the marked vertices and the degree-three vertices;
every corridor becomes one labelled multigraph edge, including loops and
parallel edges. The declarations below use the current multigraph forest
definition, which retains both of those possibilities.
-/

noncomputable section

namespace Erdos1016.ShortProof.MarkedCorridors

open Proof.PhysicalPartition Proof.SingleCorridorRoute Proof.CoreComponentAssembly
open Proof.PhysicalDegreeTwoCoreComponents Proof.PartitionRouteDecomposition
open Proof.CompressedRouteDecomposition
open Proof.EdgeSeedConstruction
local instance markedCorridorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.IsConnected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)

private def emptyWitnessEndpoints :
    ∀ e ∈ (∅ : Finset G.Edge), G.src e ∈ P ∧ G.dst e ∈ P := by simp

def partition : CorridorPartition G P ∅ :=
  exists_corridor_partition_of_degree_two_three G P ∅ hconn hP hdegree (emptyWitnessEndpoints G P)

lemma partition_nonempty :
    ∀ C ∈ (partition G P hconn hP hdegree).corridors, C.edges ≠ [] :=
  corridor_partition_edges_nonempty_of_degree_two_three G P ∅ hconn hP hdegree
    (emptyWitnessEndpoints G P)

lemma partition_endpoints : ∀ C ∈ (partition G P hconn hP hdegree).corridors,
    corridorStart C ∈ protectedOrBranch G P ∧ corridorFinish C ∈ protectedOrBranch G P :=
  canonical_assembled_partition_endpoints_retained G P ∅ hconn hP hdegree (emptyWitnessEndpoints G P)

def graph : FiniteMultiGraph :=
  compressedCorridorGraph (partition G P hconn hP hdegree) (partition_endpoints G P hconn hP hdegree)

def vertexMap : (graph G P hconn hP hdegree).Vertex → G.Vertex :=
  compressedCorridorVertexMap (partition G P hconn hP hdegree) (partition_endpoints G P hconn hP hdegree)

lemma vertexMap_injective : Function.Injective (vertexMap G P hconn hP hdegree) :=
  compressedCorridorVertexMap_injective _ _

lemma vertexMap_retained (v : (graph G P hconn hP hdegree).Vertex) :
    vertexMap G P hconn hP hdegree v ∈ protectedOrBranch G P :=
  ((Finset.equivFin (protectedOrBranch G P)).symm v).2

def marks : Finset (graph G P hconn hP hdegree).Vertex :=
  Finset.univ.filter fun v => vertexMap G P hconn hP hdegree v ∈ P

@[simp] lemma mem_marks (v : (graph G P hconn hP hdegree).Vertex) :
    v ∈ marks G P hconn hP hdegree ↔ vertexMap G P hconn hP hdegree v ∈ P := by simp [marks]

def markedVertexEquiv : {v // v ∈ P} ≃ {v // v ∈ marks G P hconn hP hdegree} where
  toFun v := ⟨Finset.equivFin (protectedOrBranch G P)
    ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩, by
      simp [marks, vertexMap, compressedCorridorVertexMap, retainedVertexEquiv, v.2]⟩
  invFun v := ⟨vertexMap G P hconn hP hdegree v.1, (mem_marks G P hconn hP hdegree v.1).mp v.2⟩
  left_inv v := by
    apply Subtype.ext
    simp [vertexMap, compressedCorridorVertexMap, retainedVertexEquiv]
  right_inv v := by
    apply Subtype.ext
    simp [vertexMap, compressedCorridorVertexMap, retainedVertexEquiv]

theorem marks_card : (marks G P hconn hP hdegree).card = P.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (markedVertexEquiv G P hconn hP hdegree)).symm

@[simp] lemma markedVertexEquiv_vertexMap (v : {v // v ∈ P}) :
    vertexMap G P hconn hP hdegree (markedVertexEquiv G P hconn hP hdegree v).1 = v.1 := by
  simp [markedVertexEquiv, vertexMap, compressedCorridorVertexMap, retainedVertexEquiv]

lemma singleton_mem_partition (e : G.Edge) (hs : G.src e ∈ P) (ht : G.dst e ∈ P) :
    singletonCorridor G e ∈ (partition G P hconn hP hdegree).corridors := by
  let S := (canonicalCoreCorridorChoices G P hconn hP hdegree).toSystem G P
  change singletonCorridor G e ∈ S.corridors ++
    (protectedProtectedEdges G P).toList.map (singletonCorridor G)
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨e, Finset.mem_toList.mpr ?_, rfl⟩
  exact (protectedProtectedEdges_mem G P e).mpr
    ⟨Finset.mem_union.mpr (Or.inl hs), Finset.mem_union.mpr (Or.inl ht)⟩

lemma singleton_compressed_edge (e : G.Edge) (hs : G.src e ∈ P) (ht : G.dst e ∈ P) :
    ∃ f : (graph G P hconn hP hdegree).Edge,
      vertexMap G P hconn hP hdegree ((graph G P hconn hP hdegree).src f) = G.src e ∧
      vertexMap G P hconn hP hdegree ((graph G P hconn hP hdegree).dst f) = G.dst e := by
  have hmem : singletonCorridor G e ∈ corridorFamily (partition G P hconn hP hdegree) :=
    Finset.mem_toList.mpr (List.mem_toFinset.mpr (singleton_mem_partition G P hconn hP hdegree e hs ht))
  obtain ⟨f, hf⟩ := List.mem_iff_get.mp hmem
  have hf' : corridorAt (partition G P hconn hP hdegree) f = singletonCorridor G e := hf
  refine ⟨f, ?_, ?_⟩
  · change compressedCorridorVertexMap _ _ ((compressedCorridorGraph _ _).src f) = _
    rw [compressedCorridor_src_image, hf']
    rfl
  · change compressedCorridorVertexMap _ _ ((compressedCorridorGraph _ _).dst f) = _
    rw [compressedCorridor_dst_image, hf']
    rfl

def markedGraphHom : G.toSimpleGraph.induce (↑P : Set G.Vertex) →g
    (graph G P hconn hP hdegree).toSimpleGraph.induce
      (↑(marks G P hconn hP hdegree) : Set (graph G P hconn hP hdegree).Vertex) where
  toFun := markedVertexEquiv G P hconn hP hdegree
  map_rel' := by
    intro u v huv
    have hne : u.1 ≠ v.1 := G.toSimpleGraph.ne_of_adj huv
    obtain ⟨e, _, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := huv
    · obtain ⟨f, hfs, hft⟩ := singleton_compressed_edge G P hconn hP hdegree e (hs ▸ u.2) (ht ▸ v.2)
      refine ⟨?_, f, Or.inl ⟨?_, ?_⟩⟩
      · intro h
        apply hne
        have h' := congrArg (vertexMap G P hconn hP hdegree) h
        change vertexMap G P hconn hP hdegree (markedVertexEquiv G P hconn hP hdegree u).1 =
          vertexMap G P hconn hP hdegree (markedVertexEquiv G P hconn hP hdegree v).1 at h'
        simpa only [markedVertexEquiv_vertexMap] using h'
      · apply vertexMap_injective G P hconn hP hdegree
        exact hfs.trans (hs.trans (markedVertexEquiv_vertexMap G P hconn hP hdegree u).symm)
      · apply vertexMap_injective G P hconn hP hdegree
        exact hft.trans (ht.trans (markedVertexEquiv_vertexMap G P hconn hP hdegree v).symm)
    · obtain ⟨f, hfs, hft⟩ := singleton_compressed_edge G P hconn hP hdegree e (hs ▸ v.2) (ht ▸ u.2)
      refine ⟨?_, f, Or.inr ⟨?_, ?_⟩⟩
      · intro h
        apply hne
        have h' := congrArg (vertexMap G P hconn hP hdegree) h
        change vertexMap G P hconn hP hdegree (markedVertexEquiv G P hconn hP hdegree u).1 =
          vertexMap G P hconn hP hdegree (markedVertexEquiv G P hconn hP hdegree v).1 at h'
        simpa only [markedVertexEquiv_vertexMap] using h'
      · apply vertexMap_injective G P hconn hP hdegree
        exact hfs.trans (hs.trans (markedVertexEquiv_vertexMap G P hconn hP hdegree v).symm)
      · apply vertexMap_injective G P hconn hP hdegree
        exact hft.trans (ht.trans (markedVertexEquiv_vertexMap G P hconn hP hdegree u).symm)

theorem marked_component_count_le :
    Nat.card ((graph G P hconn hP hdegree).toSimpleGraph.induce
      (↑(marks G P hconn hP hdegree) : Set (graph G P hconn hP hdegree).Vertex)).ConnectedComponent ≤
      Nat.card (G.toSimpleGraph.induce (↑P : Set G.Vertex)).ConnectedComponent := by
  let f := SimpleGraph.ConnectedComponent.map (markedGraphHom G P hconn hP hdegree)
  apply Nat.card_le_card_of_surjective f
  intro c
  refine SimpleGraph.ConnectedComponent.ind ?_ c
  intro v
  obtain ⟨u, rfl⟩ := (markedVertexEquiv G P hconn hP hdegree).surjective v
  exact ⟨(G.toSimpleGraph.induce (↑P : Set G.Vertex)).connectedComponentMk u, rfl⟩

theorem connected : (graph G P hconn hP hdegree).toSimpleGraph.Connected :=
  Proof.AssembledCorridorCompression.canonicalCompressedCorridorGraph_connected
    G P ∅ (emptyWitnessEndpoints G P) hconn hP hdegree

lemma degree_eq_ambientDegree (M : FiniteMultiGraph) (v : M.Vertex) :
    M.degree v = Proof.CleanupSpecification.ambientDegree M v := by
  unfold FiniteMultiGraph.degree FiniteMultiGraph.selectedDegree
  have hfull : (Finset.univ.filter fun _e : M.Edge => (1 : F₂) ≠ 0) = Finset.univ := by
    ext e; simp
  rw [hfull]
  rfl

theorem degree_preserved (v : (graph G P hconn hP hdegree).Vertex) :
    (graph G P hconn hP hdegree).degree v = G.degree (vertexMap G P hconn hP hdegree v) := by
  rw [degree_eq_ambientDegree]
  exact Proof.EndpointIncidenceBijection.compressedCorridor_ambientDegree_eq_physical_degree
    (partition G P hconn hP hdegree) (partition_nonempty G P hconn hP hdegree)
    (partition_endpoints G P hconn hP hdegree) v

theorem degree_le_three (hmax : ∀ v, G.degree v ≤ 3)
    (v : (graph G P hconn hP hdegree).Vertex) : (graph G P hconn hP hdegree).degree v ≤ 3 := by
  rw [degree_preserved]
  exact hmax _

theorem degree_eq_three_outside_marks (v : (graph G P hconn hP hdegree).Vertex)
    (hv : v ∉ marks G P hconn hP hdegree) : (graph G P hconn hP hdegree).degree v = 3 := by
  rw [degree_preserved]
  have hret := vertexMap_retained G P hconn hP hdegree v
  have hn : vertexMap G P hconn hP hdegree v ∉ P := by simpa only [mem_marks] using hv
  simpa only [protectedOrBranch, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, hn, false_or] using hret

/-- Expanding each auxiliary edge along its actual corridor is a linear
bijection on binary cycle spaces. -/
def cycleSpaceEquiv : (graph G P hconn hP hdegree).CycleSpace ≃ₗ[F₂] (CycleCore.asMultigraph G).CycleSpace :=
  compressedCorridor_cycleEquiv (partition G P hconn hP hdegree)
    (partition_nonempty G P hconn hP hdegree) (partition_endpoints G P hconn hP hdegree)

theorem cycleRank_preserved : (graph G P hconn hP hdegree).cycleRank = G.cycleRank :=
  ((cycleSpaceEquiv G P hconn hP hdegree).trans (CycleCore.physicalMultigraphEquiv G).symm).finrank_eq

def routes : FiniteMultiGraph.EdgeDisjointRouteSystem
    (graph G P hconn hP hdegree) (CycleCore.asMultigraph G) :=
  compressedCorridorRouteSystem (partition G P hconn hP hdegree)
    (partition_nonempty G P hconn hP hdegree) (partition_endpoints G P hconn hP hdegree)

@[simp] theorem cycleSpaceEquiv_apply (x : (graph G P hconn hP hdegree).CycleSpace) (e : G.Edge) :
    (cycleSpaceEquiv G P hconn hP hdegree x).1 e =
      FiniteMultiGraph.expand _ _ (routes G P hconn hP hdegree) x.1 e := rfl

theorem cycleSpaceEquiv_apply_of_mem
    (x : (graph G P hconn hP hdegree).CycleSpace)
    (e : (graph G P hconn hP hdegree).Edge) (p : G.Edge)
    (hp : p ∈ (routes G P hconn hP hdegree).support e) :
    (cycleSpaceEquiv G P hconn hP hdegree x).1 p = x.1 e := by
  rw [cycleSpaceEquiv_apply]
  exact FiniteMultiGraph.expand_apply_of_mem_support _ _ (routes G P hconn hP hdegree) x.1 e p hp

end Erdos1016.ShortProof.MarkedCorridors

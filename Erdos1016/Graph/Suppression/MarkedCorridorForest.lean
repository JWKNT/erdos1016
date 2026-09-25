import Erdos1016.Graph.Suppression.MarkedCorridors
import Erdos1016.Graph.Multigraph.ForestCharacterization

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Forest probability transport through the actual marked corridor suppression. -/

noncomputable section

namespace Erdos1016.ShortProof.MarkedCorridors

open Proof.PhysicalPartition Proof.SingleCorridorRoute Proof.CoreComponentAssembly
open Proof.PartitionRouteDecomposition Proof.CompressedRouteDecomposition
local instance markedCorridorForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.IsConnected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)

lemma routes_cover (p : G.Edge) :
    ∃ e, p ∈ (routes G P hconn hP hdegree).support e :=
  (compressedCorridorDecomposition (partition G P hconn hP hdegree)
    (partition_nonempty G P hconn hP hdegree)
    (partition_endpoints G P hconn hP hdegree)).physical_edge_coverage p

/-- A corridor whose retained endpoints are unmarked has no marked vertex
on any of its physical edges. -/
theorem route_avoids_marks (e : (graph G P hconn hP hdegree).Edge)
    (hs : (graph G P hconn hP hdegree).src e ∉ marks G P hconn hP hdegree)
    (ht : (graph G P hconn hP hdegree).dst e ∉ marks G P hconn hP hdegree)
    (p : G.Edge) (hp : p ∈ (routes G P hconn hP hdegree).support e) :
    G.src p ∉ P ∧ G.dst p ∉ P := by
  let D := partition G P hconn hP hdegree
  let C := corridorAt D e
  have hC : C ∈ D.corridors := corridorAt_mem D e
  have hne : C.edges ≠ [] := partition_nonempty G P hconn hP hdegree C hC
  have hstart : corridorStart C ∉ P := by
    have hs' : vertexMap G P hconn hP hdegree ((graph G P hconn hP hdegree).src e) ∉ P :=
      (not_congr (mem_marks G P hconn hP hdegree _)).mp hs
    simpa only [vertexMap, graph, compressedCorridor_src_image] using hs'
  have hfinish : corridorFinish C ∉ P := by
    have ht' : vertexMap G P hconn hP hdegree ((graph G P hconn hP hdegree).dst e) ∉ P :=
      (not_congr (mem_marks G P hconn hP hdegree _)).mp ht
    simpa only [vertexMap, graph, compressedCorridor_dst_image] using ht'
  have hnone (v : G.Vertex) (hv : v ∈ P) (hinc : G.incident p v) : False := by
    have hterminal := Proof.EndpointIncidenceBijection.incident_owned_corridor_edge_is_terminal
      D P (fun _ h => Or.inl h) hC hne hp hv hinc
    rcases hterminal with h | h
    · exact hstart (h.2.symm ▸ hv)
    · exact hfinish (h.2.symm ▸ hv)
  exact ⟨fun h => hnone _ h (Or.inl rfl), fun h => hnone _ h (Or.inr rfl)⟩

def regionWord (x : (graph G P hconn hP hdegree).CycleSpace) :
    (graph G P hconn hP hdegree).EdgeWord :=
  (graph G P hconn hP hdegree).restrictEdges
    ((graph G P hconn hP hdegree).internalEdges (marks G P hconn hP hdegree)ᶜ) x.1

lemma regionWord_nonzero_iff (x : (graph G P hconn hP hdegree).CycleSpace)
    (e : (graph G P hconn hP hdegree).Edge) :
    regionWord G P hconn hP hdegree x e ≠ 0 ↔ x.1 e ≠ 0 ∧
      (graph G P hconn hP hdegree).src e ∉ marks G P hconn hP hdegree ∧
      (graph G P hconn hP hdegree).dst e ∉ marks G P hconn hP hdegree := by
  unfold regionWord FiniteMultiGraph.restrictEdges FiniteMultiGraph.internalEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  split_ifs with h
  · exact ⟨fun hx => ⟨hx, h⟩, fun hx => hx.1⟩
  · simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun _ hs ht => h ⟨hs, ht⟩

lemma expanded_seed_supported_outside
    (x seed : (graph G P hconn hP hdegree).CycleSpace)
    (hsub : ∀ e, seed.1 e ≠ 0 → regionWord G P hconn hP hdegree x e ≠ 0) :
    ∀ p, (cycleSpaceEquiv G P hconn hP hdegree seed).1 p ≠ 0 →
      CycleCore.regionWord G P (cycleSpaceEquiv G P hconn hP hdegree x) p ≠ 0 := by
  intro p hp
  obtain ⟨e, he⟩ := routes_cover G P hconn hP hdegree p
  rw [cycleSpaceEquiv_apply_of_mem G P hconn hP hdegree seed e p he] at hp
  have hx := (regionWord_nonzero_iff G P hconn hP hdegree x e).mp (hsub e hp)
  have hend := route_avoids_marks G P hconn hP hdegree e hx.2.1 hx.2.2 p he
  apply (CycleCore.regionWord_nonzero_iff G P _ p).mpr
  refine ⟨?_, hend⟩
  rw [cycleSpaceEquiv_apply_of_mem G P hconn hP hdegree x e p he]
  exact hx.1

theorem outside_forest_survives (x : (graph G P hconn hP hdegree).CycleSpace)
    (hx : (CycleCore.asMultigraph G).IsForestWord
      (CycleCore.regionWord G P (cycleSpaceEquiv G P hconn hP hdegree x))) :
    (graph G P hconn hP hdegree).IsForestWord (regionWord G P hconn hP hdegree x) := by
  apply ((graph G P hconn hP hdegree).isForestWord_iff_no_even_support _).mpr
  intro seed hsub
  have hseed : (cycleSpaceEquiv G P hconn hP hdegree seed).1 = 0 :=
    ((CycleCore.asMultigraph G).isForestWord_iff_no_even_support _).mp hx
      (cycleSpaceEquiv G P hconn hP hdegree seed)
      (expanded_seed_supported_outside G P hconn hP hdegree x seed hsub)
  have hs : cycleSpaceEquiv G P hconn hP hdegree seed = 0 := Subtype.ext hseed
  have hz : seed = 0 := (cycleSpaceEquiv G P hconn hP hdegree).injective (by simpa using hs)
  exact congrArg Subtype.val hz

lemma regionForestProbability_eq_density :
    (graph G P hconn hP hdegree).regionForestProbability (marks G P hconn hP hdegree)ᶜ =
      Finite.density (fun x : (graph G P hconn hP hdegree).CycleSpace =>
        (graph G P hconn hP hdegree).IsForestWord (regionWord G P hconn hP hdegree x)) := by
  unfold FiniteMultiGraph.regionForestProbability Finite.density Finite.count regionWord
  have hc : (Fintype.card (graph G P hconn hP hdegree).CycleSpace : ℝ) =
      (2 : ℝ) ^ (graph G P hconn hP hdegree).cycleRank := by
    exact_mod_cast (graph G P hconn hP hdegree).cycleSpace_card
  rw [hc]
  simp only [Finset.sum_boole]

/-- Suppression preserves the full binary cycle-space measure and transports
the actual outside forest event in the direction needed for an upper bound. -/
theorem regionForestProbability_le_suppressed :
    (CycleCore.asMultigraph G).regionForestProbability Pᶜ ≤
      (graph G P hconn hP hdegree).regionForestProbability (marks G P hconn hP hdegree)ᶜ := by
  rw [CycleCore.regionForestProbability_eq_density, regionForestProbability_eq_density]
  have heq := Finite.density_equiv (cycleSpaceEquiv G P hconn hP hdegree).toEquiv
    (P := fun x => (CycleCore.asMultigraph G).IsForestWord
      (CycleCore.regionWord G P (cycleSpaceEquiv G P hconn hP hdegree x)))
    (Q := fun y => (CycleCore.asMultigraph G).IsForestWord (CycleCore.regionWord G P y))
    (fun _ => Iff.rfl)
  rw [← heq]
  unfold Finite.density
  exact div_le_div_of_nonneg_right
    (Finite.count_mono (outside_forest_survives G P hconn hP hdegree)) (Nat.cast_nonneg _)

end Erdos1016.ShortProof.MarkedCorridors

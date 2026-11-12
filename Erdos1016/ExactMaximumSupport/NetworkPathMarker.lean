import Erdos1016.ExactMaximumSupport.GeodesicPathMarker
import Erdos1016.ExactMaximumSupport.NetworkPoleLayers
import Erdos1016.ExactMaximumSupport.PoleCyclePacking
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Shortest-path markers in the original network

The physical marker theorem gives one path vertex per distance layer.
A nonordinary thin layer therefore has a parallel-edge vertex outside the path.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkPathMarker
open BoundaryTrace BoundaryTrace.Network

local instance networkPathMarkerDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Two vertices on the prescribed shortest path cannot share a distance layer. -/
theorem eq_of_same_layer (hconn : N.graph.Connected) {s t : V} {A : N.Word}
    (hA : N.IsPathWord s t A) (hshort : size A = N.graph.dist s t)
    (u v : V) (hu : 0 < N.deg A u) (hv : 0 < N.deg A v)
    (hdist : N.graph.dist s u = N.graph.dist s v) : u = v := by
  let G := NetworkMultigraph.graph N
  let e := NetworkMultigraph.vertices N
  let a := NetworkMultigraph.wordEquiv N A
  have hA' : G.looplessNetwork.IsPathWord (e s) (e t) (G.nonloopWord a) :=
    NetworkMultigraph.isPathWord_push (NetworkMultigraph.relabel N) hA
  have hshort' : size a = G.toSimpleGraph.dist (e s) (e t) := by
    change G.wordLength a = G.toSimpleGraph.dist (e s) (e t)
    rw [PoleCyclePacking.length_wordEquiv, NetworkPoleLayers.distance_eq N hconn]
    exact hshort
  have hmark := GeodesicPathMarker.marked_layer_card_le_one G
    (NetworkMultigraph.isLoopless N) (NetworkMultigraph.connected N hconn) hA' hshort'
    (N.graph.dist s u : ℤ)
  apply e.injective
  apply Finset.card_le_one.mp hmark (e u) _ (e v) _
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · rw [GeodesicPathMarker.mem_support]
      exact (NetworkMultigraph.selectedDegree_wordEquiv N A u).symm ▸ hu
    · change (G.toSimpleGraph.dist (e s) (e u) : ℤ) = (N.graph.dist s u : ℤ)
      rw [NetworkPoleLayers.distance_eq N hconn]
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · rw [GeodesicPathMarker.mem_support]
      exact (NetworkMultigraph.selectedDegree_wordEquiv N A v).symm ▸ hv
    · change (G.toSimpleGraph.dist (e s) (e v) : ℤ) = (N.graph.dist s u : ℤ)
      rw [NetworkPoleLayers.distance_eq N hconn, hdist]

/-- A nonordinary thin layer has an actual parallel-edge vertex outside the prescribed path. -/
theorem parallel_witness_of_not_ordinary
    (hconn : N.graph.Connected) {s t : V} {A : N.Word}
    (hA : N.IsPathWord s t A) (hshort : size A = N.graph.dist s t)
    (j : ℕ) (hthin : N.IsThinLayer s t j) (hno : ¬ N.IsOrdinaryLayer s t j) :
    ∃ v : V, N.graph.dist s v = j ∧ N.deg A v = 0 ∧ N.OnParallel v := by
  by_contra hnone
  apply hno
  refine ⟨hthin,?_⟩
  intro x y hx hy hpx hpy
  have hxA : 0 < N.deg A x := by
    by_contra hn
    exact hnone ⟨x,hx,by omega,hpx⟩
  have hyA : 0 < N.deg A y := by
    by_contra hn
    exact hnone ⟨y,hy,by omega,hpy⟩
  exact eq_of_same_layer N hconn hA hshort x y hxA hyA (hx.trans hy.symm)

end Erdos1016.ExactMaximumSupport.NetworkPathMarker

import Erdos1016.ExactMaximumSupport.PolePathRank
import Erdos1016.ExactMaximumSupport.NetworkPoleLayers
import Erdos1016.ExactMaximum.ThirdPair

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual shortest path words in a finite network

A graph walk gives a parity join with no more selected physical labels than
walk steps. Extracting a path subword and comparing with ordinary distance
produces an actual shortest path word. Parallel labels remain distinct.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkGeodesic
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph

local instance networkGeodesicDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- Adding one physical label increases support size by at most one. -/
theorem size_unit_add_le (e : E) (x : N.Word) : size (unitWord e + x) ≤ size x + 1 := by
  calc
    _ ≤ (insert e (Finset.univ.filter fun f : E => x f ≠ 0)).card := by
      apply Finset.card_le_card
      intro f hf
      by_cases h : e = f
      · subst f
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ f, ?_⟩
        have hh := (Finset.mem_filter.mp hf).2
        simpa [unitWord_apply,h] using hh
    _ ≤ _ := Finset.card_insert_le _ _

/-- Every actual graph walk supplies a join of no greater physical support size. -/
theorem exists_join_le_walk {s t : V} (p : N.graph.Walk s t) :
    ∃ y : N.Word, N.boundary y = N.pathDemand s t ∧ size y ≤ p.length := by
  induction p with
  | nil =>
    refine ⟨0, ?_, ?_⟩
    · change N.boundary 0 = unitWord _ + unitWord _
      rw [map_zero,word_add_self]
    · simp [Network.size]
  | @cons u v w huv p ih =>
    obtain ⟨y,hy,hsize⟩ := ih
    obtain ⟨e,he⟩ := huv
    have hedge : N.boundary (unitWord e) = unitWord u + unitWord v := by
      rcases he with he | he
      · simp only [boundary_unit,he.1,he.2]
      · simp only [boundary_unit,he.1,he.2,add_comm]
    refine ⟨unitWord e+y, ?_, ?_⟩
    · change N.boundary (unitWord e+y) = unitWord u+unitWord w
      change N.boundary y = unitWord v+unitWord w at hy
      rw [map_add,hedge,hy]
      calc
        _ = unitWord u+unitWord w+(unitWord v+unitWord v) := by abel
        _ = _ := by rw [word_add_self,add_zero]
    · have hh := size_unit_add_le N e y
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Every actual physical path has at least the ordinary endpoint distance. -/
theorem physical_dist_le_size (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    {s t : G.Vertex} {A : G.EdgeWord}
    (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A)) :
    G.toSimpleGraph.dist s t ≤ Network.size A := by
  have hs : s ∈ GeodesicPathMarker.support G A := by
    apply (GeodesicPathMarker.mem_support G A s).mpr
    rw [G.selectedDegree_eq_deg A (hloop.word A),hA.2.1]
    decide
  have hr : (G.selectedGraph A).Reachable s t := by
    rw [G.selectedGraph_eq]
    apply hA.2.2.2.2 t
    rw [hA.2.2.1]
    decide
  obtain ⟨p,hp⟩ := hr.exists_isPath
  have hcard := Finset.card_le_card (GeodesicPathMarker.walk_support_subset G p hs)
  rw [List.toFinset_card_of_nodup hp.support_nodup,p.length_support,
    GeodesicPathMarker.path_support_card G hloop hA] at hcard
  let f : G.selectedGraph A →g G.toSimpleGraph := {
    toFun := id
    map_rel' := fun h => ⟨h.1, by obtain ⟨e,he,hh⟩ := h.2; exact ⟨e,hh⟩⟩ }
  have hd := G.toSimpleGraph.dist_le (p.map f)
  simp only [SimpleGraph.Walk.length_map] at hd
  change G.toSimpleGraph.dist s t ≤ p.length at hd
  omega

/-- Distance is bounded by the size of an actual network path word. -/
theorem dist_le_size (hN : N.graph.Connected) {s t : V} {A : N.Word}
    (hA : N.IsPathWord s t A) : N.graph.dist s t ≤ size A := by
  have hp := NetworkMultigraph.isPathWord_push (NetworkMultigraph.relabel N) hA
  rw [← NetworkMultigraph.nonloop_wordEquiv] at hp
  have hh := physical_dist_le_size (NetworkMultigraph.graph N) (NetworkMultigraph.isLoopless N) hp
  change (NetworkMultigraph.graph N).toSimpleGraph.dist
    (NetworkMultigraph.vertices N s) (NetworkMultigraph.vertices N t) ≤
      size (NetworkMultigraph.wordEquiv N A) at hh
  simpa only [NetworkPoleLayers.distance_eq N hN,PolePathRank.size_wordEquiv] using hh

/-- Connected distinct endpoints admit an actual shortest path word. -/
theorem exists_shortest_path (hN : N.graph.Connected) (s t : V) (hne : s ≠ t) :
    ∃ A : N.Word, N.IsPathWord s t A ∧ size A = N.graph.dist s t := by
  obtain ⟨p,hp⟩ := hN.exists_walk_length_eq_dist s t
  obtain ⟨y,hy,hlen⟩ := exists_join_le_walk N p
  obtain ⟨A,hA,hsub⟩ := N.exists_isPathWord_subword hne y hy
  have hsize : size A ≤ size y := by
    apply Finset.card_le_card
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,hsub e (Finset.mem_filter.mp he).2⟩
  have hd := dist_le_size N hN hA
  exact ⟨A,hA,by omega⟩

end Erdos1016.ExactMaximumSupport.NetworkGeodesic

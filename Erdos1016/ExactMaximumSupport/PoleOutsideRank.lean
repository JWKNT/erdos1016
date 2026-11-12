import Erdos1016.ExactMaximumSupport.OutsideRankFromPacking
import Erdos1016.ExactMaximumSupport.SmallCyclicInterval
import Erdos1016.ExactMaximumSupport.GeodesicPathMarker
import Erdos1016.ExactMaximumSupport.NetworkPoleLayers
import Erdos1016.ExactMaximumSupport.NetworkExteriorRank

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Bounded cycle rank outside a shortest path in a path-rich pole

The actual shortest path supplies the marker geometry.
Small cyclic intervals form a disjoint family with a forest remainder.
Path density bounds the family size, and actual vertex deletion bounds the rank.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleOutsideRank
open FiniteMultiGraph BoundaryTrace BoundaryTrace.Network BoundaryDecay
open LargeGirth ThinIntervalBoundary
local instance outsideRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The complete outside-rank bound for actual physical multigraphs. -/
theorem exists_physical_bound :
    ∃ C : ℕ,∀ (G : FiniteMultiGraph) (s t : G.Vertex) (A : G.EdgeWord),
      G.IsLoopless → G.toSimpleGraph.Connected → G.degree s≤2 → G.degree t≤2 →
      (∀ v,v≠s → v≠t → G.degree v=3) →
      G.looplessNetwork.IsPathWord s t (G.nonloopWord A) →
      Network.size A=G.toSimpleGraph.dist s t →
      501*2^G.cycleRank≤1000*G.looplessNetwork.numPaths s t →
      (PieceCore.Induced.graph G (GeodesicPathMarker.support G A)ᶜ).cycleRank≤C := by
  obtain ⟨B,hB⟩ := PathForestProbability.exists_path_layer_bound_501
  let θ := 9*B
  let L := 22*(θ+1)
  refine ⟨2*L*(1000*(L+1)*2^L),?_⟩
  intro G s t A hloop hG hs ht hcubic hA hshort hpaths
  let P := GeodesicPathMarker.support G A
  let level : G.Vertex → ℤ := fun v => G.toSimpleGraph.dist s v
  have hdeg : ∀ v,G.degree v≤3 := by
    intro v
    by_cases hvs : v=s
    · subst v
      omega
    by_cases hvt : v=t
    · subst v
      omega
    exact (hcubic v hvs hvt).le
  have hsP : s∈P := by
    change s∈GeodesicPathMarker.support G A
    rw [GeodesicPathMarker.mem_support,G.selectedDegree_eq_deg A (hloop.word A),hA.2.1]
    decide
  have htP : t∈P := by
    change t∈GeodesicPathMarker.support G A
    rw [GeodesicPathMarker.mem_support,G.selectedDegree_eq_deg A (hloop.word A),hA.2.2.1]
    decide
  have hcubicP : ∀ v,v∉P → G.degree v=3 := by
    intro v hv
    exact hcubic v (by rintro rfl; exact hv hsP) (by rintro rfl; exact hv htP)
  have hports : ∀ v,v∉({s,t}:Finset G.Vertex) → G.degree v=3 := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
    exact hcubic v hv.1 hv.2
  have hfull (j : ℤ) : (Finset.univ.filter fun v => level v=j).card≤θ := by
    have hh := hB G {s,t} s t hloop hG hdeg hports (by simp) (by simp) hA.1 hpaths j
    simpa only [Finset.card_pair hA.1,Nat.reduceAdd,Nat.reducePow,Nat.mul_comm B 9] using hh
  have hwidth (j : ℤ) : (layer G P level j).card≤θ := by
    apply (Finset.card_le_card (show layer G P level j ⊆ Finset.univ.filter (fun v => level v=j) from ?_)).trans (hfull j)
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mem_layer G P level j v).mp hv).2⟩
  have hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1 :=
    Probability.GeodesicMarker.level_edge G hG s
  have hfurther : ∀ v∈P,G.selectedDegree (outsideWord G P) v≤1 :=
    GeodesicPathMarker.outside_incidence_le_one G hloop hA hs ht (fun v hv hw => (hcubic v hv hw).le)
  have hmark : ∀ j,(Probability.LevelWindowBoundary.markedLayer G P level j).card≤1 :=
    GeodesicPathMarker.marked_layer_card_le_one G hloop hG hA hshort
  have hlocal : ∀ a b : ℤ,G.HasCycleIn (region G P level a b) →
      ∃ c d : ℤ,region G P level c d ⊆ region G P level a b ∧
        (region G P level c d).card≤L ∧ G.HasCycleIn (region G P level c d) := by
    intro a b hcyclic
    obtain ⟨c,d,_,_,_,hsub,hcy,hcard⟩ := SmallCyclicInterval.exists_small_interval G P level θ
      hloop hdeg hcubicP hfurther hlevel hwidth hmark hcyclic
    exact ⟨c,d,hsub,hcard,hcy⟩
  have hb : G.boundary A=G.looplessNetwork.pathDemand s t := by
    rw [← G.nonloopWord_boundary]
    exact hA.boundary_eq
  have hzero : ∀ e∈G.internalEdges Pᶜ,A e=0 := by
    intro e he
    by_contra hn
    have hs' : G.src e∉P := Finset.mem_compl.mp (Finset.mem_filter.mp he).2.1
    exact hs' ((GeodesicPathMarker.mem_support G A _).mpr (G.selectedDegree_src_pos hn))
  have hprob := PathExteriorProbability.restrictedForestProbability_ge_501 G hloop hG s t
    hA.1 hpaths A hb (G.internalEdges Pᶜ) hzero
  exact OutsideRankFromPacking.rank_le_of_local_intervals G P level L hloop hG hdeg
    hlevel hlocal hprob

/-- Proposition 5.3, Steps 1--3, with the exact original-network conclusion. -/
theorem poleOutsideRankStatement : ExactMaximum.PoleOutsideRankStatement := by
  obtain ⟨C,hC⟩ := exists_physical_bound
  refine ⟨C,?_⟩
  intro V E _ _ N s t A hN hs ht hcubic hA hshort hpaths
  let G := NetworkMultigraph.graph N
  let e := NetworkMultigraph.vertices N
  let a := NetworkMultigraph.wordEquiv N A
  have hA' : G.looplessNetwork.IsPathWord (e s) (e t) (G.nonloopWord a) :=
    NetworkMultigraph.isPathWord_push (NetworkMultigraph.relabel N) hA
  have hcubic' : ∀ v,v≠e s → v≠e t → G.degree v=3 := by
    intro v hvs hvt
    obtain ⟨w,rfl⟩ := e.surjective v
    simpa only [G,e,NetworkMultigraph.degree] using hcubic w
      (fun h => hvs (congrArg e h)) (fun h => hvt (congrArg e h))
  have hshort' : Network.size a=G.toSimpleGraph.dist (e s) (e t) := by
    change G.wordLength a=G.toSimpleGraph.dist (e s) (e t)
    rw [PoleCyclePacking.length_wordEquiv,NetworkPoleLayers.distance_eq N hN]
    exact hshort
  have hpaths' : 501*2^G.cycleRank≤1000*G.looplessNetwork.numPaths (e s) (e t) := by
    simpa only [G,e,NetworkMultigraph.cycleRank,NetworkMultigraph.numPaths] using hpaths
  have hh := hC G (e s) (e t) a (NetworkMultigraph.isLoopless N) (NetworkMultigraph.connected N hN)
    (by simpa only [G,e,NetworkMultigraph.degree] using hs)
    (by simpa only [G,e,NetworkMultigraph.degree] using ht) hcubic' hA' hshort' hpaths'
  rw [NetworkExteriorRank.outside_rank_eq N A]
  exact hh

end Erdos1016.ExactMaximumSupport.PoleOutsideRank

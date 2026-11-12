import Erdos1016.ExactMaximumSupport.PoleMarginProbability

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Exterior rank at any positive path-density margin

The established interval packing argument works at each positive margin.
All ranks and paths refer to the original physical network.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank
open FiniteMultiGraph BoundaryTrace BoundaryTrace.Network BoundaryDecay
open LargeGirth ThinIntervalBoundary
local instance marginOutsideDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A uniform cycle packing bound controls the entire path exterior. -/
theorem exists_exterior_rank_bound (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ∃ C : ℕ, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (level : G.Vertex → ℤ) (_hloop : G.IsLoopless)
    (_hG : G.toSimpleGraph.Connected) (_hdegree : ∀ v, G.degree v ≤ 3)
    (_hlevel : ∀ e, level (G.src e) ≤ level (G.dst e) + 1 ∧
      level (G.dst e) ≤ level (G.src e) + 1)
    (_hlocal : ∀ a b : ℤ, G.HasCycleIn (region G P level a b) →
      ∃ c d : ℤ, region G P level c d ⊆ region G P level a b ∧
        (region G P level c d).card ≤ L ∧ G.HasCycleIn (region G P level c d))
    (_hforest : (1/2 : ℝ) + ε ≤ Finite.density (fun z : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges Pᶜ) z.1))),
    (LargeGirth.PieceCore.Induced.graph G Pᶜ).cycleRank ≤
      C := by
  classical
  obtain ⟨K,hK⟩ := PoleMarginProbability.exists_packing_bound ε hε L
  refine ⟨2 * L * K,?_⟩
  intro G P level hloop hG hdegree hlevel hlocal hforest
  obtain ⟨F, hF, hdisj, hout, hrem⟩ :=
    IntervalCyclePacking.exists_packing_with_forest_remainder G P level L hloop hlevel hlocal
  let I := {R : Finset G.Vertex // R ∈ F}
  have hcycles (i : I) : ∃ z : G.EdgeWord, G.IsCycleWord z ∧ G.SupportedIn z i.1 :=
    (hF i.1 i.2).2.2
  choose Z hZ hsupport using hcycles
  have hsub (i : I) : CycleRegions.region G (Z i) ⊆ i.1 :=
    MinimalCyclicInterval.cycle_region_subset_of_supported G (Z i) i.1 (hsupport i)
  have hcycle_disj : Pairwise fun i j : I =>
      Disjoint (CycleRegions.region G (Z i)) (CycleRegions.region G (Z j)) := by
    intro i j hij
    apply (hdisj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))).mono (hsub i) (hsub j)
  have hcycle_out (i : I) : Disjoint (CycleRegions.region G (Z i)) P := by
    apply Finset.disjoint_left.mpr
    intro v hv hp
    have hvi : v ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨i.1, i.2, hsub i hv⟩
    exact Finset.mem_compl.mp (hout hvi) hp
  have hlength (i : I) : G.wordLength (Z i) ≤ L := by
    rw [← CycleRegions.cycle_region_card G (Z i) (hZ i)]
    exact (Finset.card_le_card (hsub i)).trans (hF i.1 i.2).2.1
  have hcard := hK G hG hdegree I Z hZ hcycle_disj P hcycle_out hlength hforest
  have hFcard : F.card ≤ K := by
    simpa only [I, Fintype.card_coe] using hcard
  exact (IntervalCyclePacking.exterior_rank_le G P level L F hloop hdegree hF hrem).trans
    (Nat.mul_le_mul_left (2 * L) hFcard)

/-- Positive path density bounds the physical exterior rank. -/
theorem exists_physical_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ,∀ (G : FiniteMultiGraph) (s t : G.Vertex) (A : G.EdgeWord),
      G.IsLoopless → G.toSimpleGraph.Connected → G.degree s≤2 → G.degree t≤2 →
      (∀ v,v≠s → v≠t → G.degree v=3) →
      G.looplessNetwork.IsPathWord s t (G.nonloopWord A) →
      Network.size A=G.toSimpleGraph.dist s t →
      (1/2 + ε) * (2:ℝ)^G.cycleRank ≤ G.looplessNetwork.numPaths s t →
      (PieceCore.Induced.graph G (GeodesicPathMarker.support G A)ᶜ).cycleRank≤C := by
  obtain ⟨B,hB⟩ := PoleMarginProbability.exists_path_layer_bound ε hε
  let θ := 9*B
  let L := 22*(θ+1)
  obtain ⟨C,hC⟩ := exists_exterior_rank_bound ε hε L
  refine ⟨C,?_⟩
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
  have hprob := PoleMarginProbability.restricted_forest_probability ε G hloop hG s t
    hA.1 hpaths A hb (G.internalEdges Pᶜ) hzero
  exact hC G P level hloop hG hdeg
    hlevel hlocal hprob


/-- The original network keeps all physical edge labels and the exact exterior. -/
theorem exists_network_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E)
      (s t : V) (A : N.Word), N.graph.Connected →
      N.deg (fun _ => 1) s ≤ 2 → N.deg (fun _ => 1) t ≤ 2 →
      (∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3) →
      N.IsPathWord s t A → size A = N.graph.dist s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t →
      networkRank (N.sub (fun e => N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0)) ≤ C := by
  obtain ⟨C,hC⟩ := exists_physical_bound ε hε
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
  have hpaths' : (1/2 + ε) * (2:ℝ)^G.cycleRank ≤ G.looplessNetwork.numPaths (e s) (e t) := by
    simpa only [G,e,NetworkMultigraph.cycleRank,NetworkMultigraph.numPaths] using hpaths
  have hh := hC G (e s) (e t) a (NetworkMultigraph.isLoopless N) (NetworkMultigraph.connected N hN)
    (by simpa only [G,e,NetworkMultigraph.degree] using hs)
    (by simpa only [G,e,NetworkMultigraph.degree] using ht) hcubic' hA' hshort' hpaths'
  rw [NetworkExteriorRank.outside_rank_eq N A]
  exact hh


end Erdos1016.ExactMaximumSupport.PoleMarginOutsideRank

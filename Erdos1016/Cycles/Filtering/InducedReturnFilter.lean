import Erdos1016.Cycles.Filtering.ReturnMassLoss

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Proof.InducedRetainedCycleFilter

open scoped BigOperators
open BoundaryDecay Nonbacktracking SafeCore
open ExternalReturnFilter RejectedReturnWitness
open WeightedThetaCharging ReturnMassLoss
open PhysicalThetaCandidates RejectedCycleEncoding
open ThetaMassFiberBridge

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The full manuscript filter includes length-one external returns: chords.
The old return predicate handles the remaining paths, of length at least two. -/
def inducedAcceptedCycles (G : PhysicalGraph) (V : Finset G.Vertex)
    (bases : Finset G.CycleWord) (q : ℕ) : Finset G.CycleWord :=
  (acceptedShortReturnCycles G V bases q).filter Cycle.IsInduced

theorem mem_inducedAcceptedCycles (G : PhysicalGraph) (V : Finset G.Vertex)
    (bases : Finset G.CycleWord) (q : ℕ) (C : G.CycleWord) :
    C ∈ inducedAcceptedCycles G V bases q ↔ C ∈ bases ∧
      NoShortExternalReturnWithin G V (Cycle.vertices C) q ∧ Cycle.IsInduced C := by
  simp [inducedAcceptedCycles, mem_acceptedShortReturnCycles, and_assoc]

/-- A chord is an external simple return of length one on the representative
cycle walk. Its edge is absent from the selected cycle's edge set. -/
theorem noninduced_cycle_has_chord_return (G : PhysicalGraph) (C : G.CycleWord)
    (hC : ¬ Cycle.IsInduced C) :
    ∃ a : G.Vertex, ∃ (c : G.toSimpleGraph.Walk a a) (hc : c.IsCycle),
      ∃ (hword : cycleWordOfWalk G c hc = C), ∃ u v : G.Vertex,
      ∃ (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v),
      ∃ (route : G.toSimpleGraph.Walk u v),
      route.IsPath ∧ route.length = 1 ∧
      (∀ z, z ∈ route.support → z ≠ u → z ≠ v → z ∉ c.support) ∧
      (∀ e, e ∈ route.edges → e ∉ c.edges) := by
  classical
  have hnsub : ¬ internalEdges G (Cycle.vertices C) ⊆ Cycle.edges C := by
    intro h
    exact hC (Finset.Subset.antisymm h (Cycle.edges_subset_internal C))
  obtain ⟨e, he, henot⟩ := Finset.not_subset.mp hnsub
  have hend : G.src e ∈ Cycle.vertices C ∧ G.dst e ∈ Cycle.vertices C := by
    simpa [internalEdges] using he
  obtain ⟨a, c, hc, hword⟩ := exists_cycle_walk_of_cycleWord G C
  have hwordValue : walkWord G c = C.1 := congrArg Subtype.val hword
  have hvertices : ∀ z, z ∈ Cycle.vertices C ↔ z ∈ c.support := by
    intro z
    change z ∈ G.usedVertices C.1 ↔ _
    rw [← hwordValue]
    exact used_walkWord_iff G c hc z
  have hadj : G.toSimpleGraph.Adj (G.src e) (G.dst e) :=
    ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩
  let route : G.toSimpleGraph.Walk (G.src e) (G.dst e) := .cons hadj .nil
  have hpath : route.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil
    simpa using G.noLoops e
  have hedge : s(G.src e, G.dst e) ∉ c.edges := by
    intro hec
    apply henot
    change e ∈ G.edgeSupport C.1
    rw [← hwordValue]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (walkWord_nonzero_iff G c e).mpr hec⟩
  refine ⟨a, c, hc, hword, G.src e, G.dst e,
    (hvertices _).mp hend.1, (hvertices _).mp hend.2, G.noLoops e, route,
    hpath, rfl, ?_, ?_⟩
  · intro z hz hzu hzv
    simp only [route, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz
    exact (hz.elim hzu hzv).elim
  · intro f hf
    have hf' : f = s(G.src e, G.dst e) := by simpa [route] using hf
    simpa [hf'] using hedge

/-- Rejection by either part of the full filter gives the same external
path witness used by the theta accounting. -/
theorem rejected_induced_cycle_has_return (G : PhysicalGraph)
    (V : Finset G.Vertex) (bases : Finset G.CycleWord) (q : ℕ) (hq : 1 ≤ q)
    (C : G.CycleWord) (hbase : C ∈ bases)
    (hnot : C ∉ inducedAcceptedCycles G V bases q) :
    ∃ a : G.Vertex, ∃ (c : G.toSimpleGraph.Walk a a) (hc : c.IsCycle),
      ∃ (hword : cycleWordOfWalk G c hc = C), ∃ u v : G.Vertex,
      ∃ (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v),
      ∃ (route : G.toSimpleGraph.Walk u v),
      route.IsPath ∧ route.length ≤ q ∧
      (∀ z, z ∈ route.support → z ≠ u → z ≠ v → z ∉ c.support) ∧
      (∀ e, e ∈ route.edges → e ∉ c.edges) := by
  by_cases hold : C ∈ acceptedShortReturnCycles G V bases q
  · have hnind : ¬ Cycle.IsInduced C := fun hi =>
      hnot (Finset.mem_filter.mpr ⟨hold, hi⟩)
    obtain ⟨a, c, hc, hw, u, v, hu, hv, huv, route, hp, hl, hs, he⟩ :=
      noninduced_cycle_has_chord_return G C hnind
    exact ⟨a, c, hc, hw, u, v, hu, hv, huv, route, hp, by omega, hs, he⟩
  · exact rejected_cycle_has_short_external_return G C hbase hold

/-- Both sorts of discarded cycles share one recovery injection, so adding
chord rejection does not increase the coefficient in the mass loss. -/
theorem rejected_induced_cycle_has_weighted_code (G : PhysicalGraph)
    (D s q L : ℕ) (hgirth : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 2 * s ≤ D) (hq : 1 ≤ q) (hqL : q ≤ L)
    (V : Finset G.Vertex) (C : G.CycleWord)
    (hbase : C ∈ shortCycleWords G L)
    (hnot : C ∉ inducedAcceptedCycles G V (shortCycleWords G L) q) :
    ∃ code : RealizableCandidate G (shortCycleWords G L) s L × Fin 3,
      recoverThetaTagCycle G code = C ∧
      G.wordLength (candidateCycle G code.1.1).1 +
        candidateBranchLength G code.1.1 ≤ q + G.wordLength C.1 := by
  classical
  obtain ⟨a, c, hc, hword, u, v, hu, hv, huv, route, hr, hrlen, hinterior, hedges⟩ :=
    rejected_induced_cycle_has_return G V (shortCycleWords G L) q hq C hbase hnot
  have hclen : c.length ≤ L := by
    have hshort : G.wordLength C.1 ≤ L := (Finset.mem_filter.mp hbase).2
    calc
      c.length = G.wordLength (cycleWordOfWalk G c hc).1 := by
        symm
        simpa [PhysicalGraph.wordLength] using cycleWordOfWalk_length G c hc
      _ = G.wordLength C.1 := congrArg (fun C : G.CycleWord => G.wordLength C.1) hword
      _ ≤ L := hshort
  obtain ⟨code, hrecover, hcharge⟩ := short_external_return_yields_weighted_code
    G D s q L hgirth hs hqL c hc hclen hu hv huv route hr hrlen hinterior hedges
  exact ⟨code, hrecover.trans hword, by simpa [hword] using hcharge⟩

/-- The full induced retained filter obeys the same finite suffix budget as
the old filter. This includes the length-one returns missing from that filter. -/
theorem rejected_induced_mass_le_suffix_budget (G : PhysicalGraph)
    (D s q L : ℕ) (V : Finset G.Vertex)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hgirth : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hshortGirth : 2 * s ≤ D) (hq : 1 ≤ q) (hqL : q ≤ L) :
    (∑ C ∈ shortCycleWords G L \ inducedAcceptedCycles G V
      (shortCycleWords G L) q, cycleWordMass G C) ≤
      (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 *
        (1 / 2 : ℝ) ^ s * shortCycleMass G L := by
  classical
  have hreject : (∑ C ∈ shortCycleWords G L \ inducedAcceptedCycles G V
      (shortCycleWords G L) q, cycleWordMassWeight G C) ≤
      3 * (2 : ℝ) ^ q * (∑ w : RealizableCandidate G (shortCycleWords G L) s L,
        realizableThetaMassWeight G w) := by
    apply excluded_cycle_mass_le_three_pow_q_candidate_mass G
    intro C hC
    have hm := Finset.mem_sdiff.mp hC
    obtain ⟨code, hrec, hcharge⟩ := rejected_induced_cycle_has_weighted_code
      G D s q L hgirth hshortGirth hq hqL V C hm.1 hm.2
    exact ⟨code, hrec, by simpa [hrec] using hcharge⟩
  have hcandidate := realizable_candidate_mass_le_short_return_path_mass
    G (shortCycleWords G L) s L
  have htheta := ThetaFilterAccounting.shortReturnPathThetaMass_le
    G (shortCycleWords G L) s L D (fun C hC => (Finset.mem_filter.mp hC).2)
      hmin hmax hgirth hs hshortGirth
  calc
    _ ≤ 3 * (2 : ℝ) ^ q * (∑ w : RealizableCandidate G (shortCycleWords G L) s L,
          realizableThetaMassWeight G w) := by
      simpa only [cycleWordMass, cycleWordMassWeight] using hreject
    _ ≤ 3 * (2 : ℝ) ^ q *
        (ThetaFilterAccounting.shortReturnPathThetaMass G (shortCycleWords G L) s L) :=
      mul_le_mul_of_nonneg_left hcandidate (by positivity)
    _ ≤ 3 * (2 : ℝ) ^ q * ((3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s *
        shortCycleMass G L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [shortCycleMass, cycleWordMass] using htheta
    _ = _ := by ring

end Erdos1016.Proof.InducedRetainedCycleFilter
end

import Erdos1016.Cycles.Counting.WeightedVertexLoad
import Erdos1016.Nonbacktracking.Walks.WindowPositions

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CycleSuffixGeometry

open Nonbacktracking WalkPrefix CollisionSliceInstantiation WeightedWalkPrefix
open RootedCyclePrefixes CycleRootChoice
open FixedLengthVertexMass

variable (G : PhysicalGraph)

private theorem runDarts_mpr {m n : ℕ} (h : n = m) {d e : Dart G}
    (hh : Run G n d e = Run G m d e) (r : Run G m d e) :
    runDarts G n (Eq.mpr hh r) = runDarts G m r := by
  cases h
  rfl

theorem split_suffix_darts_subset : ∀ {j k : ℕ} (hjk : j ≤ k) {d e : Dart G}
    (r : Run G k d e),
    runDarts G (k - j) (splitRun G hjk r).2.2 ⊆ runDarts G k r := by
  intro j
  induction j with
  | zero =>
      intro k hjk d e r
      rw [splitRun.eq_1 G k d e r hjk]
      exact List.Subset.refl _
  | succ j ih =>
      intro k hjk d e r
      cases k with
      | zero => omega
      | succ k =>
          obtain ⟨f, hf, rest⟩ := r
          have h := ih (Nat.le_of_succ_le_succ hjk) rest
          rw [splitRun.eq_3 G d e j k hjk ⟨f, hf, rest⟩]
          rw [runDarts_mpr G (Nat.succ_sub_succ_eq_sub k j)]
          simp only [runDarts]
          change runDarts G (k - j) (splitRun G (Nat.le_of_succ_le_succ hjk) rest).2.2 ⊆
            d :: runDarts G k rest
          exact h.trans (by intro x hx; exact List.mem_cons_of_mem _ hx)

theorem walkDarts_endpoints_mem_support {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (d : Dart G) (hd : d ∈ walkDarts G p) :
    tail G d ∈ p.support ∧ head G d ∈ p.support := by
  induction p with
  | nil => simp [walkDarts] at hd
  | cons h p ih =>
      rcases List.mem_cons.mp hd with rfl | hd
      · simp only [tail_dartOfAdj, head_dartOfAdj, SimpleGraph.Walk.support_cons,
          List.mem_cons, true_or, true_and]
        exact Or.inr p.start_mem_support
      · have hh := ih hd
        exact ⟨List.mem_cons_of_mem _ hh.1, List.mem_cons_of_mem _ hh.2⟩

theorem runWalk_support_subset {k : ℕ} {d e : Dart G} (r : Run G k d e)
    (S : Finset G.Vertex)
    (hS : ∀ f ∈ runDarts G k r, tail G f ∈ S ∧ head G f ∈ S) :
    ∀ v ∈ (runWalk G k r).support, v ∈ S := by
  have hd : d ∈ runDarts G k r := by cases k <;> simp [runDarts]
  have hheads : (runDarts G k r).map (head G) = (runWalk G k r).support.tail := by
    rw [← walkDarts_runWalk, walkDarts_map_head]
  intro v hv
  rw [(runWalk G k r).support_eq_cons] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (hS d hd).1
  · rw [← hheads] at hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
    exact (hS f hf).2

/-- Every vertex of the actual encoded suffix still lies on its candidate
cycle. This statement does not require minimum degree in the counting graph. -/
theorem encoded_suffix_support
    (ell j : ℕ) (hj : j ≤ ell - 1) (v : G.Vertex)
    (C : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v})
    (orientation : Bool) :
    ∀ z ∈ (runWalk G ((ell - 1) - j)
      (splitRun G hj (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2).2.2).support,
      z ∈ BoundaryDecay.Cycle.vertices C.1.1 := by
  let c := chosenRootedSimpleCycle C.1
  let x := selectRootAtVertex G ell v C
  let q := rootedOrientedWalk c.1.2 x orientation
  have hq : q.IsCycle := rootedOrientedWalk_cycle c.1.2 c.2.1 x orientation
  have hword : walkWord G q = C.1.1.1 :=
    (rootedOrientedWalk_word_eq c.1.2 x orientation).trans
      (congrArg Subtype.val (chosenRootedSimpleCycle_word C.1))
  have hdarts : runDarts G (ell - 1)
      (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2 = walkDarts G q :=
    rootedCycleEndpointPrefix_darts G c x (selectRootAtVertex_spec G ell v C) orientation
  apply runWalk_support_subset
  intro d hd
  have hfull := split_suffix_darts_subset G hj
    (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2 hd
  rw [hdarts] at hfull
  have hends := walkDarts_endpoints_mem_support G q d hfull
  constructor
  · change tail G d ∈ G.usedVertices C.1.1.1
    rw [← hword]
    exact (used_walkWord_iff G q hq _).mpr hends.1
  · change head G d ∈ G.usedVertices C.1.1.1
    rw [← hword]
    exact (used_walkWord_iff G q hq _).mpr hends.2

theorem short_run_isPath (D k : ℕ) (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hlen : k + 1 ≤ D) {d e : Dart G} (r : Run G k d e) :
    (runWalk G k r).IsPath :=
  ShortWalks.reduced_isPath_of_girth D hg _ (runWalk_reduced G k r)
    (by simpa only [runWalk_length] using hlen)

end Erdos1016.Proof.CycleSuffixGeometry

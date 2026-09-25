import Erdos1016.Cycles.Counting.CycleWordRunCount
import Erdos1016.Cycles.Filtering.ThetaSupportArcs
import Erdos1016.Nonbacktracking.Trace.SimpleRunMass

set_option autoImplicit false

namespace Erdos1016.Proof.CycleSupportFibers
noncomputable section

open SimpleGraph
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclePathUniqueness
open Erdos1016.Proof.ThetaSupportArcUniqueness
open Erdos1016.Proof.ThetaArcUniqueness
open Erdos1016.Proof.SimpleRunMass
open Erdos1016.Proof.RootedCyclicRunInjection
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.CyclicRunCollisionGeometry

variable {G : PhysicalGraph}

local instance fiberEqualityDecidable (P : Prop) : Decidable P := Classical.propDecidable P

private theorem walk_mem_edges_subset {u v : G.Vertex}
    (p q : G.toSimpleGraph.Walk u v)
    (h : p.edges.toFinset = q.edges.toFinset) :
    ∀ e, e ∈ q.edges → e ∈ p.edges := by
  intro e he
  apply List.mem_toFinset.mp
  rw [h]
  exact List.mem_toFinset.mpr he

private theorem transfer_mapLe_id {V : Type*} {G H : SimpleGraph V}
    (hHG : H ≤ G) {u v : V} (p : G.Walk u v)
    (hedges : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hedges).mapLe hHG = p := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    simp only [Walk.transfer, Walk.mapLe, Walk.map_cons]
    congr 1
    exact ih (fun e he => hedges e (by simp [he]))

private theorem transfer_snd {V : Type*} {G H : SimpleGraph V}
    {u v : V} (p : G.Walk u v)
    (hedges : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) :
    (p.transfer H hedges).snd = p.snd := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    simp only [Walk.transfer, Walk.snd_cons]

private theorem first_edge_mem' {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hpos : 0 < p.length) :
    s(u, p.snd) ∈ p.edges := by
  cases p with
  | nil => simp at hpos
  | cons h q => simp [Walk.edges_cons]

/-- In the spanning subgraph of a simple cycle, a path to the starting
vertex is fixed by its first edge. We use this to compare closed walks with
the same root and first step. -/
private theorem cycle_eq_of_same_root_first_step {u : G.Vertex}
    (p q : G.toSimpleGraph.Walk u u) (hp : p.IsCycle) (hq : q.IsCycle)
    (hedges : p.edges.toFinset = q.edges.toFinset)
    (hsnd : p.snd = q.snd) : p = q := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | @cons _ b _ hab pt =>
    cases q with
    | nil => exact (hq.not_nil (by simp)).elim
    | @cons _ b' _ hab' qt =>
      have hb : b = b' := by simpa using hsnd
      subst b'
      have hptPath : pt.IsPath := (Walk.cons_isCycle_iff pt hab).1 hp |>.1
      have hqtPath : qt.IsPath := (Walk.cons_isCycle_iff qt hab').1 hq |>.1
      have hptLen : 1 < pt.length := by
        have hh := hp.three_le_length
        simp only [Walk.length_cons] at hh
        omega
      have hqtLen : 1 < qt.length := by
        have hh := hq.three_le_length
        simp only [Walk.length_cons] at hh
        omega
      have hptEnd : pt.snd ≠ u := by
        intro he
        have hend := hptPath.getVert_eq_end_iff (by omega : 1 ≤ pt.length)
        have hi : pt.getVert 1 = u := by
          cases pt with
          | nil => simp at hptLen
          | cons hadj t => simpa [Walk.getVert] using he
        have := hend.mp hi
        omega
      have hqtEnd : qt.snd ≠ u := by
        intro he
        have hend := hqtPath.getVert_eq_end_iff (by omega : 1 ≤ qt.length)
        have hi : qt.getVert 1 = u := by
          cases qt with
          | nil => simp at hqtLen
          | cons hadj t => simpa [Walk.getVert] using he
        have := hend.mp hi
        omega
      let H := (Walk.cons hab pt).toSubgraph.spanningCoe
      have hpEdges : ∀ e, e ∈ pt.edges → e ∈ H.edgeSet := by
        intro e he
        change e ∈ (Walk.cons hab pt).toSubgraph.edgeSet
        exact (Walk.cons hab pt).mem_edges_toSubgraph.2 (by simp [Walk.edges_cons, he])
      have hqEdges : ∀ e, e ∈ qt.edges → e ∈ H.edgeSet := by
        intro e he
        apply hpEdges
        have hmem : e ∈ (Walk.cons hab' qt).edges := by simp [Walk.edges_cons, he]
        have hmem' : e ∈ (Walk.cons hab pt).edges :=
          walk_mem_edges_subset (Walk.cons hab pt) (Walk.cons hab' qt) hedges e hmem
        have hne : e ≠ s(u, b) := by
          intro heq
          have hnot := (Walk.cons_isCycle_iff qt hab').1 hq |>.2
          apply hnot
          simpa [heq] using he
        have hmemPt : e ∈ pt.edges := by
          simpa [Walk.edges_cons, hne] using hmem'
        exact hmemPt
      let ptH := pt.transfer H hpEdges
      let qtH := qt.transfer H hqEdges
      have hcycles : H.IsCycles := by
        dsimp [H]
        exact hp.isCycles_spanningCoe_toSubgraph
      have hpPathH : ptH.IsPath := SimpleGraph.Walk.IsPath.transfer hpEdges hptPath
      have hqPathH : qtH.IsPath := SimpleGraph.Walk.IsPath.transfer hqEdges hqtPath
      have hlenPtH : ptH.length = pt.length := by simp [ptH]
      have hlenQtH : qtH.length = qt.length := by simp [qtH]
      have hadj : H.Adj u b := by
        change s(u, b) ∈ (Walk.cons hab pt).toSubgraph.edgeSet
        exact (Walk.cons hab pt).mem_edges_toSubgraph.2 (by simp [Walk.edges_cons])
      have hptPos : 0 < ptH.length := by rw [hlenPtH]; omega
      have hqtPos : 0 < qtH.length := by rw [hlenQtH]; omega
      have hptAdj : H.Adj b ptH.snd :=
        ptH.adj_snd ((Walk.not_nil_iff_lt_length).2 hptPos)
      have hqtAdj : H.Adj b qtH.snd :=
        qtH.adj_snd ((Walk.not_nil_iff_lt_length).2 hqtPos)
      have hptSnd : u ≠ ptH.snd := by
        rw [transfer_snd]
        exact hptEnd.symm
      have hqtSnd : u ≠ qtH.snd := by
        rw [transfer_snd]
        exact hqtEnd.symm
      obtain ⟨z, hz, hzuniq⟩ := hcycles.existsUnique_ne_adj hadj.symm
      have heqSnd : ptH.snd = qtH.snd := by
        exact (hzuniq ptH.snd ⟨hptSnd, hptAdj⟩).trans
          (hzuniq qtH.snd ⟨hqtSnd, hqtAdj⟩).symm
      have htailEq := path_eq_of_first_edge H hcycles ptH qtH
        hpPathH hqPathH (by exact hab.ne.symm) heqSnd
      have htailMap := congrArg (fun w : H.Walk b u => w.mapLe ((Walk.cons hab pt).toSubgraph.spanningCoe_le)) htailEq
      have htail : pt = qt := by
        change ptH.mapLe _ = qtH.mapLe _ at htailMap
        rw [transfer_mapLe_id _ pt hpEdges, transfer_mapLe_id _ qt hqEdges] at htailMap
        exact htailMap
      cases htail
      rfl

/-- Two simple cycle walks with the same unordered edge set are rotations of
one another, up to reversal. -/
theorem cycle_eq_rotate_or_reverse_of_edges_eq {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u u) (q : G.toSimpleGraph.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    ∃ h : v ∈ p.support, q = p.rotate h ∨ q = (p.rotate h).reverse := by
  have hqpos : 0 < q.length := by
    have hh := hq.three_le_length
    omega
  have hqfirst : s(v, q.snd) ∈ q.edges := first_edge_mem' q hqpos
  have hfirstP : s(v, q.snd) ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [hedges]
    exact List.mem_toFinset.mpr hqfirst
  have hroot : v ∈ p.support := p.fst_mem_support_of_mem_edges hfirstP
  let p' := p.rotate hroot
  have hp' : p'.IsCycle := hp.rotate hroot
  have hp'pos : 0 < p'.length := by
    have hh := hp'.three_le_length
    omega
  have hrotEdges : p'.edges.toFinset = p.edges.toFinset := by
    ext e
    have hpPerm := (p.rotate_edges hroot).perm
    simp only [List.mem_toFinset]
    exact hpPerm.mem_iff
  have hedge' : p'.edges.toFinset = q.edges.toFinset := hrotEdges.trans hedges
  have hcycles : p'.toSubgraph.spanningCoe.IsCycles :=
    hp'.isCycles_spanningCoe_toSubgraph
  have hadjP : p'.toSubgraph.spanningCoe.Adj v p'.snd := by
    change s(v, p'.snd) ∈ p'.toSubgraph.edgeSet
    have he : s(v, p'.snd) ∈ p'.edges := first_edge_mem' p' hp'pos
    exact p'.mem_edges_toSubgraph.2 he
  have hadjQ : p'.toSubgraph.spanningCoe.Adj v q.snd := by
    change s(v, q.snd) ∈ p'.toSubgraph.edgeSet
    apply p'.mem_edges_toSubgraph.2
    apply List.mem_toFinset.mp
    rw [hedge']
    exact List.mem_toFinset.mpr hqfirst
  have hrevNe : p'.snd ≠ p'.reverse.snd := by
    rw [Walk.snd_reverse]
    exact hp'.snd_ne_penultimate
  have hadjRev : p'.toSubgraph.spanningCoe.Adj v p'.reverse.snd := by
    change s(v, p'.reverse.snd) ∈ p'.toSubgraph.edgeSet
    apply p'.mem_edges_toSubgraph.2
    have hpPerm : p'.reverse.edges.Perm p'.edges := by simp
    have hrevpos : 0 < p'.reverse.length := by simpa using hp'pos
    have he : s(v, p'.reverse.snd) ∈ p'.reverse.edges := first_edge_mem' p'.reverse hrevpos
    exact hpPerm.mem_iff.mp he
  have hfirstChoice : q.snd = p'.snd ∨ q.snd = p'.reverse.snd := by
    obtain ⟨z, hz, huniq⟩ := hcycles.existsUnique_ne_adj hadjP
    by_cases heq : q.snd = p'.snd
    · exact Or.inl heq
    · have hqz : q.snd = z := huniq q.snd ⟨by
        intro h
        exact heq h.symm, hadjQ⟩
      have hrevz : p'.reverse.snd = z := huniq p'.reverse.snd ⟨hrevNe, hadjRev⟩
      exact Or.inr (hqz.trans hrevz.symm)
  rcases hfirstChoice with hsame | hsame
  · have heq := cycle_eq_of_same_root_first_step p' q hp' hq hedge' hsame.symm
    exact ⟨hroot, Or.inl heq.symm⟩
  · have hedgeRev : p'.reverse.edges.toFinset = q.edges.toFinset := by
      simpa [Walk.edges_reverse] using hedge'
    have hrev : p'.reverse = q :=
      cycle_eq_of_same_root_first_step p'.reverse q hp'.reverse hq hedgeRev hsame.symm
    exact ⟨hroot, Or.inr hrev.symm⟩

private theorem mem_support_tail_of_isCycle {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u u) (hp : p.IsCycle)
    (hv : v ∈ p.support) : v ∈ p.support.tail := by
  cases p with
  | nil => exact False.elim (hp.not_nil (by simp))
  | cons h t =>
    have hv' : v ∈ u :: t.support := by simpa [Walk.support_cons] using hv
    rcases List.mem_cons.mp hv' with heq | htail
    · subst v
      exact t.end_mem_support
    · exact htail

private theorem physicalPair_exists_local {a : Sym2 G.Vertex}
    (ha : a ∈ G.toSimpleGraph.edgeSet) : ∃ e : G.Edge, physicalPair G e = a := by
  revert ha
  refine Sym2.inductionOn a ?_
  intro u v huv
  rcases huv with ⟨e, _, h | h⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inl h)⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inr h)⟩

private theorem walkWord_edge_image_local {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    (G.edgeSupport (walkWord G p)).image (physicalPair G) = p.edges.toFinset := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
    apply List.mem_toFinset.2
    exact (walkWord_nonzero_iff G p e).1 (Finset.mem_filter.1 he).2
  · intro ha
    have hm : a ∈ p.edges := List.mem_toFinset.1 ha
    have hbase : a ∈ G.toSimpleGraph.edgeSet :=
      p.toSubgraph.edgeSet_subset ((p.mem_edges_toSubgraph).2 hm)
    obtain ⟨e, he⟩ := physicalPair_exists_local hbase
    refine Finset.mem_image.2 ⟨e, ?_, he⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, (walkWord_nonzero_iff G p e).2 ?_⟩
    rwa [he]

private theorem cycleWord_eq_edges_toFinset_eq_any_roots
    {u v : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (q : G.toSimpleGraph.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle)
    (hword : cycleWordOfWalk G p hp = cycleWordOfWalk G q hq) :
    p.edges.toFinset = q.edges.toFinset := by
  have h := congrArg
    (fun C : G.CycleWord => (G.edgeSupport C.1).image (physicalPair G)) hword
  have hp := walkWord_edge_image_local p
  have hq := walkWord_edge_image_local q
  simpa only [cycleWordOfWalk, hp, hq] using h

/-- The physical word carried by a simple cyclic run. -/
noncomputable def simpleRunCycleWord (ell : ℕ)
    (r : simpleCyclicRuns G ell) : G.CycleWord :=
  cycleWordOfWalk G (cyclicRunWalk G ell r.1) r.2

/-- The associated physical word has the same length as the cyclic run. -/
theorem simpleRunCycleWord_length (ell : ℕ) (hell : 0 < ell)
    (r : simpleCyclicRuns G ell) :
    BoundaryDecay.Cycle.length (simpleRunCycleWord ell r) = ell := by
  rw [simpleRunCycleWord, cycleWordOfWalk_length,
    cyclicRunWalk_length G ell hell r.1]

abbrev SimpleRunFiber (ell : ℕ) (C : CycleWordsAtLength G ell) :=
  {r : simpleCyclicRuns G ell // simpleRunCycleWord ell r = C.1}

/-- Any simple closed walk rooted at a vertex on a fixed simple cycle is its
forward or reverse traversal, selected by its first step. -/
private theorem exists_root_orientation_for_equalCycleWord (ell : ℕ)
    (C : CycleWordsAtLength G ell) (r : simpleCyclicRuns G ell) :
    simpleRunCycleWord ell r = C.1 →
      ∃ z : RootChoices (chosenRootedSimpleCycle C).1.2 × Bool,
        walkDarts G (cyclicRunWalk G ell r.1) =
          walkDarts G (rootedOrientedWalk
            (chosenRootedSimpleCycle C).1.2 z.1 z.2) := by
  intro hword
  let c := chosenRootedSimpleCycle C
  let p := c.1.2
  let hp := c.2.1
  let q := cyclicRunWalk G ell r.1
  let x := tail G r.1.1.1.1
  have hcycleWord : cycleWordOfWalk G q r.2 =
      cycleWordOfWalk G p hp := by
    change simpleRunCycleWord ell r = _
    rw [hword, chosenRootedSimpleCycle_word]
  have hedge : p.edges.toFinset = q.edges.toFinset :=
    cycleWord_eq_edges_toFinset_eq_any_roots p q hp r.2 hcycleWord.symm
  obtain ⟨hroot, hforward | hreverse⟩ :=
    cycle_eq_rotate_or_reverse_of_edges_eq p q hp r.2 hedge
  · have htail := mem_support_tail_of_isCycle p hp hroot
    refine ⟨⟨⟨x, htail⟩, false⟩, ?_⟩
    simpa [rootedOrientedWalk] using congrArg (walkDarts G) hforward
  · have htail := mem_support_tail_of_isCycle p hp hroot
    refine ⟨⟨⟨x, htail⟩, true⟩, ?_⟩
    simpa [rootedOrientedWalk] using congrArg (walkDarts G) hreverse

noncomputable def simpleRunFiberCode (ell : ℕ) (C : CycleWordsAtLength G ell)
    (r : SimpleRunFiber ell C) : RootChoices ((chosenRootedSimpleCycle C).1.2) × Bool := by
  let z := Classical.choose (exists_root_orientation_for_equalCycleWord ell C r.1 r.2)
  exact z

theorem simpleRunFiberCode_spec (ell : ℕ) (C : CycleWordsAtLength G ell)
    (r : SimpleRunFiber ell C) :
    walkDarts G (cyclicRunWalk G ell r.1.1) = walkDarts G (rootedOrientedWalk
      (chosenRootedSimpleCycle C).1.2 (simpleRunFiberCode ell C r).1
        (simpleRunFiberCode ell C r).2) := by
  let z := Classical.choose (exists_root_orientation_for_equalCycleWord ell C r.1 r.2)
  have hz := Classical.choose_spec
    (exists_root_orientation_for_equalCycleWord ell C r.1 r.2)
  simpa [simpleRunFiberCode, z] using hz

noncomputable instance simpleRunFiberFintype (ell : ℕ) (C : CycleWordsAtLength G ell) :
    Fintype (SimpleRunFiber ell C) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun r : simpleCyclicRuns G ell => simpleRunCycleWord ell r = C.1)
    (by intro r; simp [SimpleRunFiber])

/-- Each physical cycle word of length `ell` has at most `2 ell` simple
cyclic-run representatives. -/
theorem simpleRunFiber_card_le (ell : ℕ) (hell : 0 < ell)
    (C : CycleWordsAtLength G ell) :
    Fintype.card (SimpleRunFiber ell C) ≤ 2 * ell := by
  classical
  letI : Fintype (simpleCyclicRuns G ell) := simpleCyclicRunsFintype G ell
  let p := (chosenRootedSimpleCycle C).1.2
  let hp := (chosenRootedSimpleCycle C).2.1
  let enc : SimpleRunFiber ell C → RootChoices p × Bool := fun r => simpleRunFiberCode ell C r
  have henc r : walkDarts G (cyclicRunWalk G ell r.1.1) =
      walkDarts G (rootedOrientedWalk p (enc r).1 (enc r).2) :=
    simpleRunFiberCode_spec ell C r
  have hinj : Function.Injective enc := by
    intro r s hrs
    have hwalk : walkDarts G (cyclicRunWalk G ell r.1.1) =
        walkDarts G (cyclicRunWalk G ell s.1.1) := by
      calc
        _ = walkDarts G (rootedOrientedWalk p (enc r).1 (enc r).2) := henc r
        _ = walkDarts G (rootedOrientedWalk p (enc s).1 (enc s).2) := by rw [hrs]
        _ = _ := (henc s).symm
    have hrun : r.1.1 = s.1.1 := by
      apply cyclicRuns_eq_of_same_rotated_dart_word G ell 0 hell (Nat.zero_le ell)
      simpa [hwalk]
    apply Subtype.ext
    apply Subtype.ext
    exact hrun
  have hrootCard : Fintype.card (RootChoices p) = ell := by
    rw [card_rootChoices p hp]
    simpa [p] using (chosenRootedSimpleCycle C).2.2
  calc
    Fintype.card (SimpleRunFiber ell C) ≤ Fintype.card (RootChoices p × Bool) :=
      Fintype.card_le_of_injective enc hinj
    _ = 2 * ell := by simp [hrootCard, Fintype.card_bool]; omega







end
end Erdos1016.Proof.CycleSupportFibers

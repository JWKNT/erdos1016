import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking

variable {G : PhysicalGraph} {u v : G.Vertex}

local instance finiteProofDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def run_append_step : ∀ (k : ℕ) {d e f : Dart G},
    Run G k d e → Next G e f → Run G (k + 1) d f := by
  intro k
  induction k with
  | zero =>
      intro d e f r h
      have he : d = e := r.2
      subst e
      exact ⟨f, ⟨(), h⟩, ⟨(), rfl⟩⟩
  | succ k ih =>
      intro d e f r h
      rcases r with ⟨a, ha, r⟩
      exact ⟨a, ha, ih r h⟩

theorem run_append_step_darts : ∀ (k : ℕ) {d e f : Dart G}
    (r : Run G k d e) (h : Next G e f),
    runDarts G (k + 1) (run_append_step k r h) = runDarts G k r ++ [f] := by
  intro k
  induction k with
  | zero =>
      intro d e f r h
      have he : d = e := r.2
      subst e
      simp [run_append_step, runDarts]
  | succ k ih =>
      intro d e f r h
      rcases r with ⟨u, hu, r⟩
      have hs : run_append_step (k + 1) (⟨u, hu, r⟩ : Run G (k + 1) d e) h =
          ⟨u, hu, run_append_step k r h⟩ := rfl
      rw [hs]
      change d :: runDarts G (k + 1) (run_append_step k r h) =
        d :: (runDarts G k r ++ [f])
      rw [ih r h]

theorem runDarts_cast {m n : ℕ} (h : m = n) {d e : Dart G}
    (r : Run G m d e) : runDarts G n (h ▸ r) = runDarts G m r := by
  cases h
  rfl



theorem path_has_dart_run : ∀ {a b : G.Vertex} (p : G.toSimpleGraph.Walk a b),
      p.IsPath → 0 < p.length →
      ∃ d e : Dart G, tail G d = a ∧ head G d = p.snd ∧
        tail G e = p.penultimate ∧ head G e = b ∧
        ∃ r : Run G (p.length - 1) d e,
          runDarts G (p.length - 1) r = walkDarts G p := by
  intro a b p
  induction p with
  | nil =>
      intro hp hl
      simp at hl
  | @cons a b c hab q ih =>
      intro hp hl
      change (SimpleGraph.Walk.cons hab q).IsPath at hp
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons] at hp
      rcases List.nodup_cons.mp hp with ⟨haq, hqnodup⟩
      let d := dartOfAdj G hab
      have htail : tail G d = a := tail_dartOfAdj G hab
      have hhead : head G d = b := head_dartOfAdj G hab
      cases q with
      | nil =>
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hl ⊢
          refine ⟨d, d, htail, ?_, ?_, hhead, ?_⟩
          · simpa using hhead
          · exact htail
          · refine ⟨⟨(), rfl⟩, ?_⟩
            simp [runDarts, walkDarts, d]
      | @cons b c z hbc r =>
          have hqpath : (SimpleGraph.Walk.cons hbc r).IsPath :=
            SimpleGraph.Walk.IsPath.mk' hqnodup
          have hqpos : 0 < (SimpleGraph.Walk.cons hbc r).length := by simp
          obtain ⟨e, f, htailE, hheadE, htailF, hheadF, rr, hrr⟩ := ih hqpath hqpos
          have hnoreturn : head G e ≠ a := by
            intro h
            apply haq
            have hmem : s(b, c) ∈ (SimpleGraph.Walk.cons hbc r).edges := by
              simp [SimpleGraph.Walk.edges]
            have hcq := SimpleGraph.Walk.snd_mem_support_of_mem_edges
              (SimpleGraph.Walk.cons hbc r) hmem
            have hce : c = a := by
              simpa [SimpleGraph.Walk.snd] using hheadE.symm.trans h
            exact hce ▸ hcq
          have hnext : Next G d e := by
            refine ⟨?_, ?_⟩
            · rw [hhead, htailE]
            · intro hrev
              apply hnoreturn
              rw [hrev, head_reverse, htail]
          have hlen : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc r)).length - 1 =
              (SimpleGraph.Walk.cons hbc r).length := by simp
          have hqidx : (SimpleGraph.Walk.cons hbc r).length - 1 = r.length := by simp
          let rr' : Run G r.length e f := hqidx ▸ rr
          have hrr' : runDarts G r.length rr' = walkDarts G (SimpleGraph.Walk.cons hbc r) := by
            simpa [rr', hqidx] using hrr
          let rrnew : Run G (r.length + 1) d f := ⟨e, ⟨(), hnext⟩, rr'⟩
          have hlist : runDarts G (r.length + 1) rrnew =
              walkDarts G (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc r)) := by
            simp [rrnew, runDarts, walkDarts, d, hrr']
          refine ⟨d, f, htail, ?_, ?_, hheadF, ?_⟩
          · simpa using hhead
          · simpa [SimpleGraph.Walk.penultimate] using htailF
          rw [hlen]
          exact ⟨rrnew, hlist⟩

theorem cycle_has_closed_run {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) : ∃ d : Dart G, tail G d = a ∧ head G d = p.snd ∧
      ∃ r : Run G p.length d d, runDarts G p.length r = walkDarts G p ++ [d] := by
  cases p with
  | nil => exact False.elim (hp.not_nil (by simp))
  | @cons a b _ hab q =>
      let cyc : G.toSimpleGraph.Walk a a := SimpleGraph.Walk.cons hab q
      have hcycle := (SimpleGraph.Walk.cons_isCycle_iff q hab).1 hp
      rcases hcycle with ⟨hqpath, hnotedge⟩
      have hpos : 0 < q.length := by
        have := hp.three_le_length
        simp only [SimpleGraph.Walk.length_cons] at this
        omega
      obtain ⟨e, f, htailE, hheadE, htailF, hheadF, rr, hrr⟩ :=
        path_has_dart_run q hqpath hpos
      let d := dartOfAdj G hab
      have htailD : tail G d = a := tail_dartOfAdj G hab
      have hheadD : head G d = b := head_dartOfAdj G hab
      have hstep : Next G d e := by
        refine ⟨?_, ?_⟩
        · rw [hheadD, htailE]
        · intro hrev
          have hbad : q.snd = a := by
            calc
              q.snd = head G e := hheadE.symm
              _ = tail G d := by rw [hrev, head_reverse]
              _ = a := htailD
          apply hnotedge
          have hmem : s(b, q.snd) ∈ q.edges := by
            cases q with
            | nil => simp at hpos
            | cons h r => simp [SimpleGraph.Walk.edges]
          simpa [hbad, Sym2.eq_swap] using hmem
      let rlinear : Run G ((q.length - 1) + 1) d f := ⟨e, ⟨(), hstep⟩, rr⟩
      have hqidx : (q.length - 1) + 1 = q.length := Nat.sub_add_cancel (by omega)
      let rline : Run G q.length d f := hqidx ▸ rlinear
      have hline : runDarts G q.length rline = walkDarts G cyc := by
        have hlinear : runDarts G ((q.length - 1) + 1) rlinear =
            walkDarts G cyc := by
          simpa [cyc, rlinear, runDarts, walkDarts, d, hrr]
        calc
          runDarts G q.length rline = runDarts G ((q.length - 1) + 1) rlinear :=
            runDarts_cast hqidx rlinear
          _ = walkDarts G cyc := hlinear
      have htailF' : tail G f = cyc.penultimate := by
        have : cyc.penultimate = q.penultimate := by
          exact SimpleGraph.Walk.penultimate_cons_of_not_nil hab q (by
            intro hnil
            cases hnil
            simp at hpos)
        rw [this]
        exact htailF
      have hclose : Next G f d := by
        refine ⟨?_, ?_⟩
        · rw [hheadF, htailD]
        · intro hrev
          apply hp.snd_ne_penultimate
          calc
            cyc.snd = head G d := by simpa [cyc, SimpleGraph.Walk.snd] using hheadD.symm
            _ = head G (reverse G f) := by rw [hrev]
            _ = tail G f := head_reverse G f
            _ = cyc.penultimate := htailF'
      refine ⟨d, htailD, ?_, ?_⟩
      · simpa [cyc, SimpleGraph.Walk.snd] using hheadD
      have hcycidx : cyc.length - 1 = q.length := by simp [cyc]
      let rbase : Run G (cyc.length - 1) d f := hcycidx ▸ rline
      let rclosed := run_append_step (cyc.length - 1) rbase hclose
      have hcycpos : 1 ≤ cyc.length := by
        simpa [cyc] using Nat.succ_le_succ (Nat.zero_le q.length)
      have hclosedList : runDarts G ((cyc.length - 1) + 1) rclosed =
          walkDarts G cyc ++ [d] := by
        have hs := run_append_step_darts (cyc.length - 1) rbase hclose
        have hbaseList : runDarts G (cyc.length - 1) rbase = walkDarts G cyc := by
          calc
            runDarts G (cyc.length - 1) rbase = runDarts G q.length rline :=
              runDarts_cast hcycidx rline
            _ = walkDarts G cyc := hline
        rw [hbaseList] at hs
        exact hs
      refine ⟨?_, ?_⟩
      · exact Nat.sub_add_cancel hcycpos ▸ rclosed
      · simpa [Nat.sub_add_cancel hcycpos, cyc] using hclosedList

abbrev RootChoices {a : G.Vertex} (p : G.toSimpleGraph.Walk a a) :=
  {v : G.Vertex // v ∈ p.support.tail}

def rootedOrientedWalk {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (x : RootChoices p) (orientation : Bool) :
    G.toSimpleGraph.Walk x.1 x.1 :=
  let hroot : x.1 ∈ p.support := List.mem_of_mem_tail x.2
  let q := p.rotate hroot
  if orientation then q.reverse else q

theorem rootedOrientedWalk_cycle {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) :
    (rootedOrientedWalk p x orientation).IsCycle := by
  dsimp [rootedOrientedWalk]
  split
  · exact (hp.rotate (List.mem_of_mem_tail x.2)).reverse
  · exact hp.rotate (List.mem_of_mem_tail x.2)

noncomputable def rootedCycleStartDart {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) : Dart G :=
  Classical.choose (cycle_has_closed_run (rootedOrientedWalk p x orientation)
    (rootedOrientedWalk_cycle p hp x orientation))

theorem rootedCycleStartDart_tail {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) :
    tail G (rootedCycleStartDart p hp x orientation) = x.1 :=
  (Classical.choose_spec (cycle_has_closed_run (rootedOrientedWalk p x orientation)
    (rootedOrientedWalk_cycle p hp x orientation))).1

theorem rootedCycleStartDart_head {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) :
    head G (rootedCycleStartDart p hp x orientation) =
      (rootedOrientedWalk p x orientation).snd :=
  (Classical.choose_spec (cycle_has_closed_run (rootedOrientedWalk p x orientation)
    (rootedOrientedWalk_cycle p hp x orientation))).2.1

theorem rootedCycleStartDart_injective {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) :
    Function.Injective (fun z : RootChoices p × Bool =>
      rootedCycleStartDart p hp z.1 z.2) := by
  intro z w h
  obtain ⟨x, bx⟩ := z
  obtain ⟨y, b2⟩ := w
  have hv : x.1 = y.1 := by
    have ht := congrArg (tail G) h
    simpa only [rootedCycleStartDart_tail] using ht
  have hxy : x = y := Subtype.ext hv
  subst y
  cases bx <;> cases b2
  · rfl
  · have hh := congrArg (head G) h
    rw [rootedCycleStartDart_head, rootedCycleStartDart_head] at hh
    change (p.rotate (List.mem_of_mem_tail x.2)).snd =
      ((p.rotate (List.mem_of_mem_tail x.2)).reverse).snd at hh
    rw [SimpleGraph.Walk.snd_reverse] at hh
    exact False.elim ((hp.rotate (List.mem_of_mem_tail x.2)).snd_ne_penultimate hh)
  · have hh := congrArg (head G) h
    rw [rootedCycleStartDart_head, rootedCycleStartDart_head] at hh
    change ((p.rotate (List.mem_of_mem_tail x.2)).reverse).snd =
      (p.rotate (List.mem_of_mem_tail x.2)).snd at hh
    rw [SimpleGraph.Walk.snd_reverse] at hh
    exact False.elim ((hp.rotate (List.mem_of_mem_tail x.2)).snd_ne_penultimate hh.symm)
  · rfl

theorem length_rotate_walk {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (x : G.Vertex) (hx : x ∈ p.support) : (p.rotate hx).length = p.length := by
  simp only [SimpleGraph.Walk.rotate, SimpleGraph.Walk.length_append]
  have hs := congrArg SimpleGraph.Walk.length (p.take_spec hx)
  rw [SimpleGraph.Walk.length_append] at hs
  omega

theorem rootedOrientedWalk_length {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (x : RootChoices p) (orientation : Bool) :
    (rootedOrientedWalk p x orientation).length = p.length := by
  cases orientation
  · exact length_rotate_walk p x.1 (List.mem_of_mem_tail x.2)
  · simp only [rootedOrientedWalk, Bool.false_eq_true, ↓reduceIte,
      SimpleGraph.Walk.length_reverse]
    exact length_rotate_walk p x.1 (List.mem_of_mem_tail x.2)

noncomputable def rootedCycleRun {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) : AllRuns G p.length :=
  let q := rootedOrientedWalk p x orientation
  let hq := rootedOrientedWalk_cycle p hp x orientation
  let ex := cycle_has_closed_run q hq
  let d := Classical.choose ex
  let r : Run G q.length d d := Classical.choose (Classical.choose_spec ex).2.2
  let hlen : q.length = p.length := rootedOrientedWalk_length p x orientation
  ⟨d, d, hlen ▸ r⟩

theorem rootedCycleRun_darts {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) (x : RootChoices p) (orientation : Bool) :
    runDarts G p.length (rootedCycleRun p hp x orientation).2.2 =
      walkDarts G (rootedOrientedWalk p x orientation) ++
        [rootedCycleStartDart p hp x orientation] := by
  dsimp [rootedCycleRun]
  let q := rootedOrientedWalk p x orientation
  let hq := rootedOrientedWalk_cycle p hp x orientation
  let ex := cycle_has_closed_run q hq
  let d := Classical.choose ex
  let r : Run G q.length d d := Classical.choose (Classical.choose_spec ex).2.2
  have hrun := Classical.choose_spec (Classical.choose_spec ex).2.2
  have hlen : q.length = p.length := rootedOrientedWalk_length p x orientation
  change runDarts G p.length (hlen ▸ r) = walkDarts G q ++ [d]
  calc
    runDarts G p.length (hlen ▸ r) =
        runDarts G q.length r := runDarts_cast hlen _
    _ = walkDarts G q ++ [d] := hrun



theorem rotate_walkWord_eq (p : G.toSimpleGraph.Walk v v)
    (h : u ∈ p.support) : walkWord G (p.rotate h) = walkWord G p := by
  funext e
  simp only [walkWord]
  have hp := (p.rotate_edges h).perm
  simp [hp.mem_iff]

theorem physicalPair_dart (d : Dart G) :
    physicalPair G d.1 = s(tail G d, head G d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [physicalPair, tail, head, Sym2.eq_swap]

theorem physicalPair_dartOfAdj {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) :
    physicalPair G (dartOfAdj G h).1 = s(u, v) := by
  rw [physicalPair_dart, tail_dartOfAdj, head_dartOfAdj]

theorem walkDarts_map_physicalPair {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    (walkDarts G p).map (fun d => physicalPair G d.1) = p.edges := by
  induction p with
  | nil => rfl
  | @cons u v w h q ih =>
      simp [walkDarts, SimpleGraph.Walk.edges, physicalPair_dartOfAdj, ih]









/-- Reversing a closed walk does not change the underlying edge-support word. -/
theorem reverse_walkWord_eq (p : G.toSimpleGraph.Walk v v) :
    walkWord G p.reverse = walkWord G p := by
  funext e
  simp only [walkWord]
  have hp : p.reverse.edges.Perm p.edges := by
    rw [SimpleGraph.Walk.edges_reverse]
    exact List.reverse_perm p.edges
  simp [hp.mem_iff]



theorem rootedOrientedWalk_word_eq {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (x : RootChoices p) (orientation : Bool) :
    walkWord G (rootedOrientedWalk p x orientation) = walkWord G p := by
  cases orientation
  · exact rotate_walkWord_eq p (List.mem_of_mem_tail x.2)
  · change walkWord G ((p.rotate (List.mem_of_mem_tail x.2)).reverse) = walkWord G p
    rw [reverse_walkWord_eq]
    exact rotate_walkWord_eq p (List.mem_of_mem_tail x.2)



/-!
The lemmas above prove that every rooted/oriented cycle choice gives a distinct
closed run and that the chosen run serializes to the oriented cycle's dart list
followed by the repeated starting dart.  They also prove rotation and reversal
invariance for the source walk's edge-support word.

The support-word bridge is proved above: serialization transfers through
`walkDarts_runWalk`, and the first dart equals the appended seam dart, so that
the seam edge is already in the cycle's edge list.  The rooted-run word theorem
identifies the run walk's support with the source cycle's support.
-/

theorem card_rootChoices {a : G.Vertex} (p : G.toSimpleGraph.Walk a a)
    (hp : p.IsCycle) : Fintype.card (RootChoices p) = p.length := by
  let e : RootChoices p ≃ {v : G.Vertex // v ∈ p.support.tail.toFinset} := {
    toFun := fun x => ⟨x.1, List.mem_toFinset.2 x.2⟩
    invFun := fun x => ⟨x.1, List.mem_toFinset.1 x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Fintype.card (RootChoices p) = Fintype.card {v : G.Vertex // v ∈ p.support.tail.toFinset} :=
      Fintype.card_congr e
    _ = p.support.tail.toFinset.card := by
      simpa only [Fintype.card_coe]
    _ = p.support.tail.length := List.toFinset_card_of_nodup hp.support_nodup
    _ = p.length := by simp [List.length_tail, SimpleGraph.Walk.length_support]



end Erdos1016.Nonbacktracking
end

import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace Erdos1016.Proof.CyclePathUniqueness

open SimpleGraph

private theorem path_tail_snd_eq {V : Type*} [Finite V] [DecidableEq V]
    (H : SimpleGraph V) (hcycles : H.IsCycles)
    {u b v : V} (p q : H.Walk b v)
    (hp : p.IsPath) (hq : q.IsPath) (hadj : H.Adj u b)
    (hup : u ∉ p.support) (huq : u ∉ q.support) : p.snd = q.snd := by
  by_cases hbv : b = v
  · subst v
    have hpNil : p = Walk.nil := (Walk.isPath_iff_eq_nil p).mp hp
    have hqNil : q = Walk.nil := (Walk.isPath_iff_eq_nil q).mp hq
    subst p
    subst q
    rfl
  · cases p with
    | nil => exact (hbv rfl).elim
    | @cons _ x v hbx p' =>
      cases q with
      | nil => exact (hbv rfl).elim
      | @cons _ y v hby q' =>
        have hu_ne_x : u ≠ x := by
          intro hx
          subst x
          exact hup (by simp [Walk.support_cons, p'.start_mem_support])
        have hu_ne_y : u ≠ y := by
          intro hy
          subst y
          exact huq (by simp [Walk.support_cons, q'.start_mem_support])
        obtain ⟨z, hz, huniq⟩ := hcycles.existsUnique_ne_adj hadj.symm
        have hx : x = z := huniq x ⟨hu_ne_x, hbx⟩
        have hy : y = z := huniq y ⟨hu_ne_y, hby⟩
        simpa [hx, hy]

/-- In a graph whose non-isolated vertices have degree two, a simple path
between distinct endpoints is determined by its first edge. -/
theorem path_eq_of_first_edge {V : Type*} [Finite V] [DecidableEq V]
    (H : SimpleGraph V) (hcycles : H.IsCycles)
    {u v : V} (p q : H.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (huv : u ≠ v) (hsnd : p.snd = q.snd) : p = q := by
  cases p with
  | nil => exact (huv rfl).elim
  | @cons _ b v hab pTail =>
    cases q with
    | nil => exact (huv rfl).elim
    | @cons _ b' v hab' qTail =>
      have hhead : b = b' := by simpa using hsnd
      subst b'
      have hpt : pTail.IsPath := (Walk.cons_isPath_iff hab pTail).mp hp |>.1
      have hqt : qTail.IsPath := (Walk.cons_isPath_iff hab' qTail).mp hq |>.1
      by_cases hbv : b = v
      · subst v
        have hpNil : pTail = Walk.nil := (Walk.isPath_iff_eq_nil pTail).mp hpt
        have hqNil : qTail = Walk.nil := (Walk.isPath_iff_eq_nil qTail).mp hqt
        subst pTail
        subst qTail
        rfl
      · have hnotp := (Walk.cons_isPath_iff hab pTail).mp hp |>.2
        have hnotq := (Walk.cons_isPath_iff hab' qTail).mp hq |>.2
        have hsndTail := path_tail_snd_eq H hcycles pTail qTail hpt hqt
          hab hnotp hnotq
        have htail : pTail = qTail :=
          path_eq_of_first_edge H hcycles pTail qTail hpt hqt hbv hsndTail
        rw [htail]

end Erdos1016.Proof.CyclePathUniqueness

import Erdos1016.ExactMaximum.NetBridgeCut
import Erdos1016.ExactMaximum.PoleReduce

set_option autoImplicit false

/-!
# The two sides of a bridge of a pole

Lemma 5.2 (b) of the paper "The maximum number of cycles in a graph of large rank" cuts a pole
with the two ports `s`, `t` at its bridges. This file proves one step. Let `N` be such a pole
with at least `0.501 · 2^b` paths from `s` to `t`, and let no cycle take the edge `e`. Then
(`exists_bridge_split`):

* the vertices that are joined to `s` without `e` form a cut `S` whose only crossing edge is `e`;
* `t` is not in `S`, and `e` joins `x ∈ S` and `y ∉ S` with `x ≠ s` and `y ≠ t`;
* the first side is a pole with the two ports `s`, `x`, and the second side is a pole with the
  two ports `y`, `t`.

A pole can have isolated vertices here (`IsWeakTwoPole`), so the two sides are networks on the
vertices of `N`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleSidesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*}

/-! ### Connections in a part of a network -/

/-- A connection in a part is a connection in a larger part. -/
theorem reachable_sub_mono (N : Network V E) {p q : E → Prop} (hpq : ∀ g, p g → q g) {a b : V}
    (h : (N.sub p).graph.Reachable a b) : (N.sub q).graph.Reachable a b := by
  refine (N.sub p).mem_of_reachable_of_closed (fun z => (N.sub q).graph.Reachable a z) ?_ h
    (SimpleGraph.Reachable.refl a)
  intro g
  have hadj : (N.sub q).graph.Adj (N.src g.1) (N.dst g.1) :=
    ⟨⟨g.1, hpq g.1 g.2⟩, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun k => k.trans hadj.reachable, fun k => k.trans hadj.symm.reachable⟩

/-- A connection in the network is a connection in a part that has all edges. -/
theorem reachable_sub_of_forall (N : Network V E) {p : E → Prop} (hp : ∀ g, p g) {a b : V}
    (h : N.graph.Reachable a b) : (N.sub p).graph.Reachable a b := by
  refine N.mem_of_reachable_of_closed (fun z => (N.sub p).graph.Reachable a z) ?_ h
    (SimpleGraph.Reachable.refl a)
  intro g
  have hadj : (N.sub p).graph.Adj (N.src g) (N.dst g) := ⟨⟨g, hp g⟩, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun k => k.trans hadj.reachable, fun k => k.trans hadj.symm.reachable⟩

/-! ### The side of a vertex without an edge -/

/-- The vertices that are joined to `s` without the edge `e`. -/
def sideOf (N : Network V E) (e : E) (s : V) (v : V) : Prop :=
  (N.sub fun g => g ≠ e).graph.Reachable s v

theorem sideOf_self (N : Network V E) (e : E) (s : V) : N.sideOf e s s :=
  SimpleGraph.Reachable.refl s

/-- An edge other than `e` has both ends in the side or none. -/
theorem sideOf_iff_of_ne (N : Network V E) (e : E) (s : V) {g : E} (hg : g ≠ e) :
    N.sideOf e s (N.src g) ↔ N.sideOf e s (N.dst g) := by
  have hadj : (N.sub fun g => g ≠ e).graph.Adj (N.src g) (N.dst g) :=
    ⟨⟨g, hg⟩, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun k => k.trans hadj.reachable, fun k => k.trans hadj.symm.reachable⟩

/-- Only the edge `e` can cross the cut of the side. -/
theorem eq_of_crosses_sideOf (N : Network V E) (e : E) (s : V) {g : E}
    (h : N.crosses (N.sideOf e s) g) : g = e :=
  Classical.not_not.1 fun hne => h (N.sideOf_iff_of_ne e s hne)

/-- Every vertex of the side is joined to `s` by edges of the side. -/
theorem reachable_inside_sideOf (N : Network V E) (e : E) (s : V) {v : V}
    (hv : N.sideOf e s v) : (N.sub (N.inside (N.sideOf e s))).graph.Reachable s v := by
  have key : N.sideOf e s v ∧ (N.sub (N.inside (N.sideOf e s))).graph.Reachable s v := by
    refine (N.sub fun g => g ≠ e).mem_of_reachable_of_closed
      (fun z => N.sideOf e s z ∧ (N.sub (N.inside (N.sideOf e s))).graph.Reachable s z) ?_ hv
      ⟨N.sideOf_self e s, SimpleGraph.Reachable.refl s⟩
    intro g
    have hS := N.sideOf_iff_of_ne e s g.2
    constructor
    · rintro ⟨h1, h2⟩
      have hadj : (N.sub (N.inside (N.sideOf e s))).graph.Adj (N.src g.1) (N.dst g.1) :=
        ⟨⟨g.1, ⟨h1, hS.1 h1⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨hS.1 h1, h2.trans hadj.reachable⟩
    · rintro ⟨h1, h2⟩
      have hadj : (N.sub (N.inside (N.sideOf e s))).graph.Adj (N.src g.1) (N.dst g.1) :=
        ⟨⟨g.1, ⟨hS.2 h1, h1⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact ⟨hS.2 h1, h2.trans hadj.symm.reachable⟩
  exact key.2

/-- A vertex that is joined to `s` is in the side of `s` or in the side of the other end of
`e`. -/
theorem sideOf_or_sideOf (N : Network V E) {e : E} {x y : V} (he : N.Joins e x y) (s : V)
    (hx : N.sideOf e s x) {v : V} (h : N.graph.Reachable s v) :
    N.sideOf e s v ∨ N.sideOf e y v := by
  refine N.mem_of_reachable_of_closed (fun z => N.sideOf e s z ∨ N.sideOf e y z) ?_ h
    (Or.inl (N.sideOf_self e s))
  intro g
  by_cases hg : g = e
  · have h1 : N.sideOf e s (N.src g) ∨ N.sideOf e y (N.src g) := by
      rw [hg]
      rcases he with ⟨k1, _⟩ | ⟨k1, _⟩
      · rw [k1]
        exact Or.inl hx
      · rw [k1]
        exact Or.inr (N.sideOf_self e y)
    have h2 : N.sideOf e s (N.dst g) ∨ N.sideOf e y (N.dst g) := by
      rw [hg]
      rcases he with ⟨_, k2⟩ | ⟨_, k2⟩
      · rw [k2]
        exact Or.inr (N.sideOf_self e y)
      · rw [k2]
        exact Or.inl hx
    exact ⟨fun _ => h2, fun _ => h1⟩
  · have hs := N.sideOf_iff_of_ne e s hg
    have hy := N.sideOf_iff_of_ne e y hg
    exact ⟨fun k => k.elim (fun k => Or.inl (hs.1 k)) (fun k => Or.inr (hy.1 k)),
      fun k => k.elim (fun k => Or.inl (hs.2 k)) (fun k => Or.inr (hy.2 k))⟩

variable [Fintype V] [Fintype E]

/-- If no cycle takes the edge `e`, the two ends of `e` are not joined without `e`. -/
theorem not_reachable_of_bridge (N : Network V E) {e : E}
    (hbr : ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0) {x y : V} (he : N.Joins e x y) :
    ¬ (N.sub fun g => g ≠ e).graph.Reachable x y := by
  intro h
  obtain ⟨P, hP, hPw⟩ := N.exists_isPathWord_of_reachable (fun g => g ≠ e) he.ne h
  have hPe : P e = 0 := Classical.not_not.1 fun hne => hPw e hne rfl
  have h1 := hbr _ (hP.add_closing he hPe)
  rw [Pi.add_apply, hPe, zero_add, unitWord_apply, if_pos rfl] at h1
  exact one_ne_zero h1

/-! ### Poles with two ports -/

/-- A pole, possibly with isolated vertices, whose ports are exactly `s` and `t`. -/
structure IsWeakTwoPole (N : Network V E) (s t : V) : Prop where
  pole : N.IsWeakPole
  port_s : N.IsPort s
  port_t : N.IsPort t
  ne : s ≠ t
  only : ∀ z, N.IsPort z → z = s ∨ z = t

omit [Fintype V] in
theorem IsWeakTwoPole.symm {N : Network V E} {s t : V} (h : N.IsWeakTwoPole s t) :
    N.IsWeakTwoPole t s :=
  ⟨h.pole, h.port_t, h.port_s, h.ne.symm, fun z hz => (h.only z hz).symm⟩

omit [Fintype V] in
/-- A vertex other than the two ports has degree zero or three. -/
theorem IsWeakTwoPole.deg_other {N : Network V E} {s t : V} (h : N.IsWeakTwoPole s t) {z : V}
    (hzs : z ≠ s) (hzt : z ≠ t) :
    N.deg (fun _ => 1) z = 0 ∨ N.deg (fun _ => 1) z = 3 := by
  rcases h.pole.1 z with k | k | k
  · exact Or.inl k
  · exact absurd (h.only z k) (fun k' => k'.elim hzs hzt)
  · exact Or.inr k

omit [Fintype V] in
/-- Every vertex of a pole has degree zero or at least two. -/
theorem IsWeakPole.deg_zero_or_two_le {N : Network V E} (h : N.IsWeakPole) (v : V) :
    N.deg (fun _ => 1) v = 0 ∨ 2 ≤ N.deg (fun _ => 1) v := by
  rcases h.1 v with k | k | k
  · exact Or.inl k
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)

/-! ### The degrees in a side of a cut with one crossing edge -/

omit [Fintype V] in
/-- The crossing edges at a vertex, when `e` is the only crossing edge. -/
theorem deg_crosses_of_one_crossing (N : Network V E) (S : V → Prop) {e : E} {x y : V}
    (he : N.Joins e x y) (hx : S x) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e) (v : V) :
    N.deg (restrict (fun _ => 1) (N.crosses S)) v = if v = x ∨ v = y then 1 else 0 := by
  have hce : N.crosses S e := N.crosses_of_joins he hx hy
  have hw : restrict (fun _ => (1 : Bit)) (N.crosses S) = unitWord e := by
    funext g
    by_cases hg : N.crosses S g
    · rw [restrict_apply_of_pos _ hg, hC g hg, unitWord_apply, if_pos rfl]
    · rw [restrict_apply_of_neg _ hg, unitWord_apply, if_neg (fun h : e = g => hg (h ▸ hce))]
  rw [hw]
  by_cases hvx : v = x
  · rw [if_pos (Or.inl hvx), hvx]
    exact N.deg_unitWord_eq_one he.at_left
  · by_cases hvy : v = y
    · rw [if_pos (Or.inr hvy), hvy]
      exact N.deg_unitWord_eq_one he.at_right
    · rw [if_neg (fun h => h.elim hvx hvy)]
      exact N.deg_unitWord_of_joins he hvx hvy

omit [Fintype V] in
/-- The degree of a vertex of `S` in the first side. -/
theorem deg_inside_of_one_crossing (N : Network V E) (S : V → Prop) {e : E} {x y : V}
    (he : N.Joins e x y) (hx : S x) (hy : ¬ S y) (hC : ∀ g, N.crosses S g → g = e) {v : V}
    (hv : S v) :
    (N.sub (N.inside S)).deg (fun _ => 1) v + (if v = x then 1 else 0) =
      N.deg (fun _ => 1) v := by
  have h1 := N.deg_split S v
  rw [N.deg_outside_eq_zero S hv, add_zero, N.deg_crosses_of_one_crossing S he hx hy hC v] at h1
  rw [N.deg_sub_ones (N.inside S) v, h1]
  by_cases hvx : v = x
  · rw [if_pos hvx, if_pos (Or.inl hvx)]
  · rw [if_neg hvx, if_neg (fun h => h.elim hvx (fun k => hy (k ▸ hv)))]

omit [Fintype V] in
/-- A vertex outside `S` is on no edge of the first side. -/
theorem deg_inside_of_not_mem (N : Network V E) (S : V → Prop) {v : V} (hv : ¬ S v) :
    (N.sub (N.inside S)).deg (fun _ => 1) v = 0 := by
  rw [N.deg_sub_ones (N.inside S) v]
  exact N.deg_inside_eq_zero S hv

omit [Fintype V] in
/-- **A side of a cut with one crossing edge is a pole with two ports.** Let `N` be a pole with
the two ports `s`, `t`, and let the only crossing edge `e` of the cut `S` join `x ∈ S` and
`y ∉ S`, where `s ∈ S`, `t ∉ S` and `x ≠ s`. If every vertex of `S` of positive degree is joined
to `s` in the first side, then the first side is a pole with the two ports `s`, `x`. -/
theorem isWeakTwoPole_side (N : Network V E) {s t : V} (hN : N.IsWeakTwoPole s t)
    (S : V → Prop) {e : E} {x y : V} (he : N.Joins e x y) (hx : S x) (hy : ¬ S y)
    (hC : ∀ g, N.crosses S g → g = e) (hs : S s) (ht : ¬ S t) (hxs : x ≠ s)
    (hin : ∀ v, S v → 0 < N.deg (fun _ => 1) v →
      (N.sub (N.inside S)).graph.Reachable s v) :
    (N.sub (N.inside S)).IsWeakTwoPole s x := by
  have hxt : x ≠ t := fun h => ht (h ▸ hx)
  have hst : s ≠ t := hN.ne
  have hone : (fun _ : E => (1 : Bit)) e ≠ 0 := one_ne_zero
  -- the degree of `x` in `N` is three
  have hxpos : 0 < N.deg (fun _ => 1) x := by
    rcases he.at_left with h | h
    · rw [← h]
      exact N.deg_src_pos hone
    · rw [← h]
      exact N.deg_dst_pos hone
  have hx3 : N.deg (fun _ => 1) x = 3 := by
    rcases hN.deg_other hxs hxt with h | h
    · omega
    · exact h
  have hdx : (N.sub (N.inside S)).deg (fun _ => 1) x = 2 := by
    have h := N.deg_inside_of_one_crossing S he hx hy hC hx
    rw [if_pos rfl, hx3] at h
    omega
  have hds : (N.sub (N.inside S)).deg (fun _ => 1) s = 2 := by
    have h := N.deg_inside_of_one_crossing S he hx hy hC hs
    rw [if_neg (fun k : s = x => hxs k.symm), add_zero] at h
    rw [h]
    exact hN.port_s
  -- the other vertices
  have hother : ∀ v, v ≠ s → v ≠ x →
      (N.sub (N.inside S)).deg (fun _ => 1) v = 0 ∨
        (N.sub (N.inside S)).deg (fun _ => 1) v = 3 := by
    intro v hvs hvx
    by_cases hv : S v
    · have h := N.deg_inside_of_one_crossing S he hx hy hC hv
      rw [if_neg hvx, add_zero] at h
      rw [h]
      exact hN.deg_other hvs (fun k => ht (k ▸ hv))
    · exact Or.inl (N.deg_inside_of_not_mem S hv)
  have hle : ∀ v, (N.sub (N.inside S)).deg (fun _ => 1) v ≤ N.deg (fun _ => 1) v := by
    intro v
    by_cases hv : S v
    · have h := N.deg_inside_of_one_crossing S he hx hy hC hv
      omega
    · rw [N.deg_inside_of_not_mem S hv]
      exact Nat.zero_le _
  have hmem : ∀ v, 0 < (N.sub (N.inside S)).deg (fun _ => 1) v → S v := by
    intro v hpos
    refine Classical.not_not.1 fun hv => ?_
    rw [N.deg_inside_of_not_mem S hv] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨⟨fun v => ?_, fun u v hu hv => ?_⟩, hds, hdx, fun k => hxs k.symm, fun z hz => ?_⟩
  · by_cases hvs : v = s
    · rw [hvs]
      exact Or.inr (Or.inl hds)
    · by_cases hvx : v = x
      · rw [hvx]
        exact Or.inr (Or.inl hdx)
      · rcases hother v hvs hvx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  · have h1 := hin u (hmem u hu) (lt_of_lt_of_le hu (hle u))
    have h2 := hin v (hmem v hv) (lt_of_lt_of_le hv (hle v))
    exact h1.symm.trans h2
  · by_cases hzs : z = s
    · exact Or.inl hzs
    · by_cases hzx : z = x
      · exact Or.inr hzx
      · exfalso
        have hz' : (N.sub (N.inside S)).deg (fun _ => 1) z = 2 := hz
        rcases hother z hzs hzx with h | h <;> omega

/-! ### The step -/

/-- **The two sides of a bridge of a pole.** Let `N` be a pole with the two ports `s`, `t` and at
least `0.501 · 2^b` paths from `s` to `t`, and let no cycle take the edge `e`. Then some cut `S`
has `e` as its only crossing edge, with `s ∈ S` and `t ∉ S`, the edge `e` joins `x ∈ S` and
`y ∉ S`, and the two sides are poles with the two ports `s`, `x` and `y`, `t`. -/
theorem exists_bridge_split (N : Network V E) {s t : V} (hN : N.IsWeakTwoPole s t)
    (hmany : 501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t) {e : E}
    (hbr : ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0) :
    ∃ (S : V → Prop) (x y : V), N.Joins e x y ∧ S x ∧ ¬ S y ∧
      (∀ g, N.crosses S g → g = e) ∧ S s ∧ ¬ S t ∧
      (N.sub (N.inside S)).IsWeakTwoPole s x ∧ (N.sub (N.outside S)).IsWeakTwoPole y t := by
  have hpos : 0 < 2 ^ networkRank N := Nat.two_pow_pos _
  have hdeg := hN.pole.deg_zero_or_two_le
  have hone : (fun _ : E => (1 : Bit)) e ≠ 0 := one_ne_zero
  have hspos : 0 < N.deg (fun _ => 1) s := by
    have h : N.deg (fun _ => 1) s = 2 := hN.port_s
    omega
  have htpos : 0 < N.deg (fun _ => 1) t := by
    have h : N.deg (fun _ => 1) t = 2 := hN.port_t
    omega
  -- the cut
  obtain ⟨S, hSdef⟩ : ∃ S : V → Prop, S = N.sideOf e s := ⟨_, rfl⟩
  have hS : ∀ v, S v ↔ N.sideOf e s v := fun v => by rw [hSdef]
  have hC : ∀ g, N.crosses S g → g = e := by
    intro g hg
    rw [hSdef] at hg
    exact N.eq_of_crosses_sideOf e s hg
  have hSs : S s := (hS s).2 (N.sideOf_self e s)
  -- exactly one end of `e` is in `S`
  have hends : ∃ x y : V, N.Joins e x y ∧ S x ∧ ¬ S y := by
    have he0 : N.Joins e (N.src e) (N.dst e) := Or.inl ⟨rfl, rfl⟩
    have hnot : ¬ (S (N.src e) ∧ S (N.dst e)) := by
      rintro ⟨h1, h2⟩
      exact N.not_reachable_of_bridge hbr he0 (((hS _).1 h1).symm.trans ((hS _).1 h2))
    by_cases h1 : S (N.src e)
    · exact ⟨N.src e, N.dst e, he0, h1, fun h2 => hnot ⟨h1, h2⟩⟩
    · by_cases h2 : S (N.dst e)
      · exact ⟨N.dst e, N.src e, he0.symm, h2, h1⟩
      · exfalso
        -- no edge leaves `S`, but the first end of `e` is joined to `s`
        have hclosed : ∀ g, S (N.src g) ↔ S (N.dst g) := by
          intro g
          by_cases hg : g = e
          · rw [hg]
            exact ⟨fun k => absurd k h1, fun k => absurd k h2⟩
          · rw [hS, hS]
            exact N.sideOf_iff_of_ne e s hg
        have hr : N.graph.Reachable s (N.src e) :=
          hN.pole.2 s (N.src e) hspos (N.deg_src_pos hone)
        exact h1 (N.mem_of_reachable_of_closed S hclosed hr hSs)
  obtain ⟨x, y, he, hx, hy⟩ := hends
  -- the vertex `t` is on the other side
  have hSt : ¬ S t := by
    intro hSt
    have h1 := N.two_mul_numPaths_le_of_same_side hdeg S he hx hy hC hSs hSt
    omega
  -- the complement
  have hnn : ∀ v, S v → ¬ ¬ S v := fun v h h' => h' h
  have hC' : ∀ g, N.crosses (fun v => ¬ S v) g → g = e :=
    fun g hg => hC g ((N.crosses_not_iff S g).1 hg)
  -- the bridge is not at a port
  have hxs : x ≠ s := by
    intro h
    have h1 := N.two_mul_numPaths_le_of_bridge_at hdeg S (h ▸ he) hSs hy hC
      (le_of_eq hN.port_s) hSt
    omega
  have hyt : y ≠ t := by
    intro h
    have h1 := N.two_mul_numPaths_le_of_bridge_at hdeg (fun v => ¬ S v) (h ▸ he.symm) hSt
      (hnn x hx) hC' (le_of_eq hN.port_t) (hnn s hSs)
    rw [ExactMaximum.numPaths_symm N t s] at h1
    omega
  -- connections in the two sides
  have hin : ∀ v, S v → 0 < N.deg (fun _ => 1) v →
      (N.sub (N.inside S)).graph.Reachable s v := by
    intro v hv _
    have h := N.reachable_inside_sideOf e s ((hS v).1 hv)
    rw [← hSdef] at h
    exact h
  have houtside : ∀ g, N.inside (N.sideOf e y) g → N.inside (fun v => ¬ S v) g := by
    intro g hg
    have hno : ∀ v, N.sideOf e y v → ¬ S v := by
      intro v hv hSv
      exact hy ((hS y).2 (((hS v).1 hSv).trans hv.symm))
    exact ⟨hno _ hg.1, hno _ hg.2⟩
  have hout_y : ∀ v, ¬ S v → 0 < N.deg (fun _ => 1) v →
      (N.sub (N.inside fun v => ¬ S v)).graph.Reachable y v := by
    intro v hv hvpos
    have hr : N.graph.Reachable s v := hN.pole.2 s v hspos hvpos
    rcases N.sideOf_or_sideOf he s ((hS x).1 hx) hr with h | h
    · exact absurd ((hS v).2 h) hv
    · exact N.reachable_sub_mono houtside (N.reachable_inside_sideOf e y h)
  have hout : ∀ v, ¬ S v → 0 < N.deg (fun _ => 1) v →
      (N.sub (N.inside fun v => ¬ S v)).graph.Reachable t v :=
    fun v hv hvpos => (hout_y t hSt htpos).symm.trans (hout_y v hv hvpos)
  have h1 := N.isWeakTwoPole_side hN S he hx hy hC hSs hSt hxs hin
  have h2 : (N.sub (N.inside fun v => ¬ S v)).IsWeakTwoPole t y :=
    N.isWeakTwoPole_side hN.symm (fun v => ¬ S v) he.symm hy (hnn x hx) hC' hSt (hnn s hSs)
      hyt hout
  exact ⟨S, x, y, he, hx, hy, hC, hSs, hSt, h1, h2.symm⟩

end Erdos1016.BoundaryTrace.Network

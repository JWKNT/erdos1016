import Erdos1016.ExactMaximum.NetCutRank

set_option autoImplicit false

/-!
# Cycles in even words, and the case of a bridge

This file proves three general facts and the first case of Proposition 6.3 of the paper "The
maximum number of cycles in a graph of large rank".

* `exists_isCycleWord_subword`: every nonzero even word contains a cycle.
* `exists_isCycleWord_of_rank_pos`, `networkRank_pos_of_numCycles_pos`: a network has a cycle if
  and only if its rank is positive.
* `mem_of_reachable_of_closed`: a set of vertices that no edge leaves contains every vertex that
  is joined to one of its vertices.
* `numCycles_le_of_bridge`: let `N` be connected, and let exactly one edge cross the cut `S`. If
  both sides contain a cycle, then `N` has at most `2^(r-1)` cycles.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Every even word contains a cycle -/

/-- The number of edges of a word. -/
def size (x : E → Bit) : ℕ := (Finset.univ.filter fun e : E => x e ≠ 0).card

omit [Fintype V] in
/-- A proper sub-word has fewer edges. -/
theorem IsSubword.size_lt {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) (hne : y ≠ x) :
    size y < size x := by
  -- some edge of `x` is not an edge of `y`
  obtain ⟨e, hxe, hye⟩ : ∃ e, x e ≠ 0 ∧ y e = 0 := by
    refine Classical.not_not.1 fun hno => hne ?_
    apply word_eq_of_support
    · intro e he
      exact h e he
    · intro e he
      exact Classical.not_not.1 fun hy => hno ⟨e, he, Classical.not_not.1 hy⟩
  apply Finset.card_lt_card
  refine ⟨fun g hg => ?_, fun hsub => ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ g, h g (Finset.mem_filter.1 hg).2⟩
  · have hmem := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ e, hxe⟩)
    exact (Finset.mem_filter.1 hmem).2 hye

/-- **Every nonzero even word contains a cycle.** -/
theorem exists_isCycleWord_subword (N : Network V E) :
    ∀ x : N.Word, N.boundary x = 0 → x ≠ 0 → ∃ y : N.Word, N.IsCycleWord y ∧ N.IsSubword y x := by
  have key : ∀ n : ℕ, ∀ x : N.Word, size x = n → N.boundary x = 0 → x ≠ 0 →
      ∃ y : N.Word, N.IsCycleWord y ∧ N.IsSubword y x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn hx0 hne
      rcases Classical.em (∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y = 0 ∨ y = x)
        with hmin | hmin
      · exact ⟨x, N.isCycleWord_of_minimal hne hx0 hmin, fun _ he => he⟩
      · -- a smaller nonzero even sub-word
        obtain ⟨y, hsub, hy0, hyne, hyx⟩ : ∃ y : N.Word, N.IsSubword y x ∧ N.boundary y = 0 ∧
            y ≠ 0 ∧ y ≠ x := by
          refine Classical.not_not.1 fun hno => hmin fun y hsub hy0 => ?_
          refine Classical.not_not.1 fun hor => hno ⟨y, hsub, hy0, ?_, ?_⟩
          · exact fun h => hor (Or.inl h)
          · exact fun h => hor (Or.inr h)
        have hlt : size y < n := by
          rw [← hn]
          exact hsub.size_lt hyx
        obtain ⟨z, hz, hzy⟩ := ih (size y) hlt y rfl hy0 hyne
        exact ⟨z, hz, fun e he => hsub e (hzy e he)⟩
  intro x hx0 hne
  exact key (size x) x rfl hx0 hne

/-- A network of positive rank has a cycle. -/
theorem exists_isCycleWord_of_rank_pos (N : Network V E) (h : 0 < networkRank N) :
    ∃ y : N.Word, N.IsCycleWord y := by
  have hcard : 1 < Fintype.card N.CycleSpace := by
    rw [cycleSpace_card_network]
    exact Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 h)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hcard
  -- one of the two elements is not zero
  obtain ⟨x, hx⟩ : ∃ x : N.CycleSpace, x ≠ 0 := by
    rcases Classical.em (a = 0) with ha | ha
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have hx0 : N.boundary x.1 = 0 := LinearMap.mem_ker.1 x.2
  have hne : x.1 ≠ 0 := fun h0 => hx (Subtype.ext h0)
  obtain ⟨y, hy, _⟩ := N.exists_isCycleWord_subword x.1 hx0 hne
  exact ⟨y, hy⟩

/-- A network with a cycle has positive rank. -/
theorem networkRank_pos_of_numCycles_pos (N : Network V E) (h : 0 < N.numCycles) :
    0 < networkRank N := by
  have h1 := N.numCycles_lt_two_pow
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, pow_zero] at h1
  omega

/-- A network of positive rank has a positive number of cycles. -/
theorem numCycles_pos_of_rank_pos (N : Network V E) (h : 0 < networkRank N) :
    0 < N.numCycles := by
  obtain ⟨y, hy⟩ := N.exists_isCycleWord_of_rank_pos h
  haveI : Nonempty {x : N.Word // N.IsCycleWord x} := ⟨⟨y, hy⟩⟩
  exact Nat.card_pos

/-! ### Sets of vertices that no edge leaves -/

omit [Fintype V] [Fintype E] in
/-- A set of vertices that no edge leaves contains every vertex that is joined to one of its
vertices. -/
theorem mem_of_reachable_of_closed (N : Network V E) (D : V → Prop)
    (hclosed : ∀ e, D (N.src e) ↔ D (N.dst e)) {u w : V} (h : N.graph.Reachable u w)
    (hu : D u) : D w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | @cons a b c hadj _ ih =>
    apply ih
    obtain ⟨e, h1 | h1⟩ := hadj
    · rw [← h1.2]
      rw [← h1.1] at hu
      exact (hclosed e).1 hu
    · rw [← h1.1]
      rw [← h1.2] at hu
      exact (hclosed e).2 hu

omit [Fintype V] [Fintype E] in
/-- **A side with one way out is connected.** Let `N` be connected, and let every crossing edge
of the cut `S` have its end in `S` joined to `s₀` by edges inside `S`. Then every vertex of `S`
is joined to `s₀` by edges inside `S`. -/
theorem reachable_inside_of_connected (N : Network V E) (S : V → Prop) {s₀ : V}
    (hN : N.graph.Connected)
    (hcross : ∀ e, N.crosses S e →
      (S (N.src e) → (N.sub (N.inside S)).graph.Reachable s₀ (N.src e)) ∧
      (S (N.dst e) → (N.sub (N.inside S)).graph.Reachable s₀ (N.dst e))) :
    ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u := by
  intro u hu
  refine Classical.not_not.1 fun hnot => ?_
  -- the vertices of `S` that are not joined to `s₀`
  have hclosed : ∀ e, (S (N.src e) ∧ ¬ (N.sub (N.inside S)).graph.Reachable s₀ (N.src e)) ↔
      (S (N.dst e) ∧ ¬ (N.sub (N.inside S)).graph.Reachable s₀ (N.dst e)) := by
    intro e
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · have hadj : (N.sub (N.inside S)).graph.Adj (N.src e) (N.dst e) :=
        ⟨⟨e, h⟩, Or.inl ⟨rfl, rfl⟩⟩
      constructor
      · rintro ⟨_, h2⟩
        exact ⟨h.2, fun hr => h2 (hr.trans hadj.symm.reachable)⟩
      · rintro ⟨_, h2⟩
        exact ⟨h.1, fun hr => h2 (hr.trans hadj.reachable)⟩
    · exact ⟨fun h1 => absurd h1.1 h.1, fun h1 => absurd h1.1 h.2⟩
    · constructor
      · rintro ⟨h1, h2⟩
        exact absurd ((hcross e h).1 h1) h2
      · rintro ⟨h1, h2⟩
        exact absurd ((hcross e h).2 h1) h2
  have hD := N.mem_of_reachable_of_closed
    (fun v => S v ∧ ¬ (N.sub (N.inside S)).graph.Reachable s₀ v) hclosed (hN.preconnected u s₀)
    ⟨hu, hnot⟩
  exact hD.2 (SimpleGraph.Reachable.refl _)

omit [Fintype V] [Fintype E] in
/-- The statement `reachable_inside_of_connected` for the other side of the cut. -/
theorem reachable_outside_of_connected (N : Network V E) (S : V → Prop) {t₀ : V}
    (hN : N.graph.Connected)
    (hcross : ∀ e, N.crosses S e →
      (¬ S (N.src e) → (N.sub (N.outside S)).graph.Reachable t₀ (N.src e)) ∧
      (¬ S (N.dst e) → (N.sub (N.outside S)).graph.Reachable t₀ (N.dst e))) :
    ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t₀ u := by
  intro u hu
  refine Classical.not_not.1 fun hnot => ?_
  have hclosed : ∀ e, (¬ S (N.src e) ∧ ¬ (N.sub (N.outside S)).graph.Reachable t₀ (N.src e)) ↔
      (¬ S (N.dst e) ∧ ¬ (N.sub (N.outside S)).graph.Reachable t₀ (N.dst e)) := by
    intro e
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · exact ⟨fun h1 => absurd h.1 h1.1, fun h1 => absurd h.2 h1.1⟩
    · have hadj : (N.sub (N.outside S)).graph.Adj (N.src e) (N.dst e) :=
        ⟨⟨e, h⟩, Or.inl ⟨rfl, rfl⟩⟩
      constructor
      · rintro ⟨_, h2⟩
        exact ⟨h.2, fun hr => h2 (hr.trans hadj.symm.reachable)⟩
      · rintro ⟨_, h2⟩
        exact ⟨h.1, fun hr => h2 (hr.trans hadj.reachable)⟩
    · constructor
      · rintro ⟨h1, h2⟩
        exact absurd ((hcross e h).1 h1) h2
      · rintro ⟨h1, h2⟩
        exact absurd ((hcross e h).2 h1) h2
  have hD := N.mem_of_reachable_of_closed
    (fun v => ¬ S v ∧ ¬ (N.sub (N.outside S)).graph.Reachable t₀ v) hclosed
    (hN.preconnected u t₀) ⟨hu, hnot⟩
  exact hD.2 (SimpleGraph.Reachable.refl _)

/-! ### A bridge -/

/-- For `a, b ≥ 1`: `2^a + 2^b ≤ 2^(a+b-1) + 2`. -/
theorem two_pow_add_two_pow_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 ^ a + 2 ^ b ≤ 2 ^ (a + b - 1) + 2 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have e1 : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
  rw [e1]
  have hA : 1 ≤ 2 ^ a' := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ b' := Nat.one_le_two_pow
  have e2 : 2 ^ (a' + 1) = 2 * 2 ^ a' := by ring
  have e3 : 2 ^ (b' + 1) = 2 * 2 ^ b' := by ring
  have e4 : 2 ^ (a' + b' + 1) = 2 * (2 ^ a' * 2 ^ b') := by ring
  rw [e2, e3, e4]
  nlinarith [Nat.mul_le_mul hA hB, Nat.zero_le ((2 ^ a' - 1) * (2 ^ b' - 1)),
    Nat.sub_add_cancel hA, Nat.sub_add_cancel hB]

/-- **Proposition 6.3 of the paper, the case of a bridge.** Let `N` be a connected network of
rank `r`, and let the edge `e`, which joins `s ∈ S` and `t ∉ S`, be the only edge that crosses
the cut `S`. If both sides contain a cycle, then `N` has at most `2^(r-1)` cycles. -/
theorem numCycles_le_of_bridge (N : Network V E) (S : V → Prop) {e : E} {s t : V}
    (hN : N.graph.Connected) (he : N.Joins e s t) (hs : S s) (ht : ¬ S t)
    (hC : ∀ g, N.crosses S g → g = e) (h1 : 0 < (N.sub (N.inside S)).numCycles)
    (h2 : 0 < (N.sub (N.outside S)).numCycles) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) := by
  -- the ends of the crossing edge
  have hends : ∀ g, N.crosses S g → (S (N.src g) → N.src g = s) ∧ (S (N.dst g) → N.dst g = s) ∧
      (¬ S (N.src g) → N.src g = t) ∧ (¬ S (N.dst g) → N.dst g = t) := by
    intro g hg
    rw [hC g hg]
    rcases he with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [k1, k2]
      exact ⟨fun _ => rfl, fun h => absurd h ht, fun h => absurd hs h, fun _ => rfl⟩
    · rw [k1, k2]
      exact ⟨fun h => absurd h ht, fun _ => rfl, fun _ => rfl, fun h => absurd hs h⟩
  -- both sides are connected
  have hin : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s u := by
    apply N.reachable_inside_of_connected S hN
    intro g hg
    obtain ⟨k1, k2, _, _⟩ := hends g hg
    exact ⟨fun h => by rw [k1 h], fun h => by rw [k2 h]⟩
  have hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t u := by
    apply N.reachable_outside_of_connected S hN
    intro g hg
    obtain ⟨_, _, k3, k4⟩ := hends g hg
    exact ⟨fun h => by rw [k3 h], fun h => by rw [k4 h]⟩
  -- the rank
  have hrank := N.networkRank_add_one_of_cut S hs ht hN hin hout
  have hcard : Nat.card {g : E // N.crosses S g} = 1 := by
    haveI : Nonempty {g : E // N.crosses S g} := ⟨⟨e, N.crosses_of_joins he hs ht⟩⟩
    haveI : Subsingleton {g : E // N.crosses S g} :=
      ⟨fun a b => Subtype.ext ((hC a.1 a.2).trans (hC b.1 b.2).symm)⟩
    exact Nat.card_unique
  rw [hcard] at hrank
  -- the count
  have hcount := N.numCycles_of_one_crossing S hC
  have hb1 := networkRank_pos_of_numCycles_pos _ h1
  have hb2 := networkRank_pos_of_numCycles_pos _ h2
  have hc1 := (N.sub (N.inside S)).numCycles_lt_two_pow
  have hc2 := (N.sub (N.outside S)).numCycles_lt_two_pow
  have hpow := two_pow_add_two_pow_le hb1 hb2
  have hr : networkRank N - 1 =
      networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) - 1 := by
    omega
  rw [hr, hcount]
  omega

end Erdos1016.BoundaryTrace.Network

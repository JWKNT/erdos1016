import Erdos1016.ExactMaximum.TwoCut
import Erdos1016.ExactMaximum.NetJoin

set_option autoImplicit false

/-!
# The third pair of ports of a side

Lemma 5.7 (b) of the paper "The maximum number of cycles in a graph of large rank" says: if a pole
of rank `h` has ports `a, b, c` and `P_ac + P_bc ≥ 1.002 · 2^h`, then `P_ab ≤ κ(h) 2^h`. The proof
adds a new vertex that is joined to `a` and `b`, and applies Theorem 5.4 to the new pole.

This file proves the statement for a side `T` of a cut `S` of a network `N`, with `a = s₁` and
`b = s₂` the ends of two crossing edges `e₁`, `e₂` (`third_pair`). The new pole is a part of `N`:
the side `T`, the edges `e₁` and `e₂`, and a path `Q` of the other side between the other ends
`t₁`, `t₂` of the two edges. This part is the pole of the paper with the new vertex replaced by a
path, which does not change the numbers of paths and cycles. Its rank is at most `h + 1`
(`Hook.networkRank_part_le`).

The file also proves that every join contains a path (`exists_isPathWord_subword`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance thirdPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Every join contains a path -/

/-- **Every join contains a path.** A word with odd degree exactly at `s` and `t` has a sub-word
that is a path from `s` to `t`. -/
theorem exists_isPathWord_subword (N : Network V E) {s t : V} (hst : s ≠ t) :
    ∀ y : N.Word, N.boundary y = N.pathDemand s t →
      ∃ P : N.Word, N.IsPathWord s t P ∧ N.IsSubword P y := by
  have key : ∀ n : ℕ, ∀ y : N.Word, size y = n → N.boundary y = N.pathDemand s t →
      ∃ P : N.Word, N.IsPathWord s t P ∧ N.IsSubword P y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hn hy
      rcases Classical.em (∀ z : N.Word, N.IsSubword z y → N.boundary z = 0 → z = 0)
        with hmin | hmin
      · exact ⟨y, N.isPathWord_of_minimal hst hy hmin, fun _ he => he⟩
      · obtain ⟨z, hz, hz0, hzne⟩ : ∃ z : N.Word, N.IsSubword z y ∧ N.boundary z = 0 ∧
            z ≠ 0 := by
          refine Classical.not_not.1 fun hno => hmin fun z hz hz0 => ?_
          exact Classical.not_not.1 fun hne => hno ⟨z, hz, hz0, hne⟩
        have hsub : N.IsSubword (y + z) y := IsSubword.add_self hz
        have hne : y + z ≠ y := by
          intro h
          apply hzne
          have h' : y + z = y + 0 := by rw [h, add_zero]
          exact add_left_cancel h'
        have hb : N.boundary (y + z) = N.pathDemand s t := by
          rw [map_add, hy, hz0, add_zero]
        have hlt : size (y + z) < n := by
          rw [← hn]
          exact hsub.size_lt hne
        obtain ⟨P, hP, hPy⟩ := ih (size (y + z)) hlt (y + z) rfl hb
        exact ⟨P, hP, fun e he => hsub e (hPy e he)⟩
  intro y hy
  exact key (size y) y rfl hy

/-- If two vertices are joined in the part of the network on a set of edges, some path within
this set joins them. -/
theorem exists_isPathWord_of_reachable (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    {s t : V} (hst : s ≠ t) (h : (N.sub p).graph.Reachable s t) :
    ∃ P : N.Word, N.IsPathWord s t P ∧ Within P p := by
  obtain ⟨w⟩ := h
  obtain ⟨y', hy'⟩ := (N.sub p).pair_mem_range_of_walk w
  have hy : N.boundary (extend p y') = N.pathDemand s t := by
    rw [boundary_extend]
    exact hy'
  obtain ⟨P, hP, hPy⟩ := N.exists_isPathWord_subword hst (extend p y') hy
  exact ⟨P, hP, fun e he => prop_of_extend_ne_zero p y' (hPy e he)⟩

/-! ### Even words within a set of edges -/

/-- The number of even words within a set of edges is two to the rank of the part. -/
theorem natCard_even_within (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}] :
    Nat.card {y : N.Word // N.boundary y = 0 ∧ Within y p} = 2 ^ networkRank (N.sub p) := by
  let f : (N.sub p).CycleSpace → {y : N.Word // N.boundary y = 0 ∧ Within y p} := fun x =>
    ⟨extend p x.1, by rw [boundary_extend]; exact LinearMap.mem_ker.1 x.2, within_extend p x.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      exact Subtype.ext (extend_injective p h')
    · rintro ⟨y, hy, hw⟩
      refine ⟨⟨pull p y, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, ← boundary_extend, extend_pull p hw]
        exact hy
      · exact Subtype.ext (extend_pull p hw)
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, cycleSpace_card_network]

/-! ### The side with two crossing edges and a path of the other side -/

/-- Two crossing edges of a cut, and a path of the second side between their ends. -/
structure Hook (N : Network V E) (S : V → Prop) (e₁ e₂ : E) (s₁ s₂ t₁ t₂ : V) (Q : N.Word) :
    Prop where
  he₁ : N.Joins e₁ s₁ t₁
  he₂ : N.Joins e₂ s₂ t₂
  hs₁ : S s₁
  hs₂ : S s₂
  ht₁ : ¬ S t₁
  ht₂ : ¬ S t₂
  hs : s₁ ≠ s₂
  ht : t₁ ≠ t₂
  hQ : N.IsPathWord t₁ t₂ Q
  hQout : Within Q (N.outside S)

namespace Hook

variable {N : Network V E} {S : V → Prop} {e₁ e₂ : E} {s₁ s₂ t₁ t₂ : V} {Q : N.Word}

/-- The edges of the first side, the two crossing edges, and the edges of the path. -/
def part (_h : Hook N S e₁ e₂ s₁ s₂ t₁ t₂ Q) (e : E) : Prop :=
  N.inside S e ∨ e = e₁ ∨ e = e₂ ∨ Q e ≠ 0

variable (h : Hook N S e₁ e₂ s₁ s₂ t₁ t₂ Q)
include h

omit [Fintype V] in
theorem ce₁ : N.crosses S e₁ := N.crosses_of_joins h.he₁ h.hs₁ h.ht₁

omit [Fintype V] in
theorem ce₂ : N.crosses S e₂ := N.crosses_of_joins h.he₂ h.hs₂ h.ht₂

omit [Fintype V] in
theorem e_ne : e₁ ≠ e₂ := N.ne_of_joins h.he₁ h.hs₁ h.ht₁ h.he₂ h.hs₂ h.ht₂ h.hs

omit [Fintype V] in
theorem Q_cross {g : E} (hg : N.crosses S g) : Q g = 0 :=
  h.hQout.eq_zero (N.not_outside_of_crosses hg)

omit [Fintype V] in
theorem Q_inside {g : E} (hg : N.inside S g) : Q g = 0 :=
  h.hQout.eq_zero (fun ho => N.not_outside_of_inside hg ho)

omit [Fintype V] in
/-- A crossing edge of the part is one of the two edges. -/
theorem part_crosses {g : E} (hp : h.part g) (hc : N.crosses S g) : g = e₁ ∨ g = e₂ := by
  rcases hp with hp | hp | hp | hp
  · exact absurd hc (N.not_crosses_of_inside hp)
  · exact Or.inl hp
  · exact Or.inr hp
  · exact absurd (h.Q_cross hc) hp

omit [Fintype V] in
/-- An edge of the part in the second side is an edge of the path. -/
theorem part_outside {g : E} (hp : h.part g) (ho : N.outside S g) : Q g ≠ 0 := by
  rcases hp with hp | hp | hp | hp
  · exact absurd ho (N.not_outside_of_inside hp)
  · exact absurd (hp ▸ h.ce₁) (N.not_crosses_of_outside ho)
  · exact absurd (hp ▸ h.ce₂) (N.not_crosses_of_outside ho)
  · exact hp

omit [Fintype V] in
theorem within_part_of_inside {x : E → Bit} (hx : Within x (N.inside S)) : Within x h.part :=
  fun e he => Or.inl (hx e he)

omit [Fintype V] in
theorem within_part_Q : Within Q h.part := fun _ he => Or.inr (Or.inr (Or.inr he))

omit [Fintype V] in
theorem within_part_e₁ : Within (unitWord e₁ : E → Bit) h.part :=
  within_unitWord (Or.inr (Or.inl rfl))

omit [Fintype V] in
theorem within_part_e₂ : Within (unitWord e₂ : E → Bit) h.part :=
  within_unitWord (Or.inr (Or.inr (Or.inl rfl)))

/-- **An even word of the part without the edge `e₁` lies in the first side.** -/
theorem within_inside_of_even {y : N.Word} (hy0 : N.boundary y = 0) (hw : Within y h.part)
    (hye : y e₁ = 0) : Within y (N.inside S) := by
  -- by parity, `y` does not use `e₂`
  have hyother : ∀ g, N.crosses S g → g ≠ e₁ → g ≠ e₂ → y g = 0 := by
    intro g hg k1 k2
    refine Classical.not_not.1 fun hne => ?_
    rcases h.part_crosses (hw g hne) hg with k | k
    · exact k1 k
    · exact k2 k
  have hsum : (∑ g, if N.crosses S g then y g else 0) = y e₁ + y e₂ := by
    rw [Finset.sum_eq_add e₁ e₂ h.e_ne]
    · rw [if_pos h.ce₁, if_pos h.ce₂]
    · intro g _ hg
      by_cases hc : N.crosses S g
      · rw [if_pos hc]
        exact hyother g hc hg.1 hg.2
      · rw [if_neg hc]
    · intro k
      exact absurd (Finset.mem_univ e₁) k
    · intro k
      exact absurd (Finset.mem_univ e₂) k
  have hpar : y e₁ + y e₂ = 0 := by
    rw [← hsum, ← N.cut_parity S y, hy0]
    simp
  have hye₂ : y e₂ = 0 := by
    rw [hye, zero_add] at hpar
    exact hpar
  have hnc : ∀ g, y g ≠ 0 → ¬ N.crosses S g := by
    intro g hg hc
    by_cases k1 : g = e₁
    · exact hg (k1 ▸ hye)
    · by_cases k2 : g = e₂
      · exact hg (k2 ▸ hye₂)
      · exact hg (hyother g hc k1 k2)
  -- the part of `y` outside `S` is an even sub-word of the path
  have hclosed : ∀ g, y g ≠ 0 → ¬ False → ¬ False → (¬ S (N.src g) ↔ ¬ S (N.dst g)) :=
    fun g hg _ _ => not_congr (Classical.not_not.1 (hnc g hg))
  have hz : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) = 0 := by
    apply h.hQ.minimal
    · intro g hg
      obtain ⟨hor, hyg⟩ := (restrict_ne_zero_iff y _ g).1 hg
      have hiff := hclosed g hyg (fun k => k) (fun k => k)
      have hout : N.outside S g := by
        rcases hor with k | k
        · exact ⟨k, hiff.1 k⟩
        · exact ⟨hiff.2 k, k⟩
      exact h.part_outside (hw g hyg) hout
    · funext w
      rw [N.boundary_restrict_of_closed y (fun v => ¬ S v) (fun _ => False)
        (fun _ k => k.elim) hclosed (fun k => k), hy0]
      simp
  intro g hg
  have hnot : ¬ (¬ S (N.src g) ∨ ¬ S (N.dst g)) := by
    intro hor
    have k : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) g ≠ 0 :=
      (restrict_ne_zero_iff y _ g).2 ⟨hor, hg⟩
    exact k (congrFun hz g)
  exact ⟨Classical.not_not.1 fun k => hnot (Or.inl k),
    Classical.not_not.1 fun k => hnot (Or.inr k)⟩

/-- **The rank of the part** is at most the rank of the first side plus one. -/
theorem networkRank_part_le :
    networkRank (N.sub h.part) ≤ networkRank (N.sub (N.inside S)) + 1 := by
  -- the even words of the part, by their value at `e₁`
  have h0 : Nat.card {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0} ≤
      Nat.card {y : N.Word // N.boundary y = 0 ∧ Within y (N.inside S)} := by
    apply Nat.card_le_card_of_injective
      (fun y : {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0} =>
        (⟨y.1, y.2.1.1, h.within_inside_of_even y.2.1.1 y.2.1.2 y.2.2⟩ :
          {y : N.Word // N.boundary y = 0 ∧ Within y (N.inside S)}))
    intro a b hab
    have k := congrArg Subtype.val hab
    exact Subtype.ext k
  have h1 : Nat.card {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0} ≤
      Nat.card {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0} := by
    by_cases hne : Nonempty {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0}
    · obtain ⟨w⟩ := hne
      have hw1 : w.1 e₁ = 1 := bit_eq_one_of_ne_zero w.2.2
      apply Nat.card_le_card_of_injective
        (fun y : {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0} =>
          (⟨y.1 + w.1, ⟨by rw [map_add, y.2.1.1, w.2.1.1, add_zero],
            y.2.1.2.add w.2.1.2⟩, by
              show y.1 e₁ + w.1 e₁ = 0
              rw [bit_eq_one_of_ne_zero y.2.2, hw1]
              exact bit_add_self 1⟩ :
            {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0}))
      intro a b hab
      have k := congrArg Subtype.val hab
      exact Subtype.ext (add_right_cancel k)
    · have hz : Nat.card
          {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0} = 0 := by
        rw [Nat.card_eq_zero]
        exact Or.inl (not_nonempty_iff.mp hne)
      rw [hz]
      exact Nat.zero_le _
  have hsplit : Nat.card {y : N.Word // N.boundary y = 0 ∧ Within y h.part} =
      Nat.card {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0} +
      Nat.card {y : N.Word // (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0} := by
    rw [← natCard_or_of_disjoint
      (fun y : N.Word => (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ = 0)
      (fun y : N.Word => (N.boundary y = 0 ∧ Within y h.part) ∧ y e₁ ≠ 0)
      (fun y k1 k2 => k2.2 k1.2)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro y
    constructor
    · intro k
      rcases Classical.em (y e₁ = 0) with k' | k'
      · exact Or.inl ⟨k, k'⟩
      · exact Or.inr ⟨k, k'⟩
    · rintro (k | k)
      · exact k.1
      · exact k.1
  have hA := N.natCard_even_within h.part
  have hB := N.natCard_even_within (N.inside S)
  have hpow : 2 ^ networkRank (N.sub h.part) ≤ 2 ^ (networkRank (N.sub (N.inside S)) + 1) := by
    rw [pow_succ, ← hA, ← hB]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hpow

/-! ### Paths and cycles of the part -/

omit [Fintype V] h in
/-- A word in the first side has no vertex outside `S`. -/
theorem deg_inside_word {x : N.Word} (hx : Within x (N.inside S)) {v : V} (hv : ¬ S v) :
    N.deg x v = 0 := by
  rcases Nat.eq_zero_or_pos (N.deg x v) with k | k
  · exact k
  · exact absurd (N.mem_of_within_inside hx k) hv

omit [Fintype V] in
/-- The path `Q` has no vertex in `S`. -/
theorem deg_Q {v : V} (hv : S v) : N.deg Q v = 0 := by
  rcases Nat.eq_zero_or_pos (N.deg Q v) with k | k
  · exact k
  · exact absurd hv (N.not_mem_of_within_outside h.hQout k)

/-- **Paths of the part.** A path of the first side from `s₁` to `s₃` and the edge `e₁` form a
path from `t₁` to `s₃`. A path of the first side from `s₂` to `s₃`, the edge `e₂` and the path
`Q` form another one. -/
theorem numPaths_part_ge (s₃ : V) :
    (N.sub (N.inside S)).numPaths s₁ s₃ + (N.sub (N.inside S)).numPaths s₂ s₃ ≤
      (N.sub h.part).numPaths t₁ s₃ := by
  rw [numPaths_sub, numPaths_sub, numPaths_sub]
  obtain ⟨f₁, hf₁⟩ : ∃ f : {x : N.Word // N.IsPathWord s₁ s₃ x ∧ Within x (N.inside S)} →
      {x : N.Word // N.IsPathWord t₁ s₃ x ∧ Within x h.part},
      ∀ a, (f a).1 = a.1 + unitWord e₁ :=
    ⟨fun a => ⟨a.1 + unitWord e₁,
      (a.2.1.symm.add_pendant h.he₁ (deg_inside_word a.2.2 h.ht₁)).symm,
      (h.within_part_of_inside a.2.2).add h.within_part_e₁⟩, fun _ => rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : {x : N.Word // N.IsPathWord s₂ s₃ x ∧ Within x (N.inside S)} →
      {x : N.Word // N.IsPathWord t₁ s₃ x ∧ Within x h.part},
      ∀ a, (f a).1 = Q + a.1 + unitWord e₂ :=
    ⟨fun a => ⟨Q + a.1 + unitWord e₂,
      h.hQ.glue a.2.1 h.he₂.symm (N.vertexDisjoint_of_within a.2.2 h.hQout).symm,
      (h.within_part_Q.add (h.within_part_of_inside a.2.2)).add h.within_part_e₂⟩,
      fun _ => rfl⟩
  rw [← Nat.card_sum]
  apply Nat.card_le_card_of_injective (Sum.elim f₁ f₂)
  have hval₁ : ∀ a, (f₁ a).1 e₁ = 1 := by
    intro a
    rw [hf₁]
    show a.1 e₁ + unitWord e₁ e₁ = 1
    rw [a.2.2.eq_zero (N.not_inside_of_crosses h.ce₁), unitWord_apply, if_pos rfl, zero_add]
  have hval₂ : ∀ a, (f₂ a).1 e₁ = 0 := by
    intro a
    rw [hf₂]
    show Q e₁ + a.1 e₁ + unitWord e₂ e₁ = 0
    rw [h.Q_cross h.ce₁, a.2.2.eq_zero (N.not_inside_of_crosses h.ce₁), unitWord_apply,
      if_neg (Ne.symm h.e_ne), add_zero, add_zero]
  rintro (a | a) (b | b) hab
  · have k : (f₁ a).1 = (f₁ b).1 := congrArg Subtype.val hab
    rw [hf₁, hf₁] at k
    exact congrArg Sum.inl (Subtype.ext (add_right_cancel k))
  · exfalso
    have k : (f₁ a).1 = (f₂ b).1 := congrArg Subtype.val hab
    have k' := congrFun k e₁
    rw [hval₁, hval₂] at k'
    exact one_ne_zero k'
  · exfalso
    have k : (f₂ a).1 = (f₁ b).1 := congrArg Subtype.val hab
    have k' := congrFun k e₁
    rw [hval₁, hval₂] at k'
    exact zero_ne_one k'
  · have k : (f₂ a).1 = (f₂ b).1 := congrArg Subtype.val hab
    rw [hf₂, hf₂] at k
    exact congrArg Sum.inr (Subtype.ext (add_left_cancel (add_right_cancel k)))

/-- **Cycles of the part.** A path of the first side from `s₁` to `s₂`, the two edges and the
path `Q` form a cycle. -/
theorem numCycles_part_ge :
    (N.sub (N.inside S)).numPaths s₁ s₂ ≤ (N.sub h.part).numCycles := by
  rw [numPaths_sub, numCycles_sub]
  apply Nat.card_le_card_of_injective
    (fun a : {x : N.Word // N.IsPathWord s₁ s₂ x ∧ Within x (N.inside S)} =>
      (⟨a.1 + Q + (unitWord e₁ + unitWord e₂),
        a.2.1.glue_cycle h.hQ h.he₁ h.he₂ (N.vertexDisjoint_of_within a.2.2 h.hQout),
        ((h.within_part_of_inside a.2.2).add h.within_part_Q).add
          (h.within_part_e₁.add h.within_part_e₂)⟩ :
        {x : N.Word // N.IsCycleWord x ∧ Within x h.part}))
  intro a b hab
  have k := congrArg Subtype.val hab
  exact Subtype.ext (add_right_cancel (add_right_cancel k))

/-! ### The part is a pole -/

omit [Fintype V] in
/-- The edges of the part are the edges of the first side, of the path, and the two edges. -/
theorem restrict_part :
    restrict (fun _ => (1 : Bit)) h.part =
      restrict (fun _ => (1 : Bit)) (N.inside S) + Q + unitWord e₁ + unitWord e₂ := by
  funext g
  show restrict (fun _ => (1 : Bit)) h.part g =
    restrict (fun _ => (1 : Bit)) (N.inside S) g + Q g + unitWord e₁ g + unitWord e₂ g
  rw [unitWord_apply, unitWord_apply]
  by_cases hi : N.inside S g
  · have k1 : e₁ ≠ g := fun k => N.not_crosses_of_inside hi (k ▸ h.ce₁)
    have k2 : e₂ ≠ g := fun k => N.not_crosses_of_inside hi (k ▸ h.ce₂)
    have hp : h.part g := Or.inl hi
    rw [restrict_apply_of_pos (p := h.part) _ hp, restrict_apply_of_pos _ hi,
      h.Q_inside hi, if_neg k1, if_neg k2, add_zero, add_zero, add_zero]
  · rw [restrict_apply_of_neg _ hi, zero_add]
    by_cases k1 : e₁ = g
    · have k2 : e₂ ≠ g := fun k => h.e_ne (k1.trans k.symm)
      have hp : h.part g := Or.inr (Or.inl k1.symm)
      rw [restrict_apply_of_pos (p := h.part) _ hp, if_pos k1, if_neg k2,
        ← k1, h.Q_cross h.ce₁, zero_add, add_zero]
    · by_cases k2 : e₂ = g
      · have hp : h.part g := Or.inr (Or.inr (Or.inl k2.symm))
        rw [restrict_apply_of_pos (p := h.part) _ hp, if_neg k1,
          if_pos k2, ← k2, h.Q_cross h.ce₂, zero_add, zero_add]
      · rw [if_neg k1, if_neg k2, add_zero, add_zero]
        by_cases kQ : Q g = 0
        · have hnp : ¬ h.part g := by
            rintro (k | k | k | k)
            · exact hi k
            · exact k1 k.symm
            · exact k2 k.symm
            · exact k kQ
          rw [restrict_apply_of_neg _ hnp, kQ]
        · have hp : h.part g := Or.inr (Or.inr (Or.inr kQ))
          rw [restrict_apply_of_pos (p := h.part) _ hp, bit_eq_one_of_ne_zero kQ]

omit [Fintype V] in
/-- **The degrees of the part.** -/
theorem deg_part (v : V) :
    (N.sub h.part).deg (fun _ => 1) v =
      (N.sub (N.inside S)).deg (fun _ => 1) v + N.deg Q v + N.deg (unitWord e₁) v +
        N.deg (unitWord e₂) v := by
  rw [N.deg_sub_ones h.part v, N.deg_sub_ones (N.inside S) v, h.restrict_part]
  have d1 : ∀ g, restrict (fun _ => (1 : Bit)) (N.inside S) g ≠ 0 → Q g = 0 :=
    fun g hg => h.Q_inside ((restrict_ne_zero_iff _ _ g).1 hg).1
  have d2 : ∀ g, (restrict (fun _ => (1 : Bit)) (N.inside S) + Q) g ≠ 0 →
      (unitWord e₁ : E → Bit) g = 0 := by
    intro g hg
    rw [unitWord_apply, if_neg]
    intro k
    apply hg
    show restrict (fun _ => (1 : Bit)) (N.inside S) g + Q g = 0
    rw [← k, restrict_apply_of_neg _ (N.not_inside_of_crosses h.ce₁), h.Q_cross h.ce₁,
      add_zero]
  have d3 : ∀ g, (restrict (fun _ => (1 : Bit)) (N.inside S) + Q + unitWord e₁) g ≠ 0 →
      (unitWord e₂ : E → Bit) g = 0 := by
    intro g hg
    rw [unitWord_apply, if_neg]
    intro k
    apply hg
    show restrict (fun _ => (1 : Bit)) (N.inside S) g + Q g + unitWord e₁ g = 0
    rw [← k, restrict_apply_of_neg _ (N.not_inside_of_crosses h.ce₂), h.Q_cross h.ce₂,
      unitWord_apply, if_neg h.e_ne, add_zero, add_zero]
  rw [N.deg_add_of_disjoint d3 v, N.deg_add_of_disjoint d2 v, N.deg_add_of_disjoint d1 v]

omit [Fintype V] in
/-- The degree of a vertex of `S` in the part. -/
theorem deg_part_of_mem {v : V} (hv : S v) :
    (N.sub h.part).deg (fun _ => 1) v =
      (N.sub (N.inside S)).deg (fun _ => 1) v + (if v = s₁ then 1 else 0) +
        (if v = s₂ then 1 else 0) := by
  have k1 : N.deg (unitWord e₁) v = if v = s₁ then 1 else 0 := by
    by_cases k : v = s₁
    · rw [if_pos k, k]
      exact N.deg_unitWord_eq_one h.he₁.at_left
    · rw [if_neg k]
      exact N.deg_unitWord_of_joins h.he₁ k (fun k' => h.ht₁ (k' ▸ hv))
  have k2 : N.deg (unitWord e₂) v = if v = s₂ then 1 else 0 := by
    by_cases k : v = s₂
    · rw [if_pos k, k]
      exact N.deg_unitWord_eq_one h.he₂.at_left
    · rw [if_neg k]
      exact N.deg_unitWord_of_joins h.he₂ k (fun k' => h.ht₂ (k' ▸ hv))
  rw [h.deg_part v, h.deg_Q hv, k1, k2, add_zero]

omit [Fintype V] in
/-- The degree of a vertex outside `S` in the part. -/
theorem deg_part_of_not_mem {v : V} (hv : ¬ S v) :
    (N.sub h.part).deg (fun _ => 1) v =
      N.deg Q v + (if v = t₁ then 1 else 0) + (if v = t₂ then 1 else 0) := by
  have k0 : (N.sub (N.inside S)).deg (fun _ => 1) v = 0 := by
    rw [N.deg_sub_ones (N.inside S) v]
    exact N.deg_inside_eq_zero S hv
  have k1 : N.deg (unitWord e₁) v = if v = t₁ then 1 else 0 := by
    by_cases k : v = t₁
    · rw [if_pos k, k]
      exact N.deg_unitWord_eq_one h.he₁.at_right
    · rw [if_neg k]
      exact N.deg_unitWord_of_joins h.he₁ (fun k' => hv (k' ▸ h.hs₁)) k
  have k2 : N.deg (unitWord e₂) v = if v = t₂ then 1 else 0 := by
    by_cases k : v = t₂
    · rw [if_pos k, k]
      exact N.deg_unitWord_eq_one h.he₂.at_right
    · rw [if_neg k]
      exact N.deg_unitWord_of_joins h.he₂ (fun k' => hv (k' ▸ h.hs₂)) k
  rw [h.deg_part v, k0, k1, k2, zero_add]

omit [Fintype V] in
/-- The end `t₁` of the path is a port of the part. -/
theorem isPort_part_t₁ : (N.sub h.part).IsPort t₁ := by
  unfold IsPort
  rw [h.deg_part_of_not_mem h.ht₁, h.hQ.2.1, if_pos rfl, if_neg h.ht]

omit [Fintype V] in
/-- A port of the first side other than `s₁`, `s₂` is a port of the part. -/
theorem isPort_part_of_port {s₃ : V} (hs₃ : S s₃) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃)
    (hp₃ : (N.sub (N.inside S)).IsPort s₃) : (N.sub h.part).IsPort s₃ := by
  unfold IsPort
  rw [h.deg_part_of_mem hs₃, if_neg (Ne.symm h13), if_neg (Ne.symm h23)]
  exact hp₃

omit [Fintype V] in
/-- **The part is a pole**, if the first side is a pole in which `s₁` and `s₂` are ports and
every vertex of `S` is joined to `s₁`. -/
theorem isWeakPole_part (hT : (N.sub (N.inside S)).IsWeakPole)
    (hp₁ : (N.sub (N.inside S)).IsPort s₁) (hp₂ : (N.sub (N.inside S)).IsPort s₂)
    (hin : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₁ u) :
    (N.sub h.part).IsWeakPole := by
  have hp₁' : (N.sub (N.inside S)).deg (fun _ => 1) s₁ = 2 := hp₁
  have hp₂' : (N.sub (N.inside S)).deg (fun _ => 1) s₂ = 2 := hp₂
  constructor
  · intro v
    by_cases hv : S v
    · rw [h.deg_part_of_mem hv]
      by_cases k1 : v = s₁
      · rw [if_pos k1, if_neg (fun k2 => h.hs (k1.symm.trans k2)), k1, hp₁']
        exact Or.inr (Or.inr rfl)
      · by_cases k2 : v = s₂
        · rw [if_neg k1, if_pos k2, k2, hp₂']
          exact Or.inr (Or.inr rfl)
        · rw [if_neg k1, if_neg k2, add_zero, add_zero]
          exact hT.1 v
    · rw [h.deg_part_of_not_mem hv]
      by_cases k1 : v = t₁
      · rw [if_pos k1, if_neg (fun k2 => h.ht (k1.symm.trans k2)), k1, h.hQ.2.1]
        exact Or.inr (Or.inl rfl)
      · by_cases k2 : v = t₂
        · rw [if_neg k1, if_pos k2, k2, h.hQ.2.2.1]
          exact Or.inr (Or.inl rfl)
        · rw [if_neg k1, if_neg k2, add_zero, add_zero]
          rcases h.hQ.2.2.2.1 v k1 k2 with k | k
          · exact Or.inl k
          · exact Or.inr (Or.inl k)
  · -- every vertex of the part is joined to `s₁`
    have hmono₁ : (N.sub (N.inside S)).graph ≤ (N.sub h.part).graph := by
      rintro a b ⟨e, he⟩
      exact ⟨⟨e.1, Or.inl e.2⟩, he⟩
    have hmono₂ : N.selectedGraph Q ≤ (N.sub h.part).graph := by
      rintro a b ⟨e, hQe, he⟩
      exact ⟨⟨e, Or.inr (Or.inr (Or.inr hQe))⟩, he⟩
    have hadj : (N.sub h.part).graph.Adj s₁ t₁ := ⟨⟨e₁, Or.inr (Or.inl rfl)⟩, h.he₁⟩
    have hroot : ∀ v, 0 < (N.sub h.part).deg (fun _ => 1) v →
        (N.sub h.part).graph.Reachable s₁ v := by
      intro v hv
      by_cases hSv : S v
      · exact (hin v hSv).mono hmono₁
      · have hQv : 0 < N.deg Q v := by
          rw [h.deg_part_of_not_mem hSv] at hv
          by_cases k1 : v = t₁
          · rw [k1, h.hQ.2.1]
            exact Nat.one_pos
          · by_cases k2 : v = t₂
            · rw [k2, h.hQ.2.2.1]
              exact Nat.one_pos
            · rw [if_neg k1, if_neg k2, add_zero, add_zero] at hv
              exact hv
        exact hadj.reachable.trans ((h.hQ.2.2.2.2 v hQv).mono hmono₂)
    intro u v hu hv
    exact (hroot u hu).symm.trans (hroot v hv)

end Hook

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance thirdPairDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Lemma 5.7 (b) of the paper for a side of a cut.** Let the first side `T` of the cut `S` be a
pole of rank `b` with the ports `s₁`, `s₂`, `s₃`, where `s₁` and `s₂` are the ends of two crossing
edges whose other ends are joined by a path `Q` of the second side. If
`P(s₁,s₃) + P(s₂,s₃) ≥ 1.002 · 2^b`, then `P(s₁,s₂)² ≤ 2K 2^b`. -/
theorem third_pair {K : ℕ} (hF : FewCyclesWith K) {V E : Type} [Fintype V] [Fintype E]
    {N : Network V E} {S : V → Prop} {e₁ e₂ : E} {s₁ s₂ s₃ t₁ t₂ : V} {Q : N.Word}
    (h : Hook N S e₁ e₂ s₁ s₂ t₁ t₂ Q) (hT : (N.sub (N.inside S)).IsWeakPole)
    (hp₁ : (N.sub (N.inside S)).IsPort s₁) (hp₂ : (N.sub (N.inside S)).IsPort s₂)
    (hp₃ : (N.sub (N.inside S)).IsPort s₃) (hs₃ : S s₃) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃)
    (hin : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₁ u)
    (hmany : 1002 * 2 ^ networkRank (N.sub (N.inside S)) ≤
      1000 * ((N.sub (N.inside S)).numPaths s₁ s₃ + (N.sub (N.inside S)).numPaths s₂ s₃)) :
    (N.sub (N.inside S)).numPaths s₁ s₂ ^ 2 ≤ 2 * K * 2 ^ networkRank (N.sub (N.inside S)) := by
  have hpole := h.isWeakPole_part hT hp₁ hp₂ hin
  have hrank := h.networkRank_part_le
  have hpaths := h.numPaths_part_ge s₃
  have hcyc := h.numCycles_part_ge
  have hne : t₁ ≠ s₃ := fun k => h.ht₁ (k ▸ hs₃)
  have hpow : 2 ^ networkRank (N.sub h.part) ≤ 2 * 2 ^ networkRank (N.sub (N.inside S)) := by
    have k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hrank
    rw [pow_succ] at k
    omega
  have key := hF V {e : E // h.part e} (N.sub h.part) hpole t₁ s₃ h.isPort_part_t₁
    (h.isPort_part_of_port hs₃ h13 h23 hp₃) hne (by omega)
  calc (N.sub (N.inside S)).numPaths s₁ s₂ ^ 2 ≤ (N.sub h.part).numCycles ^ 2 :=
        Nat.pow_le_pow_left hcyc 2
    _ ≤ K * 2 ^ networkRank (N.sub h.part) := key
    _ ≤ K * (2 * 2 ^ networkRank (N.sub (N.inside S))) := Nat.mul_le_mul_left K hpow
    _ = 2 * K * 2 ^ networkRank (N.sub (N.inside S)) := by ring

end Erdos1016.ExactMaximum

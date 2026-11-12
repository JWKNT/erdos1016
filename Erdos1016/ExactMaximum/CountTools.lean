import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# Tools for the count of Theorem 5.4

The count of Theorem 5.4 of the paper "The maximum number of cycles in a graph of large rank"
shows that a cycle is determined by a few of its edges. This file has the general facts:

* there are `2^|F|` words within a set `F` of edges (`natCard_within`), so a family of words
  that are determined by their restriction to `F` has at most `2^|F|` members
  (`natCard_le_of_determined`);
* for a set of at most two words some edge separates them (`exists_separating_edge`);
* a set of numbers between `a` and `b` without two consecutive members has at most `(b - a)/2`
  members (`card_le_half_of_no_consecutive`);
* the sums `Σ_{k ≤ j} 2^⌊k/2⌋ ≤ 4 · 2^⌊j/2⌋` and `Σ_{j ≤ n} Σ_{k ≤ j} 2^⌊k/2⌋ ≤ 16 · 2^⌊n/2⌋`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance countToolsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Cardinalities -/

/-- The union bound. -/
theorem natCard_or_le {α : Type*} [Finite α] (P Q : α → Prop) :
    Nat.card {a // P a ∨ Q a} ≤ Nat.card {a // P a} + Nat.card {a // Q a} := by
  rw [← Nat.card_sum]
  obtain ⟨f, hf⟩ : ∃ f : {a // P a ∨ Q a} → {a // P a} ⊕ {a // Q a},
      ∀ x, Sum.elim Subtype.val Subtype.val (f x) = x.1 := by
    refine ⟨fun x => if h : P x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2.resolve_left h⟩,
      fun x => ?_⟩
    show Sum.elim Subtype.val Subtype.val
      (if h : P x.1 then Sum.inl ⟨x.1, h⟩ else Sum.inr ⟨x.1, x.2.resolve_left h⟩) = x.1
    by_cases h : P x.1
    · rw [dif_pos h]
      rfl
    · rw [dif_neg h]
      rfl
  apply Nat.card_le_card_of_injective f
  intro x y hxy
  apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

/-- A smaller property has fewer elements. -/
theorem natCard_le_of_imp {α : Type*} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // P a} ≤ Nat.card {a // Q a} :=
  Nat.card_le_card_of_injective (fun a => (⟨a.1, h a.1 a.2⟩ : {a // Q a})) (fun x y hab => by
    have h1 : (⟨x.1, h x.1 x.2⟩ : {a // Q a}) = ⟨y.1, h y.1 y.2⟩ := hab
    have h2 : (⟨x.1, h x.1 x.2⟩ : {a // Q a}).1 = (⟨y.1, h y.1 y.2⟩ : {a // Q a}).1 :=
      congrArg Subtype.val h1
    exact Subtype.ext h2)

/-! ### Words within a set of edges -/

/-- There are `2^|F|` words within a set `F` of edges. -/
theorem natCard_within {E : Type*} [Fintype E] (F : E → Prop) :
    Nat.card {x : E → Bit // Within x F} = 2 ^ Nat.card {e : E // F e} := by
  have hequiv : {x : E → Bit // Within x F} ≃ ({e : E // F e} → Bit) :=
    { toFun := fun x => pull F x.1
      invFun := fun y => ⟨extend F y, within_extend F y⟩
      left_inv := fun x => Subtype.ext (extend_pull F x.2)
      right_inv := fun y => pull_extend F y }
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Nat.card_eq_fintype_card]

/-- **Words that are determined by their restriction to `F`.** Their number is at most
`2^|F|`. -/
theorem natCard_le_of_determined {E : Type*} [Fintype E] (P : (E → Bit) → Prop) (F : E → Prop)
    (h : ∀ x y, P x → P y → restrict x F = restrict y F → x = y) :
    Nat.card {x // P x} ≤ 2 ^ Nat.card {e : E // F e} := by
  rw [← natCard_within F]
  exact Nat.card_le_card_of_injective
    (fun x : {x // P x} => (⟨restrict x.1 F, within_restrict x.1 F⟩ :
      {x : E → Bit // Within x F}))
    (fun x y hxy => Subtype.ext (h x.1 y.1 x.2 y.2 (congrArg Subtype.val hxy)))

/-- **A separating edge.** For a set of at most two words there is an edge at which different
words of the set have different values. -/
theorem exists_separating_edge {E : Type*} [Fintype E] [Nonempty E] (P : (E → Bit) → Prop)
    (hP : Nat.card {m // P m} ≤ 2) :
    ∃ ε : E, ∀ m m', P m → P m' → m ε = m' ε → m = m' := by
  by_cases hsub : ∀ m m', P m → P m' → m = m'
  · exact ⟨Classical.arbitrary E, fun m m' hm hm' _ => hsub m m' hm hm'⟩
  · -- two different words of the set
    obtain ⟨m₁, hsub⟩ := not_forall.1 hsub
    obtain ⟨m₂, hsub⟩ := not_forall.1 hsub
    obtain ⟨h1, hsub⟩ := Classical.not_imp.1 hsub
    obtain ⟨h2, hne⟩ := Classical.not_imp.1 hsub
    obtain ⟨ε, hε⟩ : ∃ ε, m₁ ε ≠ m₂ ε := by
      refine Classical.not_not.1 fun hno => hne ?_
      funext g
      exact Classical.not_not.1 fun h => hno ⟨g, h⟩
    -- there is no third word
    have hall : ∀ m, P m → m = m₁ ∨ m = m₂ := by
      intro m hm
      refine Classical.not_not.1 fun hno => ?_
      have hcard : ({⟨m₁, h1⟩, ⟨m₂, h2⟩, ⟨m, hm⟩} : Finset {m // P m}).card = 3 := by
        rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
          Finset.card_singleton]
        · rw [Finset.mem_singleton]
          intro k
          exact hno (Or.inr (congrArg Subtype.val k).symm)
        · rw [Finset.mem_insert, Finset.mem_singleton]
          rintro (k | k)
          · exact hne (congrArg Subtype.val k)
          · exact hno (Or.inl (congrArg Subtype.val k).symm)
      have hle := Finset.card_le_univ ({⟨m₁, h1⟩, ⟨m₂, h2⟩, ⟨m, hm⟩} : Finset {m // P m})
      rw [hcard, ← Nat.card_eq_fintype_card] at hle
      omega
    refine ⟨ε, fun m m' hm hm' heq => ?_⟩
    rcases hall m hm with k | k <;> rcases hall m' hm' with k' | k'
    · rw [k, k']
    · exfalso
      rw [k, k'] at heq
      exact hε heq
    · exfalso
      rw [k, k'] at heq
      exact hε heq.symm
    · rw [k, k']

/-! ### Sets of numbers without two consecutive members -/

/-- A set of numbers strictly between `a` and `b` without two consecutive members has at most
`(b - a) / 2` members. -/
theorem card_le_half_of_no_consecutive (A : Finset ℕ) (a b : ℕ)
    (hA : ∀ l ∈ A, a < l ∧ l < b) (hno : ∀ l ∈ A, l + 1 ∉ A) : A.card ≤ (b - a) / 2 := by
  have hmaps : ∀ l ∈ A, (l - a - 1) / 2 ∈ Finset.range ((b - a) / 2) := by
    intro l hl
    rw [Finset.mem_range]
    have := hA l hl
    omega
  have hinj : Set.InjOn (fun l : ℕ => (l - a - 1) / 2) (A : Set ℕ) := by
    intro l hl l' hl' heq
    have h1 := hA l hl
    have h2 := hA l' hl'
    have h3 := hno l hl
    have h4 := hno l' hl'
    have heq' : (l - a - 1) / 2 = (l' - a - 1) / 2 := heq
    refine Classical.not_not.1 fun hne => ?_
    have hcases : l' = l + 1 ∨ l = l' + 1 := by omega
    rcases hcases with k | k
    · exact h3 (k ▸ hl')
    · exact h4 (k ▸ hl)
  have h := Finset.card_le_card_of_injOn (fun l : ℕ => (l - a - 1) / 2) hmaps hinj
  rwa [Finset.card_range] at h

/-! ### Sums of powers of two with halved exponents -/

/-- The sum of `2^⌊k/2⌋` for `k ≤ j`. -/
def halfPowSum (j : ℕ) : ℕ := ∑ k ∈ Finset.range (j + 1), 2 ^ (k / 2)

theorem halfPowSum_succ (j : ℕ) : halfPowSum (j + 1) = halfPowSum j + 2 ^ ((j + 1) / 2) :=
  Finset.sum_range_succ _ _

/-- `Σ_{k ≤ j} 2^⌊k/2⌋ + 2 ≤ 4 · 2^⌊j/2⌋`. -/
theorem halfPowSum_add_two_le (j : ℕ) : halfPowSum j + 2 ≤ 4 * 2 ^ (j / 2) := by
  have key : ∀ j : ℕ, halfPowSum j + 2 ≤ 4 * 2 ^ (j / 2) ∧
      halfPowSum (j + 1) + 2 ≤ 4 * 2 ^ ((j + 1) / 2) := by
    intro j
    induction j with
    | zero =>
      constructor
      · show (∑ k ∈ Finset.range 1, 2 ^ (k / 2)) + 2 ≤ 4 * 2 ^ (0 / 2)
        rw [Finset.sum_range_one]
        norm_num
      · show (∑ k ∈ Finset.range 2, 2 ^ (k / 2)) + 2 ≤ 4 * 2 ^ (1 / 2)
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        norm_num
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [halfPowSum_succ, halfPowSum_succ]
      have e1 : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
      have e2 : 2 ^ ((j + 1) / 2) ≤ 2 ^ (j / 2 + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 := ih.1
      rw [e1, pow_succ] at *
      omega
  exact (key j).1

/-- `Σ_{j ≤ n} Σ_{k ≤ j} 2^⌊k/2⌋ ≤ 16 · 2^⌊n/2⌋`. -/
theorem sum_halfPowSum_le (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), halfPowSum j) ≤ 16 * 2 ^ (n / 2) := by
  have h1 : (∑ j ∈ Finset.range (n + 1), halfPowSum j) ≤
      ∑ j ∈ Finset.range (n + 1), 4 * 2 ^ (j / 2) := by
    apply Finset.sum_le_sum
    intro j _
    have := halfPowSum_add_two_le j
    omega
  have h2 : (∑ j ∈ Finset.range (n + 1), 4 * 2 ^ (j / 2)) = 4 * halfPowSum n := by
    rw [← Finset.mul_sum]
    rfl
  have h3 := halfPowSum_add_two_le n
  omega

/-- The sum of `2^⌊(j - i)/2⌋` for `i ≤ j`. -/
theorem sum_range_half_pow_sub (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), 2 ^ ((j - i) / 2)) = halfPowSum j := by
  show (∑ i ∈ Finset.range (j + 1), 2 ^ ((j - i) / 2)) =
    ∑ k ∈ Finset.range (j + 1), 2 ^ (k / 2)
  rw [← Finset.sum_range_reflect (fun k => 2 ^ (k / 2)) (j + 1)]
  apply Finset.sum_congr rfl
  intro i _
  show 2 ^ ((j - i) / 2) = 2 ^ ((j + 1 - 1 - i) / 2)
  rw [Nat.add_sub_cancel]

end Erdos1016.BoundaryTrace.Network

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Products of consecutive matching counts

Each factor is at most two, and consecutive factors sum to at most three.
Their product is bounded by one factor of two for each consecutive pair.
The interval forms keep natural subtraction and the real half exponent explicit.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.MatchingProduct

/-- Two eligible consecutive matching counts have product at most two. -/
theorem pair_product_le_two (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2)
    (hsum : a + b ≤ 3) : a * b ≤ 2 := by
  interval_cases a <;> interval_cases b <;> omega

/-- Pair consecutive factors, leaving at most one factor at the end. -/
theorem prod_range_le (a : ℕ → ℕ) (n : ℕ)
    (ha : ∀ i < n, a i ≤ 2)
    (hadj : ∀ i, i + 1 < n → a i + a (i + 1) ≤ 3) :
    (∏ i ∈ Finset.range n, a i) ≤ 2 ^ ((n + 1) / 2) := by
  have hall : ∀ n : ℕ, (∀ i < n, a i ≤ 2) →
      (∀ i, i + 1 < n → a i + a (i + 1) ≤ 3) →
      (∏ i ∈ Finset.range n, a i) ≤ 2 ^ ((n + 1) / 2) := by
    apply Nat.twoStepInduction
    · intro _ _
      simp
    · intro h _
      simpa using h 0 (by omega)
    · intro n ih _ h hnext
      have hp := pair_product_le_two (a n) (a (n + 1))
        (h n (by omega)) (h (n + 1) (by omega)) (hnext n (by omega))
      have hprior := ih (fun i hi => h i (by omega))
        (fun i hi => hnext i (by omega))
      have he : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      calc
        _ = (∏ i ∈ Finset.range n, a i) * (a n * a (n + 1)) := by
          rw [Finset.prod_range_succ,Finset.prod_range_succ,mul_assoc]
        _ ≤ 2 ^ ((n + 1) / 2) * 2 := Nat.mul_le_mul hprior hp
        _ = _ := by rw [he,pow_succ]
  exact hall n ha hadj

/-- Translation gives the same bound on any half-open interval. -/
theorem prod_Ico_le (a : ℕ → ℕ) (s t : ℕ)
    (ha : ∀ i, s ≤ i → i < t → a i ≤ 2)
    (hadj : ∀ i, s ≤ i → i + 1 < t → a i + a (i + 1) ≤ 3) :
    (∏ i ∈ Finset.Ico s t, a i) ≤ 2 ^ ((t - s + 1) / 2) := by
  rw [Finset.prod_Ico_eq_prod_range]
  apply prod_range_le (fun i => a (s + i)) (t - s)
  · intro i hi
    exact ha (s + i) (by omega) (by omega)
  · intro i hi
    simpa only [Nat.add_assoc] using hadj (s + i) (by omega) (by omega)

/-- Eligible interior interfaces occupy `i < l` and `l+1 < j`. -/
theorem prod_interior_le (a : ℕ → ℕ) (i j : ℕ)
    (ha : ∀ l, i < l → l + 1 < j → a l ≤ 2)
    (hadj : ∀ l, i < l → l + 2 < j → a l + a (l + 1) ≤ 3) :
    (∏ l ∈ Finset.Ico (i + 1) (j - 1), a l) ≤ 2 ^ ((j - i) / 2) := by
  have hp := prod_Ico_le a (i + 1) (j - 1)
    (fun l hlo hhi => ha l (by omega) (by omega))
    (fun l hlo hhi => hadj l (by omega) (by omega))
  have he : (j - 1 - (i + 1) + 1) / 2 ≤ (j - i) / 2 := by omega
  exact hp.trans (Nat.pow_le_pow_right (by omega) he)

/-- The interior product also satisfies the paper's real half-exponent bound. -/
theorem prod_interior_le_rpow (a : ℕ → ℕ) (i j : ℕ)
    (ha : ∀ l, i < l → l + 1 < j → a l ≤ 2)
    (hadj : ∀ l, i < l → l + 2 < j → a l + a (l + 1) ≤ 3) :
    (∏ l ∈ Finset.Ico (i + 1) (j - 1), (a l : ℝ)) ≤
      (2 : ℝ) ^ ((↑(j - i) : ℝ) / 2) := by
  have hp : (∏ l ∈ Finset.Ico (i + 1) (j - 1), (a l : ℝ)) ≤
      (2 : ℝ) ^ ((j - i) / 2) := by
    exact_mod_cast prod_interior_le a i j ha hadj
  have he : (↑((j - i) / 2) : ℝ) ≤ (↑(j - i) : ℝ) / 2 := by
    have hn : (j - i) / 2 * 2 ≤ j - i := Nat.div_mul_le_self _ _
    have hr : (↑((j - i) / 2) : ℝ) * 2 ≤ (↑(j - i) : ℝ) := by exact_mod_cast hn
    linarith
  apply hp.trans
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- Fill omitted positions with one before pairing consecutive factors. -/
theorem prod_filter_range_le (a : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (ha : ∀ i < n, p i → a i ≤ 2)
    (hadj : ∀ i, i + 1 < n → p i → p (i + 1) → a i + a (i + 1) ≤ 3) :
    (∏ i ∈ (Finset.range n).filter p, a i) ≤ 2 ^ ((n + 1) / 2) := by
  let b : ℕ → ℕ := fun i => if p i then a i else 1
  have hb : ∀ i < n, b i ≤ 2 := by
    intro i hi
    by_cases hp : p i
    · simpa only [b,if_pos hp] using ha i hi hp
    · simp [b,hp]
  have hnext : ∀ i, i + 1 < n → b i + b (i + 1) ≤ 3 := by
    intro i hi
    by_cases hp : p i <;> by_cases hq : p (i + 1)
    · simpa only [b,if_pos hp,if_pos hq] using hadj i hi hp hq
    · have h := ha i (by omega) hp
      simp only [b,if_pos hp,if_neg hq]
      omega
    · have h := ha (i + 1) hi hq
      simp only [b,if_neg hp,if_pos hq]
      omega
    · simp [b,hp,hq]
  simpa [b,Finset.prod_filter] using prod_range_le b n hb hnext

/-- Omitted interior interfaces contribute one to the real half-exponent bound. -/
theorem prod_filter_interior_le_rpow (a : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p]
    (i j : ℕ)
    (ha : ∀ l, i < l → l + 1 < j → p l → a l ≤ 2)
    (hadj : ∀ l, i < l → l + 2 < j → p l → p (l + 1) →
      a l + a (l + 1) ≤ 3) :
    (∏ l ∈ (Finset.Ico (i + 1) (j - 1)).filter p, (a l : ℝ)) ≤
      (2 : ℝ) ^ ((↑(j - i) : ℝ) / 2) := by
  let b : ℕ → ℕ := fun l => if p l then a l else 1
  have hb : ∀ l, i < l → l + 1 < j → b l ≤ 2 := by
    intro l hlo hhi
    by_cases hp : p l
    · simpa only [b,if_pos hp] using ha l hlo hhi hp
    · simp [b,hp]
  have hnext : ∀ l, i < l → l + 2 < j → b l + b (l + 1) ≤ 3 := by
    intro l hlo hhi
    by_cases hp : p l <;> by_cases hq : p (l + 1)
    · simpa only [b,if_pos hp,if_pos hq] using hadj l hlo hhi hp hq
    · have h := ha l hlo (by omega) hp
      simp only [b,if_pos hp,if_neg hq]
      omega
    · have h := ha (l + 1) (by omega) (by omega) hq
      simp only [b,if_neg hp,if_pos hq]
      omega
    · simp [b,hp,hq]
  simpa [b,Finset.prod_filter] using prod_interior_le_rpow b i j hb hnext

end Erdos1016.ExactMaximumSupport.MatchingProduct

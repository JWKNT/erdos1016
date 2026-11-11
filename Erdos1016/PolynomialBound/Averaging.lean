import Erdos1016.Probability.Moments.WeightedSecondMoment

set_option autoImplicit false

/-!
# The second moment with a pair kernel, and weighted averaging

The forest estimate bounds every ordinary pair moment by twice the product
of the means. The polynomial error bound needs more detail: a pair has the
factor two only if it has exactly two links. The first lemma keeps this
information in a nonnegative kernel `k`. The second lemma turns a forest
probability of at least one half into a lower bound for the total kernel
weight.

The remaining lemmas are statements about finite weighted sums. A relation
is given by a real kernel with values between zero and one, so that no
decidability instance occurs in a statement.

* `antisymm_weight_le`: an antisymmetric kernel has at most half of the total
  pair weight.
* `exists_heavy_row`: a large total pair weight gives one row with a large
  weight.
* `exists_good_row`: the combination that the chain argument uses.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PolynomialBound.Averaging

open BoundaryDecay

local instance averagingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {Ω : Type*} [Fintype Ω] {ι : Type*}

/-- An ordinary pair has moment at most `(1 + k i j) a i a j`. The exceptional
pairs in row `i` have total moment at most `η a i`. Then the second moment is
at most `μ² + ∑ k i j a i a j + (1 + η) μ`. -/
theorem weighted_sum_second_moment_le_kernel
    (s : Finset ι) (X : ι → Ω → ℝ) (a : ι → ℝ)
    (exceptional : ι → ι → Prop) (k : ι → ι → ℝ) (η : ℝ)
    (hXnonneg : ∀ i ∈ s, ∀ x, 0 ≤ X i x)
    (hXle : ∀ i ∈ s, ∀ x, X i x ≤ 1)
    (hmean : ∀ i ∈ s, average (X i) = a i)
    (hk : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ k i j)
    (hordinary : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ exceptional i j →
      average (fun x => X i x * X j x) ≤ (1 + k i j) * (a i * a j))
    (hrow : ∀ i ∈ s,
      (∑ j ∈ s, if i ≠ j ∧ exceptional i j then
        average (fun x => X i x * X j x) else 0) ≤ η * a i) :
    average (fun x => (∑ i ∈ s, X i x) ^ 2) ≤
      (∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, ∑ j ∈ s, k i j * (a i * a j)) +
        (1 + η) * (∑ i ∈ s, a i) := by
  classical
  have ha (i : ι) (hi : i ∈ s) : 0 ≤ a i := by
    rw [← hmean i hi]
    simpa only [average_zero] using
      (average_mono (f := fun _ : Ω => 0) (hXnonneg i hi))
  have hdiag (i : ι) (hi : i ∈ s) :
      average (fun x => X i x * X i x) ≤ a i := by
    rw [← hmean i hi]
    apply average_mono
    intro x
    nlinarith [hXnonneg i hi x, hXle i hi x]
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      average (fun x => X i x * X j x) ≤
        a i * a j + k i j * (a i * a j) +
          (if i ≠ j ∧ exceptional i j then
            average (fun x => X i x * X j x) else 0) +
          (if i = j then a i else 0) := by
    have hprod : 0 ≤ a i * a j := mul_nonneg (ha i hi) (ha j hj)
    have hkprod : 0 ≤ k i j * (a i * a j) := mul_nonneg (hk i hi j hj) hprod
    by_cases hij : i = j
    · have h1 : (if i ≠ j ∧ exceptional i j then
          average (fun x => X i x * X j x) else 0) = 0 := if_neg fun h => h.1 hij
      rw [h1, if_pos hij]
      have hd := hdiag i hi
      subst hij
      linarith
    · rw [if_neg hij]
      by_cases he : exceptional i j
      · rw [if_pos ⟨hij, he⟩]
        linarith
      · have h1 : (if i ≠ j ∧ exceptional i j then
            average (fun x => X i x * X j x) else 0) = 0 := if_neg fun h => he h.2
        rw [h1]
        have h := hordinary i hi j hj hij he
        linarith
  have hsum := Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun j hj => hterm i hi j hj
  have hpair : (∑ i ∈ s, ∑ j ∈ s, a i * a j) = (∑ i ∈ s, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hdiagsum : (∑ i ∈ s, ∑ j ∈ s, if i = j then a i else 0) =
      ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hrows := Finset.sum_le_sum hrow
  simp only [← Finset.mul_sum] at hrows
  rw [second_average_sum]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hpair, hdiagsum] at hsum
  linarith

/-- If a random variable is zero with probability at least one half, and its
second moment is at most `μ² + W + K μ`, then `W ≥ μ² - K μ`. -/
theorem kernel_weight_ge [Nonempty Ω] (Z : Ω → ℝ) (μ W K : ℝ)
    (hmean : average Z = μ)
    (hsecond : average (fun x => Z x ^ 2) ≤ μ ^ 2 + W + K * μ)
    (hzero : 1 / 2 ≤ Finite.density (fun x => Z x = 0)) :
    μ ^ 2 - K * μ ≤ W := by
  classical
  have hcs := mean_sq_le_second_mul_nonzero_density Z
  have hcomplement :
      Finite.density (fun x => Z x = 0) + Finite.density (fun x => Z x ≠ 0) = 1 := by
    rw [← average_indicator, ← average_indicator, ← average_add]
    convert average_const (Ω := Ω) (1 : ℝ) using 1
    congr 1
    funext x
    by_cases hx : Z x = 0 <;> simp [indicator, hx]
  have hnonneg : 0 ≤ average (fun x => Z x ^ 2) := by
    simpa only [average_zero] using
      (average_mono (f := fun _ : Ω => 0) (fun x => sq_nonneg (Z x)))
  have hhalf : Finite.density (fun x => Z x ≠ 0) ≤ 1 / 2 := by linarith
  have hle := mul_le_mul_of_nonneg_left hhalf hnonneg
  rw [hmean] at hcs
  linarith

/-- An antisymmetric kernel carries at most half of the total pair weight. -/
theorem antisymm_weight_le (s : Finset ι) (a : ι → ℝ) (f : ι → ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, f i j + f j i ≤ 1) :
    2 * (∑ i ∈ s, ∑ j ∈ s, f i j * (a i * a j)) ≤ (∑ i ∈ s, a i) ^ 2 := by
  have hswap : (∑ i ∈ s, ∑ j ∈ s, f i j * (a i * a j)) =
      ∑ i ∈ s, ∑ j ∈ s, f j i * (a i * a j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpair : (∑ i ∈ s, ∑ j ∈ s, a i * a j) = (∑ i ∈ s, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  calc
    2 * (∑ i ∈ s, ∑ j ∈ s, f i j * (a i * a j)) =
        (∑ i ∈ s, ∑ j ∈ s, f i j * (a i * a j)) +
          ∑ i ∈ s, ∑ j ∈ s, f j i * (a i * a j) := by rw [← hswap]; ring
    _ = ∑ i ∈ s, ∑ j ∈ s, (f i j + f j i) * (a i * a j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hprod : 0 ≤ a i * a j := mul_nonneg (ha i hi) (ha j hj)
      have h := mul_le_mul_of_nonneg_right (hanti i hi j hj) hprod
      linarith
    _ = _ := hpair

/-- If the pair weight of a kernel is at least `μ θ`, where `μ > 0` is the
total weight, then some row has kernel weight at least `θ`. -/
theorem exists_heavy_row (s : Finset ι) (a : ι → ℝ) (g : ι → ι → ℝ) (θ : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i)
    (htotal : (∑ i ∈ s, a i) * θ ≤ ∑ i ∈ s, ∑ j ∈ s, g i j * (a i * a j)) :
    ∃ i ∈ s, θ ≤ ∑ j ∈ s, g i j * a j := by
  by_contra hno
  push_neg at hno
  have hrow : (∑ i ∈ s, ∑ j ∈ s, g i j * (a i * a j)) =
      ∑ i ∈ s, a i * ∑ j ∈ s, g i j * a j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨k, hk, hkpos⟩ : ∃ k ∈ s, 0 < a k := by
    by_contra hnone
    push_neg at hnone
    have : (∑ i ∈ s, a i) ≤ 0 := Finset.sum_nonpos hnone
    linarith
  have hlt : (∑ i ∈ s, a i * ∑ j ∈ s, g i j * a j) < ∑ i ∈ s, a i * θ := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact mul_le_mul_of_nonneg_left (hno i hi).le (ha i hi)
    · exact ⟨k, hk, mul_lt_mul_of_pos_left (hno k hk) hkpos⟩
  rw [← Finset.sum_mul] at hlt
  rw [hrow] at htotal
  linarith

/-- **The row with heavy chain partners.** The kernel `two` has pair weight at
least `μ² - K μ`. Every pair counted by `two` is counted by `good`, by the
antisymmetric kernel `far`, or by `joined`, and each row of `joined` has
weight at most `β`. Then some row of `good` has weight at least
`μ / 2 - K - β`. -/
theorem exists_good_row (s : Finset ι) (a : ι → ℝ) (two far joined good : ι → ι → ℝ)
    (K β : ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i)
    (hpoint : ∀ i ∈ s, ∀ j ∈ s, two i j ≤ good i j + far i j + joined i j)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, far i j + far j i ≤ 1)
    (hW : (∑ i ∈ s, a i) ^ 2 - K * (∑ i ∈ s, a i) ≤
      ∑ i ∈ s, ∑ j ∈ s, two i j * (a i * a j))
    (hjoined : ∀ i ∈ s, (∑ j ∈ s, joined i j * a j) ≤ β) :
    ∃ i ∈ s, (∑ i ∈ s, a i) / 2 - K - β ≤ ∑ j ∈ s, good i j * a j := by
  set μ : ℝ := ∑ i ∈ s, a i with hμ
  have hfar := antisymm_weight_le s a far ha hanti
  rw [← hμ] at hfar
  have hjoinedTotal : (∑ i ∈ s, ∑ j ∈ s, joined i j * (a i * a j)) ≤ β * μ := by
    have hrow : (∑ i ∈ s, ∑ j ∈ s, joined i j * (a i * a j)) =
        ∑ i ∈ s, a i * ∑ j ∈ s, joined i j * a j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hrow]
    calc
      (∑ i ∈ s, a i * ∑ j ∈ s, joined i j * a j) ≤ ∑ i ∈ s, a i * β :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hjoined i hi) (ha i hi)
      _ = β * μ := by rw [← Finset.sum_mul, hμ]; ring
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, two i j * (a i * a j)) ≤
      (∑ i ∈ s, ∑ j ∈ s, good i j * (a i * a j)) +
        (∑ i ∈ s, ∑ j ∈ s, far i j * (a i * a j)) +
        (∑ i ∈ s, ∑ j ∈ s, joined i j * (a i * a j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hprod : 0 ≤ a i * a j := mul_nonneg (ha i hi) (ha j hj)
    have h := mul_le_mul_of_nonneg_right (hpoint i hi j hj) hprod
    linarith
  apply exists_heavy_row s a good (μ / 2 - K - β) ha hpos
  rw [← hμ]
  nlinarith

end Erdos1016.PolynomialBound.Averaging

import Erdos1016.PolynomialBound.Averaging

set_option autoImplicit false

/-!
# The two-fifths second moment and the heavy row

These finite probability and weighted-sum lemmas supply the numerical step in
Section 8.3 of the minimal exact-maximum paper. They do not prove the geometric
packing, separator, or large-girth statements.

The far-pair relation is bounded relative to the exactly-two-link kernel.
This gives half of that kernel's weight, rather than half of all pair weight.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.Averaging

open BoundaryDecay
open PolynomialBound.Averaging

variable {Ω : Type*} [Fintype Ω] {ι : Type*}

/-- A zero probability of at least two fifths gives the kernel coefficient
two thirds in the second-moment lower bound. -/
theorem kernel_weight_ge_two_fifths [Nonempty Ω] (Z : Ω → ℝ) (μ W K : ℝ)
    (hmean : average Z = μ)
    (hsecond : average (fun x => Z x ^ 2) ≤ μ ^ 2 + W + K * μ)
    (hzero : (2 / 5 : ℝ) ≤ Finite.density (fun x => Z x = 0)) :
    (2 / 3 : ℝ) * μ ^ 2 - K * μ ≤ W := by
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
  have hnonzero : Finite.density (fun x => Z x ≠ 0) ≤ (3 / 5 : ℝ) := by
    linarith
  have hle := mul_le_mul_of_nonneg_left hnonzero hnonneg
  rw [hmean] at hcs
  linarith

/-- If opposite orientations together use at most the ambient kernel, the
oriented relation carries at most half of its total pair weight. -/
theorem oriented_weight_le_half_kernel (s : Finset ι) (a : ι → ℝ)
    (far two : ι → ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, far i j + far j i ≤ two i j) :
    2 * (∑ i ∈ s, ∑ j ∈ s, far i j * (a i * a j)) ≤
      ∑ i ∈ s, ∑ j ∈ s, two i j * (a i * a j) := by
  have hswap : (∑ i ∈ s, ∑ j ∈ s, far i j * (a i * a j)) =
      ∑ i ∈ s, ∑ j ∈ s, far j i * (a i * a j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    2 * (∑ i ∈ s, ∑ j ∈ s, far i j * (a i * a j)) =
        (∑ i ∈ s, ∑ j ∈ s, far i j * (a i * a j)) +
          ∑ i ∈ s, ∑ j ∈ s, far j i * (a i * a j) := by
            rw [← hswap]; ring
    _ = ∑ i ∈ s, ∑ j ∈ s, (far i j + far j i) * (a i * a j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hanti i hi j hj) (mul_nonneg (ha i hi) (ha j hj))

/-- The relative far-pair estimate preserves half of the two-link weight.
The remaining loss is the bound on each row of joined pairs. -/
theorem exists_good_row_relative (s : Finset ι) (a : ι → ℝ)
    (two far joined good : ι → ι → ℝ) (γ K β : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i)
    (hpoint : ∀ i ∈ s, ∀ j ∈ s, two i j ≤ good i j + far i j + joined i j)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, far i j + far j i ≤ two i j)
    (hW : γ * (∑ i ∈ s, a i) ^ 2 - K * (∑ i ∈ s, a i) ≤
      ∑ i ∈ s, ∑ j ∈ s, two i j * (a i * a j))
    (hjoined : ∀ i ∈ s, (∑ j ∈ s, joined i j * a j) ≤ β) :
    ∃ i ∈ s, γ * (∑ i ∈ s, a i) / 2 - K / 2 - β ≤
      ∑ j ∈ s, good i j * a j := by
  set μ : ℝ := ∑ i ∈ s, a i with hμ
  have hfar := oriented_weight_le_half_kernel s a far two ha hanti
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
    have h := mul_le_mul_of_nonneg_right (hpoint i hi j hj)
      (mul_nonneg (ha i hi) (ha j hj))
    linarith
  apply exists_heavy_row s a good (γ * μ / 2 - K / 2 - β) ha hpos
  rw [← hμ]
  nlinarith

/-- The numerical heavy row used by the chain proof: total cycle weight
above thirty and error at most one half give a good row of weight above eight. -/
theorem exists_good_row_gt_eight (s : Finset ι) (a : ι → ℝ)
    (two far joined good : ι → ι → ℝ) (η : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hμ : 30 < ∑ i ∈ s, a i) (hη : η ≤ 1 / 2)
    (hpoint : ∀ i ∈ s, ∀ j ∈ s, two i j ≤ good i j + far i j + joined i j)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, far i j + far j i ≤ two i j)
    (hW : (2 / 3 : ℝ) * (∑ i ∈ s, a i) ^ 2 -
      (1 + η) * (∑ i ∈ s, a i) ≤
        ∑ i ∈ s, ∑ j ∈ s, two i j * (a i * a j))
    (hjoined : ∀ i ∈ s, (∑ j ∈ s, joined i j * a j) ≤ 1 / 2) :
    ∃ i ∈ s, 8 < ∑ j ∈ s, good i j * a j := by
  obtain ⟨i, hi, hrow⟩ := exists_good_row_relative s a two far joined good
    (2 / 3) (1 + η) (1 / 2) ha (by linarith) hpoint hanti hW hjoined
  refine ⟨i, hi, ?_⟩
  linarith

end Erdos1016.ExactMaximumSupport.Averaging

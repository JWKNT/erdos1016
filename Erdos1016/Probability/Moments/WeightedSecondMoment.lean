import Erdos1016.Probability.Moments.SecondMoments

set_option autoImplicit false

/-!
# Sharp zero-event bounds and weighted second moments

The probability space is the complete finite uniform space. Cauchy–Schwarz
on the support of a random variable gives the sharp second-moment bound for
its zero event. The final summation lemma permits an aggregate exceptional
pair mass, rather than requiring a bound on the number of exceptional pairs.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryDecay

local instance weightedMomentsDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {Ω : Type*} [Fintype Ω]

theorem mean_sq_le_second_mul_nonzero_density (Z : Ω → ℝ) :
    average Z ^ 2 ≤
      average (fun x => Z x ^ 2) * Finite.density (fun x => Z x ≠ 0) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset Ω) Z (indicator (fun x => Z x ≠ 0))
  have hproduct : ∀ x, Z x * indicator (fun x => Z x ≠ 0) x = Z x := by
    intro x
    by_cases hx : Z x = 0 <;> simp [indicator, hx]
  simp only [hproduct, indicator_sq] at hcs
  have hden : 0 ≤ (Fintype.card Ω : ℝ) ^ 2 := sq_nonneg _
  have hdiv := div_le_div_of_nonneg_right hcs hden
  simpa only [average, Finite.density, Finite.count, indicator, div_pow,
    ← mul_div_mul_comm, pow_two] using hdiv

theorem second_moment_pos_of_mean_pos (Z : Ω → ℝ) (hmean : 0 < average Z) :
    0 < average (fun x => Z x ^ 2) := by
  have hcs := mean_sq_le_second_mul_nonzero_density Z
  have hnonneg : 0 ≤ average (fun x => Z x ^ 2) := by
    simpa only [average_zero] using
      (average_mono (f := fun _ : Ω => 0) (fun x => sq_nonneg (Z x)))
  have hdensity := Finite.density_le_one (fun x => Z x ≠ 0)
  have hle := mul_le_mul_of_nonneg_left hdensity hnonneg
  nlinarith [sq_pos_of_pos hmean]

theorem zero_density_le_one_sub_mean_sq_div_second [Nonempty Ω]
    (Z : Ω → ℝ) (hmean : 0 < average Z) :
    Finite.density (fun x => Z x = 0) ≤
      1 - average Z ^ 2 / average (fun x => Z x ^ 2) := by
  classical
  have hsecond := second_moment_pos_of_mean_pos Z hmean
  have hcs := mean_sq_le_second_mul_nonzero_density Z
  have hcomplement :
      Finite.density (fun x => Z x = 0) +
        Finite.density (fun x => Z x ≠ 0) = 1 := by
    rw [← average_indicator, ← average_indicator, ← average_add]
    convert average_const (Ω := Ω) (1 : ℝ) using 1
    congr 1
    funext x
    by_cases hx : Z x = 0 <;> simp [indicator, hx]
  have hquot : average Z ^ 2 / average (fun x => Z x ^ 2) ≤
      Finite.density (fun x => Z x ≠ 0) :=
    (div_le_iff₀ hsecond).2 (by simpa [mul_comm] using hcs)
  linarith

/-- The finite form of the shorter proof's estimate (1). No nonnegativity
assumption on `Z` is needed for this support version of Cauchy–Schwarz. -/
theorem zero_density_le_half_add_of_second_moment [Nonempty Ω]
    (Z : Ω → ℝ) (μ K : ℝ) (hμ : 0 < μ) (hK : 0 ≤ K)
    (hmean : average Z = μ)
    (hsecond : average (fun x => Z x ^ 2) ≤ 2 * μ ^ 2 + K * μ) :
    Finite.density (fun x => Z x = 0) ≤ 1 / 2 + K / (4 * μ + 2 * K) := by
  have hpos := second_moment_pos_of_mean_pos Z (hmean ▸ hμ)
  have hboundpos : 0 < 2 * μ ^ 2 + K * μ := by positivity
  have hquot : μ ^ 2 / (2 * μ ^ 2 + K * μ) ≤
      μ ^ 2 / average (fun x => Z x ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg μ) hpos hsecond
  have hzero := zero_density_le_one_sub_mean_sq_div_second Z (hmean ▸ hμ)
  rw [hmean] at hzero
  have hid : 1 - μ ^ 2 / (2 * μ ^ 2 + K * μ) =
      1 / 2 + K / (4 * μ + 2 * K) := by
    have hd : 0 < 4 * μ + 2 * K := by positivity
    field_simp
    ring
  linarith

/-- Scale an indicator to have the desired mean `a`. Its values are at most
one when the target mean does not exceed the event's actual probability. -/
def normalizedIndicator (P : Ω → Prop) (a : ℝ) (x : Ω) : ℝ :=
  (a / Finite.density P) * indicator P x

theorem normalizedIndicator_nonneg (P : Ω → Prop) (a : ℝ) (ha : 0 ≤ a)
    (x : Ω) : 0 ≤ normalizedIndicator P a x := by
  classical
  have hprob := Finite.density_nonneg P
  unfold normalizedIndicator indicator
  split_ifs <;> positivity

theorem normalizedIndicator_le_one (P : Ω → Prop) (a : ℝ)
    (ha : a ≤ Finite.density P) (hp : 0 < Finite.density P) (x : Ω) :
    normalizedIndicator P a x ≤ 1 := by
  classical
  by_cases hx : P x
  · simpa [normalizedIndicator, indicator, hx] using (div_le_one hp).2 ha
  · simp [normalizedIndicator, indicator, hx]

@[simp] theorem average_normalizedIndicator (P : Ω → Prop) (a : ℝ)
    (hp : Finite.density P ≠ 0) : average (normalizedIndicator P a) = a := by
  change average (fun x => (a / Finite.density P) * indicator P x) = a
  rw [average_mul_left, average_indicator]
  exact div_mul_cancel₀ a hp

theorem normalizedIndicator_eq_zero_iff (P : Ω → Prop) (a : ℝ)
    (ha : 0 < a) (hp : 0 < Finite.density P) (x : Ω) :
    normalizedIndicator P a x = 0 ↔ ¬ P x := by
  classical
  by_cases hx : P x
  · simp [normalizedIndicator, indicator, hx, ne_of_gt (div_pos ha hp)]
  · simp [normalizedIndicator, indicator, hx]

/-- Normalizing the marginal means preserves the exact correlation factor. -/
theorem normalizedIndicator_joint_of_ratio (P Q : Ω → Prop) (a b k : ℝ)
    (hp : Finite.density P ≠ 0) (hq : Finite.density Q ≠ 0)
    (hpair : Finite.density (fun x => P x ∧ Q x) =
      k * Finite.density P * Finite.density Q) :
    average (fun x => normalizedIndicator P a x * normalizedIndicator Q b x) =
      k * a * b := by
  have he : (fun x => normalizedIndicator P a x * normalizedIndicator Q b x) =
      (fun x => (a / Finite.density P * (b / Finite.density Q)) *
        indicator (fun x => P x ∧ Q x) x) := by
    funext x
    rw [← indicator_mul]
    unfold normalizedIndicator
    ring
  rw [he, average_mul_left, average_indicator, hpair]
  field_simp
  ring

/-- Incompatible events give zero mixed moment after normalization. -/
theorem normalizedIndicator_joint_eq_zero (P Q : Ω → Prop) (a b : ℝ)
    (hdisj : ∀ x, ¬ (P x ∧ Q x)) :
    average (fun x => normalizedIndicator P a x * normalizedIndicator Q b x) = 0 := by
  have he : (fun x => normalizedIndicator P a x * normalizedIndicator Q b x) =
      fun _ => (0 : ℝ) := by
    funext x
    by_cases hp : P x
    · have hq : ¬ Q x := fun hq => hdisj x ⟨hp, hq⟩
      simp [normalizedIndicator, indicator, hq]
    · simp [normalizedIndicator, indicator, hp]
  rw [he, average_zero]

variable {ι : Type*}

/-- The complete double sum, including the diagonal, is the second moment
of the sum. This holds for arbitrary real-valued summands. -/
theorem second_average_sum (s : Finset ι) (X : ι → Ω → ℝ) :
    average (fun x => (∑ i ∈ s, X i x) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, average (fun x => X i x * X j x) := by
  have heq : (fun x => (∑ i ∈ s, X i x) ^ 2) =
      (fun x => ∑ i ∈ s, ∑ j ∈ s, X i x * X j x) := by
    funext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [heq]
  simp only [average_sum]

/-- Ordinary off-diagonal pairs have at most twice the product of their
means. The total mass of exceptional off-diagonal pairs in row `i` is at
most `η * a i`. No independence or symmetry assumption is required. -/
theorem weighted_sum_second_moment_le
    (s : Finset ι) (X : ι → Ω → ℝ) (a : ι → ℝ)
    (exceptional : ι → ι → Prop) (η : ℝ)
    (hXnonneg : ∀ i ∈ s, ∀ x, 0 ≤ X i x)
    (hXle : ∀ i ∈ s, ∀ x, X i x ≤ 1)
    (hmean : ∀ i ∈ s, average (X i) = a i)
    (hordinary : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ exceptional i j →
      average (fun x => X i x * X j x) ≤ 2 * a i * a j)
    (hrow : ∀ i ∈ s,
      (∑ j ∈ s, if i ≠ j ∧ exceptional i j then
        average (fun x => X i x * X j x) else 0) ≤ η * a i) :
    average (fun x => (∑ i ∈ s, X i x) ^ 2) ≤
      2 * (∑ i ∈ s, a i) ^ 2 + (1 + η) * (∑ i ∈ s, a i) := by
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
        2 * a i * a j +
          (if i ≠ j ∧ exceptional i j then
            average (fun x => X i x * X j x) else 0) +
          (if i = j then a i else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, if_false, if_true, add_zero]
      nlinarith [hdiag i hi, sq_nonneg (a i)]
    · by_cases he : exceptional i j
      · simp only [ne_eq, hij, not_false_eq_true, he, and_self, if_true, if_false,
          add_zero]
        nlinarith [mul_nonneg (ha i hi) (ha j hj)]
      · simpa [hij, he] using hordinary i hi j hj hij he
  have hsum := Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun j hj => hterm i hi j hj
  have hpair : (∑ i ∈ s, ∑ j ∈ s, 2 * a i * a j) =
      2 * (∑ i ∈ s, a i) ^ 2 := by
    simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, sq]
  have hdiagsum : (∑ i ∈ s, ∑ j ∈ s, if i = j then a i else 0) =
      ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi, eq_comm]
  have hrows := Finset.sum_le_sum hrow
  simp only [← Finset.mul_sum] at hrows
  rw [second_average_sum]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hpair, hdiagsum] at hsum
  nlinarith

end Erdos1016.BoundaryDecay

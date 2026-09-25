import Erdos1016.Probability.Finite.Counting

set_option autoImplicit false

/-!
# Finite second moments on the complete uniform state space

Source: `ANALYTIC_CUBIC_INVERSE_PROOF.md`, (4.5) and Section 12.

All averages use the ENTIRE finite type, not a witness distribution or a
uniform distribution on previously successful states. This module proves
the zero-event second-moment inequality directly by finite sums. It does not
assume a probability/variance estimate as a black box.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryDecay

local instance finiteMomentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {Ω : Type*} [Fintype Ω]

def average (f : Ω → ℝ) : ℝ := (∑ x, f x) / Fintype.card Ω

def indicator (P : Ω → Prop) (x : Ω) : ℝ := if P x then 1 else 0

def variance (f : Ω → ℝ) : ℝ := average (fun x => (f x - average f) ^ 2)

@[simp] theorem average_indicator (P : Ω → Prop) :
    average (indicator P) = Finite.density P := rfl

@[simp] theorem average_zero : average (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [average]



theorem average_mono {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) :
    average f ≤ average g :=
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

@[simp] theorem average_add (f g : Ω → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

@[simp] theorem average_sub (f g : Ω → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

@[simp] theorem average_mul_left (a : ℝ) (f : Ω → ℝ) :
    average (fun x => a * f x) = a * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

@[simp] theorem average_mul_right (a : ℝ) (f : Ω → ℝ) :
    average (fun x => f x * a) = average f * a := by
  simp only [average, ← Finset.sum_mul]
  ring

@[simp] theorem average_const [Nonempty Ω] (a : ℝ) :
    average (fun _ : Ω => a) = a := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Ω)
  simp [average, hn]

@[simp] theorem average_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    average (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

@[simp] theorem indicator_sq (P : Ω → Prop) (x : Ω) :
    indicator P x ^ 2 = indicator P x := by
  by_cases h : P x <;> simp [indicator, h]

@[simp] theorem indicator_mul (P Q : Ω → Prop) (x : Ω) :
    indicator P x * indicator Q x = indicator (fun x => P x ∧ Q x) x := by
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [indicator, hp, hq]

/-- No limiting assertion is used in the second-moment identity. -/
theorem variance_eq_second_sub_sq [Nonempty Ω] (f : Ω → ℝ) :
    variance f = average (fun x => f x ^ 2) - average f ^ 2 := by
  have heq : (fun x => (f x - average f) ^ 2) =
      (fun x => f x ^ 2 - (2 * average f) * f x + average f ^ 2) := by
    funext x
    ring
  rw [variance, heq, average_add, average_sub, average_mul_left, average_const]
  ring



/-- On the zero event the squared deviation is exactly the squared mean.
This works for any real random variable; positivity is needed only to divide. -/
theorem zero_density_mul_mean_sq_le_variance (f : Ω → ℝ) :
    Finite.density (fun x => f x = 0) * average f ^ 2 ≤ variance f := by
  have hpoint (x : Ω) :
      indicator (fun x => f x = 0) x * average f ^ 2 ≤
        (f x - average f) ^ 2 := by
    by_cases hx : f x = 0
    · simp [indicator, hx]
    · simpa [indicator, hx] using sq_nonneg (f x - average f)
  simpa only [average_mul_right, average_indicator, variance] using
    average_mono hpoint

theorem zero_density_le_variance_div (f : Ω → ℝ) (hm : 0 < average f) :
    Finite.density (fun x => f x = 0) ≤ variance f / average f ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hm)).2
  exact zero_density_mul_mean_sq_le_variance f

variable {ι : Type*}

def eventCount (s : Finset ι) (P : ι → Ω → Prop) (x : Ω) : ℝ :=
  ∑ i ∈ s, indicator (P i) x

def eventMass (s : Finset ι) (P : ι → Ω → Prop) : ℝ :=
  ∑ i ∈ s, Finite.density (P i)

@[simp] theorem average_eventCount (s : Finset ι) (P : ι → Ω → Prop) :
    average (eventCount s P) = eventMass s P := by
  calc
    average (eventCount s P) =
        average (fun x => ∑ i ∈ s, indicator (P i) x) := rfl
    _ = ∑ i ∈ s, average (indicator (P i)) := average_sum s _
    _ = eventMass s P := by simp [eventMass]



/-- The complete double sum includes the diagonal. -/
theorem second_eventCount (s : Finset ι) (P : ι → Ω → Prop) :
    average (fun x => eventCount s P x ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, Finite.density (fun x => P i x ∧ P j x) := by
  have heq : (fun x => eventCount s P x ^ 2) =
      (fun x => ∑ i ∈ s, ∑ j ∈ s, indicator (fun x => P i x ∧ P j x) x) := by
    funext x
    simp only [eventCount, pow_two, Finset.sum_mul, Finset.mul_sum,
      indicator_mul]
    simp_rw [and_comm]
  rw [heq]
  simp only [average_sum, average_indicator]

theorem eventCount_eq_zero_iff (s : Finset ι) (P : ι → Ω → Prop) (x : Ω) :
    eventCount s P x = 0 ↔ ∀ i ∈ s, ¬ P i x := by
  constructor
  · intro hz i hi hpi
    have hle : indicator (P i) x ≤ eventCount s P x := by
      unfold eventCount
      exact Finset.single_le_sum
        (f := fun j => indicator (P j) x)
        (fun j _ => by by_cases hj : P j x <;> simp [indicator, hj]) hi
    rw [hz] at hle
    have hbad : (1 : ℝ) ≤ 0 := by simpa [indicator, hpi] using hle
    exact (not_le_of_gt zero_lt_one) hbad
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    simp [indicator, h i hi]

/-- A finite pairwise probability upper bound suffices; no mutual independence
or sequential resampling assumption is used. -/
theorem eventCount_variance_le_mass_add_error [Nonempty Ω]
    (s : Finset ι) (P : ι → Ω → Prop) (err : ι → ι → ℝ)
    (herr : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ err i j)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Finite.density (fun x => P i x ∧ P j x) ≤
        Finite.density (P i) * Finite.density (P j) + err i j) :
    variance (eventCount s P) ≤ eventMass s P + ∑ i ∈ s, ∑ j ∈ s, err i j := by
  classical
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Finite.density (fun x => P i x ∧ P j x) ≤
        Finite.density (P i) * Finite.density (P j) + err i j +
          (if i = j then Finite.density (P i) else 0) := by
    by_cases hij : i = j
    · subst j
      have heq : Finite.density (fun x => P i x ∧ P i x) =
          Finite.density (P i) := by simp
      rw [heq, if_pos rfl]
      have hp := Finite.density_nonneg (P i)
      have he := herr i hi i hi
      nlinarith [sq_nonneg (Finite.density (P i))]
    · simpa only [if_neg hij, add_zero] using hpair i hi j hj hij
  have hsum := Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun j hj => hterm i hi j hj
  have hdiag : (∑ i ∈ s, ∑ j ∈ s,
      if i = j then Finite.density (P i) else 0) = eventMass s P := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi, eq_comm]
  have hprod : (∑ i ∈ s, ∑ j ∈ s,
      Finite.density (P i) * Finite.density (P j)) = eventMass s P ^ 2 := by
    rw [eventMass, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hdiag, hprod] at hsum
  rw [variance_eq_second_sub_sq, second_eventCount, average_eventCount]
  linarith

/-- MANY: mutually incompatible or pairwise independent distinct events both
satisfy this bound. The only denominator is their total expected count. -/
theorem no_events_density_le_inverse_mass [Nonempty Ω]
    (s : Finset ι) (P : ι → Ω → Prop) (hm : 0 < eventMass s P)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Finite.density (fun x => P i x ∧ P j x) ≤
        Finite.density (P i) * Finite.density (P j)) :
    Finite.density (fun x => ∀ i ∈ s, ¬ P i x) ≤ 1 / eventMass s P := by
  have hv := eventCount_variance_le_mass_add_error s P (fun _ _ => 0)
    (fun _ _ _ _ => le_rfl) (by simpa using hpair)
  simp only [Finset.sum_const_zero, add_zero] at hv
  have hz := zero_density_le_variance_div (eventCount s P)
    (by simpa using hm)
  have heq : (fun x => eventCount s P x = 0) =
      (fun x => ∀ i ∈ s, ¬ P i x) := by
    funext x
    exact propext (eventCount_eq_zero_iff s P x)
  rw [heq, average_eventCount] at hz
  calc
    Finite.density (fun x => ∀ i ∈ s, ¬ P i x)
        ≤ variance (eventCount s P) / eventMass s P ^ 2 := hz
    _ ≤ eventMass s P / eventMass s P ^ 2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = 1 / eventMass s P := by
      rw [pow_two]
      field_simp [ne_of_gt hm]



end Erdos1016.BoundaryDecay

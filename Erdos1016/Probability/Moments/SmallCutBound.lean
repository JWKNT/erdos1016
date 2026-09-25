import Erdos1016.Probability.Moments.WeightedSecondMoment

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryDecay

local instance smallCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]

/-- The probabilistic form of the small-cut argument. A graph application
supplies the zero-cut events, their marginal lower bound, and the linear
exceptional-partner count. The conclusion has the paper's exact constant. -/
theorem small_cut_event_bound (s : Finset ι) (hs : s.Nonempty)
    (P : ι → Ω → Prop) (forest : Ω → Prop) (exceptional : ι → ι → Prop) (d : ℕ)
    (hprob : ∀ i ∈ s, 1 / (2 : ℝ) ^ (d + 1) ≤ Finite.density (P i))
    (hexceptional : ∀ i ∈ s, (s.filter fun j => i ≠ j ∧ exceptional i j).card ≤ d)
    (hordinary : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ exceptional i j →
      Finite.density (fun x => P i x ∧ P j x) ≤
        2 * Finite.density (P i) * Finite.density (P j))
    (hforest : ∀ x, forest x → ∀ i ∈ s, ¬ P i x) :
    Finite.density forest ≤ (1 / 2 : ℝ) + ((d : ℝ) + 1) * (2 : ℝ) ^ d /
      (2 * (s.card : ℝ)) := by
  classical
  let μ : ℝ := ∑ i ∈ s, Finite.density (P i)
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hμlower : (s.card : ℝ) / (2 : ℝ) ^ (d + 1) ≤ μ := by
    have h := Finset.sum_le_sum hprob
    simpa [μ, div_eq_mul_inv] using h
  have hμ : 0 < μ := (div_pos hcard (by positivity)).trans_le hμlower
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, if i ≠ j ∧ exceptional i j then
        average (fun x => indicator (P i) x * indicator (P j) x) else 0) ≤
          (d : ℝ) * Finite.density (P i) := by
    have hpair (j : ι) : average (fun x => indicator (P i) x * indicator (P j) x) ≤
        Finite.density (P i) := by
      rw [← average_indicator]
      apply average_mono
      intro x
      by_cases hpi : P i x <;> by_cases hpj : P j x <;> simp [indicator, hpi, hpj]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ s) =>
      show (if i ≠ j ∧ exceptional i j then
        average (fun x => indicator (P i) x * indicator (P j) x) else 0) ≤
          (if i ≠ j ∧ exceptional i j then Finite.density (P i) else 0) from by
        split_ifs <;> simp only [le_refl, hpair])
    have hcount : (∑ j ∈ s, if i ≠ j ∧ exceptional i j then Finite.density (P i) else 0) =
        ((s.filter fun j => i ≠ j ∧ exceptional i j).card : ℝ) * Finite.density (P i) := by
      rw [← Finset.sum_filter]
      simp
    rw [hcount] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hexceptional i hi)
      (Finite.density_nonneg _))
  have hsecond := weighted_sum_second_moment_le s (fun i => indicator (P i))
    (fun i => Finite.density (P i)) exceptional (d : ℝ)
    (fun i _ x => by simp only [indicator]; split_ifs <;> norm_num)
    (fun i _ x => by simp only [indicator]; split_ifs <;> norm_num)
    (fun i _ => average_indicator (P i))
    (fun i hi j hj hij he => by
      simpa only [indicator_mul, average_indicator] using hordinary i hi j hj hij he) hrow
  have hzero := zero_density_le_half_add_of_second_moment
    (fun x => ∑ i ∈ s, indicator (P i) x) μ ((d : ℝ) + 1) hμ (by positivity)
    (by simp [μ]) (by simpa [μ, add_comm] using hsecond)
  have hforestzero : Finite.density forest ≤
      Finite.density (fun x => (∑ i ∈ s, indicator (P i) x) = 0) := by
    rw [← average_indicator, ← average_indicator]
    apply average_mono
    intro x
    by_cases hx : forest x
    · have hz : (∑ i ∈ s, indicator (P i) x) = 0 :=
        Finset.sum_eq_zero (fun i hi => by simp [indicator, hforest x hx i hi])
      change (if forest x then (1 : ℝ) else 0) ≤
        if (∑ i ∈ s, indicator (P i) x) = 0 then 1 else 0
      rw [if_pos hx, if_pos hz]
    · simp only [indicator, hx, ↓reduceIte]
      split_ifs <;> norm_num
  have hquot : ((d : ℝ) + 1) / (4 * μ + 2 * ((d : ℝ) + 1)) ≤
      ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * (s.card : ℝ)) := by
    have hfirst : ((d : ℝ) + 1) / (4 * μ + 2 * ((d : ℝ) + 1)) ≤
        ((d : ℝ) + 1) / (4 * ((s.card : ℝ) / (2 : ℝ) ^ (d + 1))) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    have hid : ((d : ℝ) + 1) / (4 * ((s.card : ℝ) / (2 : ℝ) ^ (d + 1))) =
        ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * (s.card : ℝ)) := by
      rw [pow_succ]
      field_simp
      ring
    exact hid ▸ hfirst
  linarith

end Erdos1016.BoundaryDecay

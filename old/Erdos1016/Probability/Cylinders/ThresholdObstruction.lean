import Erdos1016.Probability.Cylinders.ThresholdMonotonicity

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.BadVertexCylinderThreshold

open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.BadVertexCylinderCount

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
  [DecidableEq ι]

/-- A sufficiently large mean of graphical cylinders cannot be hidden inside
the failure of an event whose probability is below `1/2 - 1/R`. This is the
second-moment step used to bound high-degree vertices in the Section 10
cleanup. The constant `1000` is deliberately loose; only an absolute multiple
of `R` is needed by the later region extraction. -/
theorem impossible_many_cylinders_under_small_event
    (E : ι → Ω → Prop) (exceptional : ι → ι → Prop)
    [DecidableRel exceptional] (F : Ω → Prop) (R : ℕ)
    (hR : 5 ≤ R)
    (hmean : (65 : ℝ) * (R : ℝ) ≤
      ∑ i, eventProbability (E i))
    (hdiag : ∀ i,
      eventProbability (fun x => E i x ∧ E i x) ≤ eventProbability (E i))
    (hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤
        2 * eventProbability (E i) * eventProbability (E j))
    (hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤ eventProbability (E i))
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ 64)
    (hcontained : ∀ x, 1 ≤ eventCount E x → ¬ F x)
    (hsmall : eventProbability (fun x => ¬ F x) <
      (1 / 2 : ℝ) - 1 / (R : ℝ)) : False := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by omega)
  let μ : ℝ := ∑ i, eventProbability (E i)
  have hμlarge : (65 : ℝ) * (R : ℝ) ≤ μ := by
    simpa [μ] using hmean
  have hμpos : 0 < μ := by
    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (show 0 < R by omega)
    nlinarith [hμlarge]
  have hμge1 : 1 < μ := by
    have hR5 : (5 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    nlinarith
  have hpartners' : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ (64 : ℝ) :=
    fun i => by exact_mod_cast hpartners i
  have htail := cylinder_threshold_le_of_contained_event E exceptional
    (fun x => ¬ F x) (64 : ℝ) 1 μ ((1 / 2 : ℝ) - 1 / (R : ℝ))
    (by norm_num) hμge1 (by norm_num)
    (by rfl)
    hdiag hordinary hexceptional hpartners' hcontained (le_of_lt hsmall)
  have hden : 0 < 2 * μ ^ 2 + 65 * μ := by positivity
  have hratio : (1 / 2 : ℝ) - 18 / μ ≤
      (μ - 1) ^ 2 / (2 * μ ^ 2 + 65 * μ) := by
    apply (le_div_iff₀ hden).2
    have hmul : ((1 / 2 : ℝ) - 18 / μ) *
        (2 * μ ^ 2 + 65 * μ) = μ ^ 2 - (7 / 2 : ℝ) * μ - 1170 := by
      field_simp
      ring
    rw [hmul]
    nlinarith
  have hrecip : 18 / μ < 1 / (R : ℝ) := by
    have hscaled : 18 / μ ≤ 18 / (65 * (R : ℝ)) := by
      apply (div_le_div_iff₀ hμpos (by positivity)).2
      nlinarith [hμlarge]
    have hstrict : 18 / (65 * (R : ℝ)) < 1 / (R : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity) hRpos).2
      nlinarith
    exact hscaled.trans_lt hstrict
  have hstrict : (1 / 2 : ℝ) - 1 / (R : ℝ) <
      (μ - 1) ^ 2 / (2 * μ ^ 2 + 65 * μ) := by
    linarith
  linarith

end Erdos1016.Proof.BadVertexCylinderThreshold

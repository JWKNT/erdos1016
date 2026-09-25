import Erdos1016.Cleanup.Degree.LinearBadVertexBound
import Erdos1016.Probability.Conditional.UniformReveal

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Erdos1016.Proof.ManyCyclicRegionsGeneralPartnerThreshold

open Erdos1016.Proof.GraphicalThreshold

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- Arbitrary exceptional partner budget version of the Section 10 estimate.
The second moment denominator is retained in its natural form. -/
theorem forest_probability_le_half_add
    (E : ι → Ω → Prop) (exceptional : ι → ι → Prop)
    [DecidableRel exceptional] (U : Ω → Prop) (R a K : ℕ)
    (hR : 5 ≤ R) (ha_pos : 1 ≤ a)
    (hdiag : ∀ i,
      eventProbability (fun x => E i x ∧ E i x) ≤ eventProbability (E i))
    (hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤
        2 * eventProbability (E i) * eventProbability (E j))
    (hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤ eventProbability (E i))
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ K)
    (hmean : (∑ i, eventProbability (E i)) ≥
      8 * (R : ℝ) * (K + (a : ℝ)))
    (hpow : (1 / 2 : ℝ) ^ a ≤ 1 / (4 * (R : ℝ)))
    (hproduct : eventProbability U ≤
      1 - eventProbability (fun x => (a : ℝ) ≤ eventCount E x) +
        (1 / 2 : ℝ) ^ a) :
    eventProbability U ≤ (1 / 2 : ℝ) + 1 / (2 * (R : ℝ)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hmu : (a : ℝ) < ∑ i, eventProbability (E i) := by
    have hfactor : (a : ℝ) < 8 * (R : ℝ) * ((K : ℝ) + (a : ℝ)) := by
      have hR5 : (5 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hs : 0 ≤ (K : ℝ) + (a : ℝ) := by positivity
      have hp := mul_le_mul_of_nonneg_right hR5 hs
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
      nlinarith
    exact lt_of_lt_of_le hfactor hmean
  have htail := graphical_cylinder_threshold E exceptional (K : ℝ) (a : ℝ)
    (∑ i, eventProbability (E i)) ha_nonneg hmu hK rfl
    hdiag hordinary hexceptional hpartners
  let μ : ℝ := ∑ i, eventProbability (E i)
  have hμ_nonneg : 0 ≤ μ := by dsimp [μ]; linarith [hmu]
  have hden : 0 < 2 * μ ^ 2 + (1 + (K : ℝ)) * μ := by
    have hsumpos : 0 < μ := by dsimp [μ]; linarith [hmu]
    positivity
  have htailProb : (μ - (a : ℝ)) ^ 2 /
      (2 * μ ^ 2 + (1 + (K : ℝ)) * μ) ≤
        eventProbability (fun x => (a : ℝ) ≤ eventCount E x) := by
    simpa [μ, eventProbability] using htail
  have htail_lower : (1 / 2 : ℝ) - 1 / (4 * (R : ℝ)) ≤
        eventProbability (fun x => (a : ℝ) ≤ eventCount E x) := by
    have hmulμ : 8 * (R : ℝ) * ((K : ℝ) + (a : ℝ)) * μ ≤ μ ^ 2 := by
      have hsum_nonneg : 0 ≤ μ := by dsimp [μ]; linarith [hmu]
      have hp := mul_le_mul_of_nonneg_right hmean hsum_nonneg
      dsimp [μ] at hp ⊢
      nlinarith [hp]
    have hnum : (1 / 2 : ℝ) - 1 / (4 * (R : ℝ)) ≤
        (μ - (a : ℝ)) ^ 2 / (2 * μ ^ 2 + (1 + (K : ℝ)) * μ) := by
      have hcoefR : (0 : ℝ) < 4 * (R : ℝ) := by positivity
      rw [show (1 / 2 : ℝ) - 1 / (4 * (R : ℝ)) =
        (2 * (R : ℝ) - 1) / (4 * (R : ℝ)) by field_simp; ring]
      rw [div_le_div_iff₀ hcoefR hden]
      have hbig : 16 * (R : ℝ) * ((K : ℝ) + (a : ℝ)) * μ ≤ 2 * μ ^ 2 := by
        nlinarith [hmulμ]
      have hKnonneg : 0 ≤ (K : ℝ) := by positivity
      have hsum : 0 ≤ (K : ℝ) + (a : ℝ) := by positivity
      have hR5 : (5 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
      have hcoef : 0 ≤ (R : ℝ) * (14 * (K : ℝ) + 8 * (a : ℝ) - 2) + (K : ℝ) + 1 := by
        have hinside : 0 ≤ 14 * (K : ℝ) + 8 * (a : ℝ) - 2 := by nlinarith [hKnonneg, ha1]
        positivity
      have hcoefμ := mul_nonneg hcoef hμ_nonneg
      nlinarith [hcoefμ, hmulμ, ha1]
    exact hnum.trans htailProb
  calc
    eventProbability U ≤ 1 - eventProbability (fun x => (a : ℝ) ≤ eventCount E x) +
        (1 / 2 : ℝ) ^ a := hproduct
    _ ≤ 1 - ((1 / 2 : ℝ) - 1 / (4 * (R : ℝ))) + 1 / (4 * (R : ℝ)) := by
      linarith [htail_lower, hpow]
    _ = (1 / 2 : ℝ) + 1 / (2 * (R : ℝ)) := by ring




end Erdos1016.Proof.ManyCyclicRegionsGeneralPartnerThreshold

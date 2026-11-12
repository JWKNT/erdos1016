import Erdos1016.ExactMaximumSupport.SecondOrder
import Erdos1016.ExactMaximum.LowerBound

set_option autoImplicit false

/-!
# Unconditional sharp second-order lower bound

This file combines the established graph-construction theorem
`ExactMaximum.lowerBoundStatement` with the proved parity arithmetic in
`SecondOrder`. Its graph threshold is honestly existential: the public
lower-bound statement does not expose a fixed threshold.

No eventual exactness or upper-bound hypothesis is used. The matching upper
comparison, and hence the two-sided sharp second-order theorem, remain separate.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport
open ExactMaximum CycleCount Filter Asymptotics

/-- The established lower-bound constructions give an eventual bound for the maximum. -/
theorem eventually_horakKim_le_maxCycles :
    ∃ R : ℕ, ∀ r, R ≤ r → horakKim r ≤ maxCycles r := by
  obtain ⟨R, hR⟩ := lowerBoundStatement
  refine ⟨R, fun r hr => ?_⟩
  obtain ⟨n, G, hRank, hCount⟩ := hR r hr
  exact hCount.trans (numCycles_le_maxCycles G r hRank)

/-- The sharp lower bound with the square-root scale and an existential graph threshold. -/
theorem maxCycles_secondOrder_lower_sqrt :
    ∃ R : ℕ, ∀ r, R ≤ r →
      (r : ℝ) * Real.sqrt ((2 : ℝ)^r) / 8 ≤
        (maxCycles r : ℝ) - (2 : ℝ)^(r-1) := by
  obtain ⟨R, hR⟩ := eventually_horakKim_le_maxCycles
  refine ⟨max R 6, fun r hr => ?_⟩
  have hHK := (horakKim_excess_real_bounds r (le_trans (le_max_right _ _) hr)).1
  have hGraph : (horakKim r : ℝ) ≤ (maxCycles r : ℝ) := by
    exact_mod_cast hR r (le_trans (le_max_left _ _) hr)
  linarith

/-- Eventually the excess is at least r*2^(r/2)/8, without an upper-bound hypothesis. -/
theorem maxCycles_secondOrder_lower :
    ∃ R : ℕ, ∀ r, R ≤ r →
      (r : ℝ) * (2 : ℝ)^((r : ℝ)/2) / 8 ≤
        (maxCycles r : ℝ) - (2 : ℝ)^(r-1) := by
  simpa only [sqrt_two_pow_eq_rpow] using maxCycles_secondOrder_lower_sqrt

/-- The unconditional lower-order comparison. The matching upper bound remains separate. -/
theorem secondOrder_scale_isBigO_maxCycles_excess :
    (fun r : ℕ => (r : ℝ)*(2 : ℝ)^((r : ℝ)/2)) =O[atTop]
      (fun r : ℕ => (maxCycles r : ℝ)-(2 : ℝ)^(r-1)) := by
  obtain ⟨R, hR⟩ := maxCycles_secondOrder_lower
  refine isBigO_iff.2 ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop R] with r hr
  have h := hR r hr
  have hs : 0 ≤ (r : ℝ)*(2 : ℝ)^((r : ℝ)/2) := by positivity
  have he : 0 ≤ (maxCycles r : ℝ)-(2 : ℝ)^(r-1) := le_trans (by positivity) h
  simp only [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg he]
  linarith

end Erdos1016.ExactMaximumSupport

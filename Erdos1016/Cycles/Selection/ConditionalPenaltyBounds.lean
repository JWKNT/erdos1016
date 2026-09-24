import Erdos1016.Cycles.Selection.PackingDecayAsymptotics

set_option autoImplicit false

/-!
# Section 7 conditional-load exponent arithmetic

The paper's effective-port estimate contains the factor
`K * ceil ((s - 1) / Δ)`.  With its choice
`Δ = K * (2 * r_c - 1) + 3`, this factor is at most
`K + (s - 1) / (2 * r_c - 1)`.  This is the arithmetic step that keeps
the conditioning loss in the conditional-neighbor load sublinear in the
girth parameter.
-/

namespace Erdos1016.Proof.ConditionalPenaltyBounds

private theorem natCeil_le_add_one (x : ℝ) (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 := by
  by_cases hz : Nat.ceil x = 0
  · rw [hz, Nat.cast_zero]
    linarith
  · have hn : 1 ≤ Nat.ceil x := by omega
    have hcast : ((Nat.ceil x - 1 : ℕ) : ℝ) + 1 = (Nat.ceil x : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hn
    have hxpred : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
      by_contra h
      have hle : x ≤ ((Nat.ceil x - 1 : ℕ) : ℝ) := le_of_not_gt h
      have hceil : Nat.ceil x ≤ Nat.ceil x - 1 := (Nat.ceil_le).2 hle
      omega
    linarith

/-- Exact upper bound on the repeated conditional degree-two penalty in
paper's load estimate.  Parameters use real ceiling, matching `Nat.ceil`
in Mathlib; `hΔ` is the chosen denominator lower bound. -/
theorem conditional_port_exponent_le
    (K r s Δ : ℕ) (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hΔ : K * (2 * r - 1) ≤ Δ) :
    ((K * Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) : ℕ) : ℝ) ≤
      (K : ℝ) + ((s - 1 : ℕ) : ℝ) / (2 * r - 1 : ℕ) := by
  have hden : 0 < (2 * r - 1 : ℕ) := by omega
  have hΔpos : 0 < Δ := by
    have : 0 < K * (2 * r - 1) := Nat.mul_pos (by omega) hden
    omega
  have hrealden : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔpos
  have hrealbase : (0 : ℝ) < (2 * r - 1 : ℕ) := by exact_mod_cast hden
  have hrealK : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hratio : (K : ℝ) * ((s - 1 : ℕ) : ℝ) / (Δ : ℝ) ≤
      ((s - 1 : ℕ) : ℝ) / (2 * r - 1 : ℕ) := by
    have hmul : (K : ℝ) * ((2 * r - 1 : ℕ) : ℝ) ≤ (Δ : ℝ) := by
      exact_mod_cast hΔ
    have ha : (0 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by positivity
    apply (div_le_div_iff₀ hrealden hrealbase).2
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hmul)]
  have hceil := natCeil_le_add_one
    (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) (div_nonneg (by positivity) hrealden.le)
  have hcastmul :
      ((K * Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) : ℕ) : ℝ) =
        (K : ℝ) * (Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) : ℝ) := by norm_cast
  rw [hcastmul]
  have hmul := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  calc
    (K : ℝ) * (Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) : ℝ)
        ≤ (K : ℝ) * (((s - 1 : ℕ) : ℝ) / (Δ : ℝ) + 1) := hmul
    _ = (K : ℝ) * (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) + K := by ring
    _ ≤ ((s - 1 : ℕ) : ℝ) / (2 * r - 1 : ℕ) + K := by
      have hr' := hratio
      rw [mul_div_assoc] at hr'
      exact add_le_add_right hr' K
    _ = (K : ℝ) + ((s - 1 : ℕ) : ℝ) / (2 * r - 1 : ℕ) := by ring

/-- The manuscript's `q, Δ` definitions give the denominator bound used by
the conditional-load estimate. -/
theorem separation_denominator_lower_bound (K r : ℕ) (hK : 1 ≤ K) (hr : 1 ≤ r) :
    K * (2 * r - 1) ≤ (K * (2 * r + 1) + 2 - 2 * K + 1) := by
  have hrel : 2 * r + 1 = (2 * r - 1) + 2 := by omega
  rw [hrel, Nat.mul_add]
  omega



end Erdos1016.Proof.ConditionalPenaltyBounds

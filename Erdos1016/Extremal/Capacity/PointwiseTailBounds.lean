import Erdos1016.Extremal.Capacity.Tail

set_option autoImplicit false

/-!
# Passing pointwise capacity estimates to tail suprema

The analytic graph argument naturally gives estimates for each normalized
initial-coverage value. This module isolates the order-theoretic step that
turns a uniform estimate on a full tail into the corresponding estimate for
`tailCapacity`.
-/

noncomputable section
namespace Erdos1016.Extremal

/-- The article's quartic scale dominates the `2^(8R)` threshold used by the
small-coverage branch, once its absolute constant satisfies `C ≥ 8`. -/
theorem quartic_scale_ge_small_coverage_threshold
    (C R : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R) :
    2 ^ (8 * R) ≤ 2 ^ (C * R ^ 4) := by
  have hRone : 1 ≤ R := by omega
  have hRpow : R ≤ R ^ 4 := by
    calc
      R = R ^ 1 := by simp
      _ ≤ R ^ 4 := Nat.pow_le_pow_right hRone (by omega)
  have hexp : 8 * R ≤ C * R ^ 4 := by
    have hmul : 8 * R ≤ 8 * (R ^ 4) := Nat.mul_le_mul_left 8 hRpow
    have hCmul : 8 * (R ^ 4) ≤ C * R ^ 4 := Nat.mul_le_mul_right (R ^ 4) hC
    omega
  exact Nat.pow_le_pow_right (by omega) hexp

/-- A uniform pointwise upper bound on all terms at or beyond `S` also bounds
their tail supremum. -/
theorem tailCapacity_le_of_pointwise_bound (S : ℕ) (B : ℝ)
    (hbound : ∀ r, S ≤ r → initialCapacityExcess r ≤ B) :
    tailCapacity S ≤ B := by
  unfold tailCapacity
  apply csSup_le
  · exact ⟨initialCapacityExcess S, ⟨S, le_rfl, rfl⟩⟩
  · rintro x ⟨r, hSr, rfl⟩
    exact hbound r hSr

/-- A pointwise near-halving estimate beyond the quartic scale immediately
implies the same estimate for the tail capacity. This is the final
supremum-passing step once the graph-theoretic estimate has been proved. -/
theorem tailCapacity_quartic_recurrence_of_pointwise
    (C R : ℕ) (ε : ℝ)
    (hpoint : ∀ r, 2 ^ (C * R ^ 4) ≤ r →
      initialCapacityExcess r ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R + ε) :
    tailCapacity (2 ^ (C * R ^ 4)) ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R + ε := by
  apply tailCapacity_le_of_pointwise_bound
  intro r hr
  exact hpoint r hr

/-- The first small-coverage branch in the paper's pointwise recurrence:
if the extremal initial interval ends before `2^(2R)`, its normalized excess
is already at most the additive error `2^(2-R)` at any sufficiently large
rank. -/
theorem initialCapacityExcess_le_error_of_small_coverage
    (R r : ℕ) (hR : 5 ≤ R) (hr : 2 ^ (8 * R) ≤ r)
    (hI : initialCapacity r < 2 ^ (2 * R) + 1) :
    initialCapacityExcess r ≤ (2 : ℝ) ^ (2 - (R : ℝ)) := by
  have hI' : initialCapacity r ≤ 2 ^ (2 * R) := by omega
  have hnumNat : initialCapacity r - 2 ≤ 2 ^ (2 * R) := by omega
  have hnumCast : ((initialCapacity r - 2 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (2 * R) := by exact_mod_cast hnumNat
  have hnum : (initialCapacity r : ℝ) - 2 ≤ (2 : ℝ) ^ (2 * R) := by
    simpa [Nat.cast_sub (by exact initialCapacity_two_le r)] using hnumCast
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hquot : initialCapacityExcess r ≤
      (2 : ℝ) ^ (2 * R) / (2 : ℝ) ^ r := by
    unfold initialCapacityExcess
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
  have hlarge : 3 * R ≤ r + 2 := by
    have htwoR : 3 * R ≤ 2 ^ (8 * R) := by
      have hpow : 8 * R + 1 ≤ 2 ^ (8 * R) := succ_le_two_pow (8 * R)
      omega
    omega
  have hexp : (2 * (R : ℝ)) ≤ (r : ℝ) + 2 - (R : ℝ) := by
    have hcast : (3 * R : ℝ) ≤ (r : ℝ) + 2 := by exact_mod_cast hlarge
    linarith
  have hpow : (2 : ℝ) ^ (2 * (R : ℝ)) ≤
      (2 : ℝ) ^ ((r : ℝ) + 2 - (R : ℝ)) :=
    (Real.rpow_le_rpow_left_iff (by norm_num : 1 < (2 : ℝ))).2 hexp
  have hnatpow : (2 : ℝ) ^ (2 * R) = (2 : ℝ) ^ (2 * (R : ℝ)) := by
    norm_cast
  have hdenpow : (2 : ℝ) ^ r = (2 : ℝ) ^ (r : ℝ) := by norm_cast
  have hadd : (2 : ℝ) ^ ((r : ℝ) + 2 - (R : ℝ)) =
      (2 : ℝ) ^ (r : ℝ) * (2 : ℝ) ^ (2 - (R : ℝ)) := by
    rw [show (r : ℝ) + 2 - (R : ℝ) = (r : ℝ) + (2 - (R : ℝ)) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hnumle : (2 : ℝ) ^ (2 * R) ≤
      (2 : ℝ) ^ r * (2 : ℝ) ^ (2 - (R : ℝ)) := by
    calc
      (2 : ℝ) ^ (2 * R) = (2 : ℝ) ^ (2 * (R : ℝ)) := hnatpow
      _ ≤ (2 : ℝ) ^ ((r : ℝ) + 2 - (R : ℝ)) := hpow
      _ = (2 : ℝ) ^ r * (2 : ℝ) ^ (2 - (R : ℝ)) := by
        rw [hdenpow, hadd]
  have hmul : (2 : ℝ) ^ (2 * R) / (2 : ℝ) ^ r ≤
      (2 : ℝ) ^ (2 - (R : ℝ)) :=
    (div_le_iff₀ hden).2 (by simpa [mul_comm] using hnumle)
  exact hquot.trans hmul

/-- The small-coverage branch at the exact quartic rank scale appearing in
§10. -/
theorem initialCapacityExcess_le_error_of_quartic_small_coverage
    (C R r : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hr : 2 ^ (C * R ^ 4) ≤ r)
    (hI : initialCapacity r < 2 ^ (2 * R) + 1) :
    initialCapacityExcess r ≤ (2 : ℝ) ^ (2 - (R : ℝ)) := by
  apply initialCapacityExcess_le_error_of_small_coverage R r hR
  · exact (quartic_scale_ge_small_coverage_threshold C R hC hR).trans hr
  · exact hI

end Erdos1016.Extremal

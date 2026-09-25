import Erdos1016.Nonbacktracking.Spectrum.NonrealSpectrum

set_option autoImplicit false

/-!
# The finite even-power spectral estimate

This proves the scalar finite-sum part of source (5.1). The eigenvalue list
must later be identified with the matrix trace, counting algebraic
multiplicities. That matrix theorem and the Perron/entropy lower bound are
NOT supplied or silently assumed by this module.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance evenSpectrumDecidable (p : Prop) : Decidable p := Classical.propDecidable p



theorem even_power_re_nonneg_of_real {z : ℂ} (hz : z.im = 0) (k : ℕ) :
    0 ≤ (z ^ (2 * k)).re := by
  have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [heq, ← Complex.ofReal_pow, Complex.ofReal_re, Nat.mul_comm 2 k, pow_mul]
  exact sq_nonneg _

theorem even_power_re_ge_neg {z : ℂ} (hz : Complex.normSq z ≤ 2) (k : ℕ) :
    -(2 : ℝ) ^ k ≤ (z ^ (2 * k)).re := by
  have hsq : (z ^ (2 * k)).re * (z ^ (2 * k)).re ≤ (2 : ℝ) ^ (2 * k) := by
    calc
      _ ≤ Complex.normSq (z ^ (2 * k)) := Complex.re_sq_le_normSq _
      _ = Complex.normSq z ^ (2 * k) := map_pow Complex.normSq z (2 * k)
      _ ≤ 2 ^ (2 * k) := by
        have hnonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
        gcongr
  have hpow : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  rw [hpow] at hsq
  have hpos : 0 ≤ (2 : ℝ) ^ k := by positivity
  nlinarith [sq_nonneg ((z ^ (2 * k)).re + (2 : ℝ) ^ k)]





end Erdos1016.Nonbacktracking

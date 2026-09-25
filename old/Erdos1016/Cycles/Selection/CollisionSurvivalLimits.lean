import Erdos1016.Cycles.Selection.ReturnSurvivalLimits

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.CollisionSurvivalLimits

open Erdos1016.Proof.CutoffLimits
open Erdos1016.Proof.ReturnSurvivalLimits

def collisionError (s : ℕ) (L : ℕ) : ℝ :=
  (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s

/-- For the paper's cutoffs, the finite collision error is dominated by the
external-return suffix budget, which already tends to zero. -/
theorem cutoff_collision_error_tendsto_zero
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => collisionError (cutoffS (x j)) (cutoffL σ (x j)))
      atTop (𝓝 0) := by
  have hreturn := cutoff_return_error_tendsto_zero σ hσ hσ20 x hx
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ collisionError (cutoffS (x j)) (cutoffL σ (x j)) := by
    filter_upwards with j
    unfold collisionError
    positivity
  have hle : ∀ᶠ j in atTop,
      collisionError (cutoffS (x j)) (cutoffL σ (x j)) ≤
        Real.exp (suffixErrorLogScale (cutoffQ σ (x j))
          (cutoffS (x j)) (cutoffL σ (x j))) := by
    filter_upwards with j
    have hLnat : 1 ≤ cutoffL σ (x j) := by
      dsimp [cutoffL, largestOddCutoff]
      omega
    have hL : 1 ≤ (cutoffL σ (x j) : ℝ) := by exact_mod_cast hLnat
    have hpow : 1 ≤ (2 : ℝ) ^ cutoffQ σ (x j) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hfactor : 1 ≤ 2 * (2 : ℝ) ^ cutoffQ σ (x j) *
        (cutoffL σ (x j) : ℝ) := by nlinarith
    have hbase : 0 ≤ collisionError (cutoffS (x j)) (cutoffL σ (x j)) := by
      unfold collisionError
      positivity
    have hmul := mul_le_mul_of_nonneg_left hfactor hbase
    have hexp := exp_suffixErrorLogScale_eq
      (cutoffQ σ (x j)) (cutoffS (x j)) (cutoffL σ (x j)) (by omega)
    calc
      collisionError (cutoffS (x j)) (cutoffL σ (x j)) =
          collisionError (cutoffS (x j)) (cutoffL σ (x j)) * 1 := by ring
      _ ≤ collisionError (cutoffS (x j)) (cutoffL σ (x j)) *
          (2 * (2 : ℝ) ^ cutoffQ σ (x j) *
            (cutoffL σ (x j) : ℝ)) := hmul
      _ = (9 / 2 : ℝ) * (2 : ℝ) ^ cutoffQ σ (x j) *
          (cutoffL σ (x j) : ℝ) ^ 3 * (1 / 2 : ℝ) ^ cutoffS (x j) := by
            unfold collisionError
            ring
      _ = Real.exp (suffixErrorLogScale (cutoffQ σ (x j))
          (cutoffS (x j)) (cutoffL σ (x j))) := hexp.symm
  exact squeeze_zero' hnonneg hle hreturn



end Erdos1016.Proof.CollisionSurvivalLimits

end

import Erdos1016.Cycles.Selection.CutoffLimits

set_option autoImplicit false

/-!
# Section 6 accepted-mass loss under the Section 7 parameters

The finite return-filter estimate loses a relative mass bounded by
`(9/2) * 2^q * L^3 * 2^-s`. This file proves that this error tends to zero
for the paper's actual choices of `q`, `s`, and `L`. Consequently, whenever
the trace lower bound is positive, the accepted family retains asymptotically
all of the short-cycle mass.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.ReturnSurvivalLimits

open Erdos1016.Proof.CutoffLimits

/-- Logarithmic scale of the Section 6 suffix-error factor. -/
def suffixErrorLogScale (q s : ℕ) (L : ℕ) : ℝ :=
  Real.log (9 / 2 : ℝ) + (q : ℝ) * Real.log 2 -
    (s : ℝ) * Real.log 2 + 3 * Real.log (L : ℝ)

/-- Exponentiating the logarithmic scale recovers the literal Section 6
rejected-mass factor. -/
theorem exp_suffixErrorLogScale_eq (q s L : ℕ) (hL : 0 < L) :
    Real.exp (suffixErrorLogScale q s L) =
      (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s := by
  have hq : Real.exp ((q : ℝ) * Real.log 2) = (2 : ℝ) ^ q := by
    rw [← Real.log_pow 2 q]
    exact Real.exp_log (by positivity)
  have hs : Real.exp (-((s : ℝ) * Real.log 2)) =
      (1 / 2 : ℝ) ^ s := by
    have hlog : Real.log ((1 / 2 : ℝ) ^ s) =
        -((s : ℝ) * Real.log 2) := by
      rw [Real.log_pow]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [hhalf, Real.log_inv]
      ring
    rw [← hlog]
    exact Real.exp_log (by positivity)
  have hLlog : Real.exp (3 * Real.log (L : ℝ)) = (L : ℝ) ^ 3 := by
    have hlog : Real.log ((L : ℝ) ^ 3) = 3 * Real.log (L : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [← hlog]
    exact Real.exp_log (by positivity)
  have hconst : Real.exp (Real.log (9 / 2 : ℝ)) = 9 / 2 :=
    Real.exp_log (by norm_num)
  unfold suffixErrorLogScale
  rw [show Real.log (9 / 2 : ℝ) + (q : ℝ) * Real.log 2 -
      (s : ℝ) * Real.log 2 + 3 * Real.log (L : ℝ) =
      (Real.log (9 / 2 : ℝ) + (q : ℝ) * Real.log 2) +
        (-((s : ℝ) * Real.log 2) + 3 * Real.log (L : ℝ)) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, hconst, hq, hs, hLlog]
  ring

theorem normalized_suffixErrorLogScale_tendsto
    (x : ℕ → ℝ) (q s L : ℕ → ℕ) (Q S : ℝ)
    (hx : Tendsto x atTop atTop)
    (hq : Tendsto (fun j => (q j : ℝ) / x j) atTop (𝓝 Q))
    (hs : Tendsto (fun j => (s j : ℝ) / x j) atTop (𝓝 S))
    (hL : Tendsto (fun j => Real.log (L j : ℝ) / x j) atTop (𝓝 0)) :
    Tendsto (fun j => suffixErrorLogScale (q j) (s j) (L j) / x j)
      atTop (𝓝 ((Q - S) * Real.log 2)) := by
  have hconstant : Tendsto (fun j => Real.log (9 / 2 : ℝ) / x j)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have hmain : Tendsto (fun j =>
      ((q j : ℝ) / x j - (s j : ℝ) / x j) * Real.log 2)
      atTop (𝓝 ((Q - S) * Real.log 2)) := by
    have hsub := (hq.sub hs).const_mul (Real.log 2)
    convert hsub using 1 <;> ext j <;> ring
  have hlast : Tendsto (fun j => 3 * (Real.log (L j : ℝ) / x j))
      atTop (𝓝 0) := by simpa using hL.const_mul (3 : ℝ)
  have htotal := (hconstant.add hmain).add hlast
  have heq : (fun j => suffixErrorLogScale (q j) (s j) (L j) / x j) =
      fun j => Real.log (9 / 2 : ℝ) / x j +
        ((q j : ℝ) / x j - (s j : ℝ) / x j) * Real.log 2 +
        3 * (Real.log (L j : ℝ) / x j) := by
    funext j
    unfold suffixErrorLogScale
    ring
  rw [heq]
  simpa using htotal

theorem exp_suffixErrorLogScale_tendsto_zero
    (x : ℕ → ℝ) (q s L : ℕ → ℕ) (c : ℝ)
    (hx : Tendsto x atTop atTop)
    (hscale : Tendsto
      (fun j => suffixErrorLogScale (q j) (s j) (L j) / x j)
      atTop (𝓝 c)) (hc : c < 0) :
    Tendsto (fun j => Real.exp (suffixErrorLogScale (q j) (s j) (L j)))
      atTop (𝓝 0) := by
  have hhalf : c < c / 2 := by linarith
  have heventually : ∀ᶠ j in atTop,
      suffixErrorLogScale (q j) (s j) (L j) / x j < c / 2 :=
    hscale.eventually (Iio_mem_nhds hhalf)
  have hxpos : ∀ᶠ j in atTop, 0 < x j := hx.eventually_gt_atTop 0
  have hbound : ∀ᶠ j in atTop,
      Real.exp (suffixErrorLogScale (q j) (s j) (L j)) ≤
        Real.exp ((c / 2) * x j) := by
    filter_upwards [heventually, hxpos] with j hscalej hxj
    apply Real.exp_le_exp.mpr
    exact (div_lt_iff₀ hxj).1 hscalej |>.le
  have hnegative : c / 2 < 0 := by linarith
  have hlin : Tendsto (fun j => (c / 2) * x j) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop hnegative hx
  have hexp : Tendsto (fun j => Real.exp ((c / 2) * x j)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  apply squeeze_zero' (Filter.Eventually.of_forall fun j => (Real.exp_pos _).le)
    hbound hexp

/-- The paper's `σ<1/20` choice makes the Section 6 rejected-mass budget
vanish for the exact floor/ceiling cutoffs. -/
theorem cutoff_return_error_tendsto_zero
    (σ : ℝ) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => Real.exp (suffixErrorLogScale
      (cutoffQ σ (x j)) (cutoffS (x j)) (cutoffL σ (x j))))
      atTop (𝓝 0) := by
  have hscale := normalized_suffixErrorLogScale_tendsto x
      (fun j => cutoffQ σ (x j)) (fun j => cutoffS (x j))
      (fun j => cutoffL σ (x j)) (20 * σ ^ 2) (1 / 4) hx
      (cutoffQ_ratio_tendsto σ hσ x hx)
      (cutoffS_ratio_tendsto x hx)
      (cutoffL_log_over_x_tendsto_zero σ hσ x hx)
  apply exp_suffixErrorLogScale_tendsto_zero x
    (fun j => cutoffQ σ (x j)) (fun j => cutoffS (x j))
    (fun j => cutoffL σ (x j))
    ((20 * σ ^ 2 - 1 / 4) * Real.log 2) hx hscale
  have hsq : σ ^ 2 < (1 / 20 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (σ - 1 / 20)]
  have hcoeff : 20 * σ ^ 2 - 1 / 4 < 0 := by nlinarith
  exact mul_neg_of_neg_of_pos hcoeff (Real.log_pos (by norm_num))

end Erdos1016.Proof.ReturnSurvivalLimits

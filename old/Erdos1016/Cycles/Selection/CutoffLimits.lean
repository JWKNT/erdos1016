import Erdos1016.Probability.Avoidance.ConditionalLoadDecay

set_option autoImplicit false

/-!
# Elementary Section 7 parameter limits

There is no general floor/ceiling asymptotic module in the existing
development. This file starts the actual parameter-sequence audit by proving
the floor cutoffs and the moment-order limit directly from the paper's
definitions.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.CutoffLimits

def cutoffD (x : ℝ) : ℕ := Nat.floor (x / 2)
def cutoffS (x : ℝ) : ℕ := (cutoffD x - 1) / 2
def momentK (σ x : ℝ) : ℕ := 2 * Nat.ceil (5 * σ * Real.sqrt x)
def largestOddCutoff (t : ℝ) : ℕ := 2 * Nat.floor ((t - 1) / 2) + 1
def cutoffL (σ x : ℝ) : ℕ := largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt x))
def cutoffRc (σ x : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2
    (4 * (momentK σ x : ℝ) * (cutoffL σ x : ℝ) + 1))
def cutoffQ (σ x : ℝ) : ℕ := momentK σ x * (2 * cutoffRc σ x + 1) + 2
def cutoffDelta (σ x : ℝ) : ℕ := cutoffQ σ x - 2 * momentK σ x + 1
def cutoffPenalty (σ x : ℝ) : ℝ :=
  ((cutoffS x - 1 : ℕ) : ℝ) / (2 * cutoffRc σ x - 1 : ℕ) / x

private theorem natCeil_le_add_one (x : ℝ) (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 := by
  by_cases hz : Nat.ceil x = 0
  · rw [hz, Nat.cast_zero]
    linarith
  · have hn : 1 ≤ Nat.ceil x := by omega
    have hxpred : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
      by_contra h
      have hle : x ≤ ((Nat.ceil x - 1 : ℕ) : ℝ) := le_of_not_gt h
      have hceil : Nat.ceil x ≤ Nat.ceil x - 1 := (Nat.ceil_le).2 hle
      omega
    have hcast : ((Nat.ceil x - 1 : ℕ) : ℝ) + 1 = (Nat.ceil x : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hn
    linarith

/-- Rounding down to the largest odd integer loses less than two. -/
theorem largestOddCutoff_bounds (t : ℝ) (ht : 4 ≤ t) :
    t - 2 < (largestOddCutoff t : ℝ) ∧ (largestOddCutoff t : ℝ) ≤ t := by
  have hfloorLower : (t - 1) / 2 <
      (Nat.floor ((t - 1) / 2) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfloorUpper : (Nat.floor ((t - 1) / 2) : ℝ) ≤ (t - 1) / 2 :=
    Nat.floor_le (by linarith)
  constructor
  · dsimp [largestOddCutoff]
    exact_mod_cast (by nlinarith [hfloorLower] :
      t - 2 < 2 * (Nat.floor ((t - 1) / 2) : ℝ) + 1)
  · dsimp [largestOddCutoff]
    push_cast
    nlinarith [hfloorUpper]

/-- The paper's largest-odd cutoff has logarithm asymptotic to
`σ sqrt(x) log 2`; only `σ>0` is needed here. -/
theorem cutoffL_log_sqrt_tendsto (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => Real.log (cutoffL σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 (σ * Real.log 2)) := by
  have hroot : Tendsto (fun j => (x j) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
  have hrootSqrt : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using hroot
  have hexp : Tendsto (fun j => σ * Real.sqrt (x j)) atTop atTop :=
    by simpa [mul_comm] using hrootSqrt.atTop_mul_const hσ
  have hT : Tendsto (fun j => (2 : ℝ) ^ (σ * Real.sqrt (x j))) atTop atTop := by
    have hExp : Tendsto (fun j => Real.exp (Real.log 2 * (σ * Real.sqrt (x j))))
        atTop atTop := by
      have hlin : Tendsto (fun j => Real.log 2 * (σ * Real.sqrt (x j))) atTop atTop :=
        (tendsto_const_mul_atTop_of_pos (Real.log_pos (by norm_num))).2 hexp
      exact Real.tendsto_exp_atTop.comp hlin
    have heq : (fun j => (2 : ℝ) ^ (σ * Real.sqrt (x j))) =
        fun j => Real.exp (Real.log 2 * (σ * Real.sqrt (x j))) := by
      funext j
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [heq]
    exact hExp
  have hlarge : ∀ᶠ j in atTop, 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) :=
    hT.eventually_ge_atTop 4
  have hinvRoot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hrootSqrt.inv_tendsto_atTop
  have hlow : Tendsto
      (fun j => σ * Real.log 2 - Real.log 2 * (Real.sqrt (x j))⁻¹)
      atTop (𝓝 (σ * Real.log 2)) := by
    have hconst : Tendsto (fun _ : ℕ => σ * Real.log 2) atTop
        (𝓝 (σ * Real.log 2)) := tendsto_const_nhds
    have hmul : Tendsto (fun j => Real.log 2 * (Real.sqrt (x j))⁻¹)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := Real.log 2)).mul hinvRoot
    simpa using hconst.sub hmul
  have hhigh : Tendsto (fun _ : ℕ => σ * Real.log 2)
      atTop (𝓝 (σ * Real.log 2)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [hlarge, hx.eventually_gt_atTop 0] with j hTj hxj
    have hbounds := largestOddCutoff_bounds ((2 : ℝ) ^ (σ * Real.sqrt (x j))) hTj
    have hLpos : 0 < (cutoffL σ (x j) : ℝ) := by
      have hodd : 1 ≤ largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j))) := by
        dsimp [largestOddCutoff]
        omega
      exact_mod_cast hodd
    have hsqrtpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hxj
    have hlogL : Real.log ((2 : ℝ) ^ (σ * Real.sqrt (x j)) / 2) ≤
        Real.log (cutoffL σ (x j) : ℝ) := by
      apply Real.log_le_log (by positivity) ?_
      have : (2 : ℝ) ^ (σ * Real.sqrt (x j)) / 2 ≤
          (largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j)) : ℝ) : ℝ) := by
        have ht := hbounds.1.le
        nlinarith
      simpa [cutoffL] using this
    have hlogpow : Real.log ((2 : ℝ) ^ (σ * Real.sqrt (x j))) =
        (σ * Real.sqrt (x j)) * Real.log 2 :=
      Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
    rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0), hlogpow] at hlogL
    rw [le_div_iff₀ hsqrtpos]
    field_simp [ne_of_gt hsqrtpos]
    nlinarith [hlogL]
  · filter_upwards [hlarge, hx.eventually_gt_atTop 0] with j hTj hxj
    have hbounds := largestOddCutoff_bounds ((2 : ℝ) ^ (σ * Real.sqrt (x j))) hTj
    have hLpos : 0 < (cutoffL σ (x j) : ℝ) := by
      have hodd : 1 ≤ largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j))) := by
        dsimp [largestOddCutoff]
        omega
      exact_mod_cast hodd
    have hlogL : Real.log (cutoffL σ (x j) : ℝ) ≤
        Real.log ((2 : ℝ) ^ (σ * Real.sqrt (x j))) :=
      Real.log_le_log hLpos (by simpa [cutoffL] using hbounds.2)
    have hlogpow : Real.log ((2 : ℝ) ^ (σ * Real.sqrt (x j))) =
        (σ * Real.sqrt (x j)) * Real.log 2 :=
      Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
    rw [hlogpow] at hlogL
    have hsqrtpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hxj
    rw [div_le_iff₀ hsqrtpos]
    nlinarith [hlogL]

/-- The actual L cutoff contributes only `o(x)` to the logarithm in `d_*`. -/
theorem cutoffL_log_over_x_tendsto_zero (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => Real.log (cutoffL σ (x j) : ℝ) / x j)
      atTop (𝓝 0) := by
  have hL := cutoffL_log_sqrt_tendsto σ hσ x hx
  have hroot : Tendsto (fun j => (x j) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
  have hrootSqrt : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using hroot
  have hinvRoot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hrootSqrt.inv_tendsto_atTop
  have hratio : Tendsto (fun j => Real.sqrt (x j) / x j) atTop (𝓝 0) := by
    have hpos : ∀ᶠ j in atTop, 0 < x j := hx.eventually_gt_atTop 0
    have heq : (fun j => Real.sqrt (x j) / x j) =ᶠ[atTop]
        fun j => (Real.sqrt (x j))⁻¹ := by
      filter_upwards [hpos] with j hj
      have hs : Real.sqrt (x j) * Real.sqrt (x j) = x j := by
        nlinarith [Real.sq_sqrt hj.le]
      calc
        Real.sqrt (x j) / x j = Real.sqrt (x j) /
            (Real.sqrt (x j) * Real.sqrt (x j)) := by rw [hs]
        _ = (Real.sqrt (x j))⁻¹ := by
          field_simp [ne_of_gt (Real.sqrt_pos.2 hj)]
    exact hinvRoot.congr' heq.symm
  have hprod : Tendsto
      (fun j => (Real.log (cutoffL σ (x j) : ℝ) / Real.sqrt (x j)) *
        (Real.sqrt (x j) / x j)) atTop (𝓝 0) := by
    simpa using hL.mul hratio
  have heq : (fun j => (Real.log (cutoffL σ (x j) : ℝ) / Real.sqrt (x j)) *
      (Real.sqrt (x j) / x j)) =ᶠ[atTop]
      fun j => Real.log (cutoffL σ (x j) : ℝ) / x j := by
    filter_upwards [hx.eventually_gt_atTop 0] with j hj
    have hsqrt : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hj)
    field_simp [ne_of_gt hj, hsqrt]
  exact hprod.congr' heq

/-- The logarithmic critical-radius term differs from `log₂ L` by at most
the `log₂ K` contribution and a fixed additive constant. -/
theorem logb_four_mul_KL_add_one_bounds (K L : ℝ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) :
    Real.logb 2 L ≤ Real.logb 2 (4 * K * L + 1) ∧
      Real.logb 2 (4 * K * L + 1) ≤
        Real.logb 2 5 + Real.logb 2 K + Real.logb 2 L := by
  have hKpos : 0 < K := by linarith
  have hLpos : 0 < L := by linarith
  have hargpos : 0 < 4 * K * L + 1 := by positivity
  have hKL : 1 ≤ K * L := by nlinarith
  have harglow : L ≤ 4 * K * L + 1 := by nlinarith [hK, hL]
  have hargupper : 4 * K * L + 1 ≤ 5 * K * L := by nlinarith [hKL]
  constructor
  · exact Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ)) hLpos harglow
  · calc
      Real.logb 2 (4 * K * L + 1) ≤ Real.logb 2 (5 * K * L) :=
        Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ)) hargpos
          (by nlinarith [hargupper])
      _ = Real.logb 2 5 + Real.logb 2 K + Real.logb 2 L := by
        rw [show 5 * K * L = 5 * (K * L) by ring,
          Real.logb_mul (by norm_num : (5 : ℝ) ≠ 0)
            (by positivity : K * L ≠ 0),
          Real.logb_mul (ne_of_gt hKpos) (ne_of_gt hLpos)]
        ring_nf

/-- The first source cutoff satisfies `floor(x/2)/x → 1/2`. -/
theorem cutoffD_ratio_tendsto (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (cutoffD (x j) : ℝ) / x j) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hrecip : Tendsto (fun j => (x j)⁻¹) atTop (𝓝 0) := hx.inv_tendsto_atTop
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun j => (1 / 2 : ℝ) - (x j)⁻¹) atTop (𝓝 (1 / 2 : ℝ)) :=
    by simpa using hconst.sub hrecip
  have hhigh : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hfloor : x j / 2 - 1 ≤ (cutoffD (x j) : ℝ) := by
      have h := Nat.lt_floor_add_one (x j / 2)
      dsimp [cutoffD]
      linarith
    have hinv : x j * (x j)⁻¹ = 1 := by field_simp [ne_of_gt hxj]
    rw [le_div_iff₀ hxj]
    nlinarith [hfloor, hinv]
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hfloor : (cutoffD (x j) : ℝ) ≤ x j / 2 := by
      dsimp [cutoffD]
      exact Nat.floor_le (by linarith : 0 ≤ x j / 2)
    have hinv : x j * (x j)⁻¹ = 1 := by field_simp [ne_of_gt hxj]
    rw [div_le_iff₀ hxj]
    nlinarith [hfloor, hinv]

/-- The second nested floor in the paper gives `s/x → 1/4`. -/
theorem cutoffS_ratio_tendsto (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (cutoffS (x j) : ℝ) / x j) atTop (𝓝 (1 / 4 : ℝ)) := by
  have hD := cutoffD_ratio_tendsto x hx
  have hrecip : Tendsto (fun j => (x j)⁻¹) atTop (𝓝 0) := hx.inv_tendsto_atTop
  have hlow : Tendsto
      (fun j => (cutoffD (x j) : ℝ) / (2 * x j) - 1 / x j)
      atTop (𝓝 (1 / 4 : ℝ)) := by
    have hfirst : Tendsto
        (fun j => (cutoffD (x j) : ℝ) / x j / 2) atTop (𝓝 (1 / 4 : ℝ)) := by
      convert hD.div_const 2 using 1 <;> norm_num
    have hsecond := hfirst.sub hrecip
    convert hsecond using 1 <;> norm_num <;> ring_nf
  have hhigh : Tendsto
      (fun j => (cutoffD (x j) : ℝ) / (2 * x j)) atTop (𝓝 (1 / 4 : ℝ)) := by
    have hfirst : Tendsto
        (fun j => (cutoffD (x j) : ℝ) / x j / 2) atTop (𝓝 (1 / 4 : ℝ)) := by
      convert hD.div_const 2 using 1 <;> norm_num
    convert hfirst using 1 <;> ext j <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [hx.eventually_ge_atTop 4] with j hxj
    have hxpos : 0 < x j := by linarith
    have hDlarge : 2 ≤ cutoffD (x j) := by
      dsimp [cutoffD]
      exact Nat.le_floor (by linarith : (2 : ℝ) ≤ x j / 2)
    have hdivLower : cutoffD (x j) - 2 ≤ 2 * cutoffS (x j) := by
      dsimp [cutoffS]
      omega
    have hcast : ((cutoffD (x j) - 2 : ℕ) : ℝ) ≤
        2 * (cutoffS (x j) : ℝ) := by exact_mod_cast hdivLower
    rw [Nat.cast_sub hDlarge] at hcast
    norm_num at hcast
    have htarget : ((cutoffD (x j) : ℝ) - 2) / (2 * x j) ≤
        (cutoffS (x j) : ℝ) / x j := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * x j)
        (by positivity : 0 < x j)).2
      nlinarith [hcast]
    have heq : (cutoffD (x j) : ℝ) / (2 * x j) - 1 / x j =
        ((cutoffD (x j) : ℝ) - 2) / (2 * x j) := by
      field_simp [ne_of_gt hxpos]
      ring
    have hlin : (cutoffD (x j) : ℝ) / (2 * x j) - 1 / x j ≤
        (cutoffS (x j) : ℝ) / x j := by rw [heq]; exact htarget
    nlinarith [hlin]
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hdivUpper : 2 * cutoffS (x j) ≤ cutoffD (x j) := by
      dsimp [cutoffS]
      omega
    have hcast : 2 * (cutoffS (x j) : ℝ) ≤ (cutoffD (x j) : ℝ) := by
      exact_mod_cast hdivUpper
    apply (div_le_div_iff₀ (by positivity : 0 < x j)
      (by positivity : 0 < 2 * x j)).2
    nlinarith [hcast]

/-- With `K=2 ceil(5σ√x)`, the MANY-moment order is sublinear in `x`. -/
theorem momentK_ratio_tendsto_zero (σ : ℝ) (hσ : 0 ≤ σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (momentK σ (x j) : ℝ) / x j) atTop (𝓝 0) := by
  have hroot : Tendsto (fun j => (x j) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
  have hrootSqrt : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using hroot
  have hinvRoot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hrootSqrt.inv_tendsto_atTop
  have hinvX : Tendsto (fun j => (x j)⁻¹) atTop (𝓝 0) := hx.inv_tendsto_atTop
  have hrootRatio : Tendsto (fun j => Real.sqrt (x j) / x j) atTop (𝓝 0) := by
    have hpos : ∀ᶠ j in atTop, 0 < x j := hx.eventually_gt_atTop 0
    have heq : (fun j => Real.sqrt (x j) / x j) =ᶠ[atTop]
        fun j => (Real.sqrt (x j))⁻¹ := by
      filter_upwards [hpos] with j hj
      have hs : Real.sqrt (x j) * Real.sqrt (x j) = x j := by
        nlinarith [Real.sq_sqrt hj.le]
      have hrootpos : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hj)
      calc
        Real.sqrt (x j) / x j = Real.sqrt (x j) /
            (Real.sqrt (x j) * Real.sqrt (x j)) := by rw [hs]
        _ = (Real.sqrt (x j))⁻¹ := by field_simp
    exact hinvRoot.congr' heq.symm
  have hupper : Tendsto (fun j => 10 * σ * (Real.sqrt (x j) / x j) + 2 / x j)
      atTop (𝓝 0) := by
    simpa using (hrootRatio.const_mul (10 * σ)).add (hinvX.const_mul 2)
  apply squeeze_zero'
    (show ∀ᶠ j in atTop, 0 ≤ (momentK σ (x j) : ℝ) / x j from ?_)
    ?_ hupper
  · filter_upwards [hx.eventually_gt_atTop 0] with j hj
    exact div_nonneg (Nat.cast_nonneg _) hj.le
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hceilLower : 5 * σ * Real.sqrt (x j) ≤
        (Nat.ceil (5 * σ * Real.sqrt (x j)) : ℝ) := Nat.le_ceil _
    have hceilUpper := natCeil_le_add_one (5 * σ * Real.sqrt (x j)) (by positivity)
    have hKUpper : (momentK σ (x j) : ℝ) ≤ 10 * σ * Real.sqrt (x j) + 2 := by
      dsimp [momentK]
      push_cast
      nlinarith [hceilUpper]
    rw [div_le_iff₀ hxj]
    field_simp [ne_of_gt hxj]
    nlinarith [hKUpper]

/-- Since `K=o(x)` while `x` grows, its base-two logarithm is negligible
on the square-root scale used for the critical radius. -/
theorem momentK_logb_sqrt_ratio_tendsto_zero (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto
      (fun j => Real.logb 2 (momentK σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 0) := by
  have hK := momentK_ratio_tendsto_zero σ hσ.le x hx
  have hroot : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
    simpa only [Real.sqrt_eq_rpow] using hp
  have hlogx : Tendsto (fun j => Real.log (x j) / Real.sqrt (x j))
      atTop (𝓝 0) := by
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hsmall' : Tendsto (fun y : ℝ => Real.log y / Real.sqrt y)
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using hsmall
    exact hsmall'.comp hx
  have hlogbX : Tendsto (fun j => Real.logb 2 (x j) / Real.sqrt (x j))
      atTop (𝓝 0) := by
    have h := hlogx.div_const (Real.log 2)
    convert h using 1
    · ext j
      simp only [Real.logb]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      <;> ring
    · simp
  apply squeeze_zero'
    (show ∀ᶠ j in atTop,
      0 ≤ Real.logb 2 (momentK σ (x j) : ℝ) / Real.sqrt (x j) from ?_)
    ?_ hlogbX
  · filter_upwards [hx.eventually_gt_atTop 0] with j hj
    have hs : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hj
    have hc : 1 ≤ (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 1 ≤ 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    exact div_nonneg (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hc) hs.le
  · filter_upwards [hx.eventually_gt_atTop 0,
      hK.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with j hj hKsmall
    have hs : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hj
    have hKpos : 0 < (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 0 < 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    have hKle : (momentK σ (x j) : ℝ) ≤ x j := by
      rw [div_lt_iff₀ hj] at hKsmall
      linarith
    have hlog : Real.logb 2 (momentK σ (x j) : ℝ) ≤ Real.logb 2 (x j) :=
      Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ)) hKpos hKle
    exact div_le_div_of_nonneg_right hlog hs.le

/-- The paper's actual critical-radius choice satisfies `r_c/sqrt(x) → σ`.
The only nonconstant error in the logarithm is `log₂ K`, already shown
negligible by `momentK_logb_sqrt_ratio_tendsto_zero`. -/
theorem cutoffRc_sqrt_ratio_tendsto (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (cutoffRc σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 σ) := by
  have hL := cutoffL_log_sqrt_tendsto σ hσ x hx
  have hKlog := momentK_logb_sqrt_ratio_tendsto_zero σ hσ x hx
  have hroot : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
    simpa only [Real.sqrt_eq_rpow] using hp
  have hσroot : Tendsto (fun j => σ * Real.sqrt (x j)) atTop atTop := by
    have hh := hroot.atTop_mul_const hσ
    simpa [mul_comm] using hh
  have hlargeExp : ∀ᶠ j in atTop, 2 ≤ σ * Real.sqrt (x j) :=
    hσroot.eventually_ge_atTop 2
  have hinvroot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hroot.inv_tendsto_atTop
  have hlogbL : Tendsto
      (fun j => Real.logb 2 (cutoffL σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 σ) := by
    have h := hL.div_const (Real.log 2)
    convert h using 1
    · ext j
      simp only [Real.logb]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      <;> ring
    · field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      <;> ring
  have hfive : Tendsto (fun j => Real.logb 2 5 * (Real.sqrt (x j))⁻¹)
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hinvroot
  have hlower : Tendsto
      (fun j => Real.logb 2 (cutoffL σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 σ) := hlogbL
  have hupper : Tendsto
      (fun j => Real.logb 2 5 * (Real.sqrt (x j))⁻¹ +
        Real.logb 2 (momentK σ (x j) : ℝ) / Real.sqrt (x j) +
        Real.logb 2 (cutoffL σ (x j) : ℝ) / Real.sqrt (x j) +
        (Real.sqrt (x j))⁻¹)
      atTop (𝓝 σ) := by
    simpa using (((hfive.add hKlog).add hlogbL).add hinvroot)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hx.eventually_gt_atTop 0, hlargeExp] with j hj hexp
    have hs : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hj
    have hT : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) := by
      exact le_trans (by norm_num : (4 : ℝ) ≤ 2 ^ (2 : ℝ))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
    have hLbound := largestOddCutoff_bounds _ hT
    have hLpos : 0 < (cutoffL σ (x j) : ℝ) := by
      have hodd : 1 ≤ largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j))) := by
        dsimp [largestOddCutoff]
        omega
      exact_mod_cast hodd
    have hKpos : 0 < (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 0 < 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    have hKone : 1 ≤ (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 1 ≤ 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    have harg : (cutoffL σ (x j) : ℝ) ≤
        4 * (momentK σ (x j) : ℝ) * (cutoffL σ (x j) : ℝ) + 1 := by
      nlinarith [hKone, hLpos]
    have hlog := Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ))
      hLpos harg
    have hceil : Real.logb 2
        (4 * (momentK σ (x j) : ℝ) * (cutoffL σ (x j) : ℝ) + 1) ≤
        (cutoffRc σ (x j) : ℝ) := Nat.le_ceil _
    exact div_le_div_of_nonneg_right (hlog.trans hceil) hs.le
  · filter_upwards [hx.eventually_gt_atTop 0, hlargeExp] with j hj hexp
    have hs : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hj
    have hT : 4 ≤ (2 : ℝ) ^ (σ * Real.sqrt (x j)) := by
      exact le_trans (by norm_num : (4 : ℝ) ≤ 2 ^ (2 : ℝ))
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
    have hLbound := largestOddCutoff_bounds _ hT
    have hLpos : 0 < (cutoffL σ (x j) : ℝ) := by
      have hodd : 1 ≤ largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j))) := by
        dsimp [largestOddCutoff]
        omega
      exact_mod_cast hodd
    have hKpos : 0 < (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 0 < 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    have hKone : 1 ≤ (momentK σ (x j) : ℝ) := by
      have hceil : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) :=
        (Nat.one_le_ceil_iff).2 (by positivity)
      dsimp [momentK]
      exact_mod_cast (by omega : 1 ≤ 2 * Nat.ceil (5 * σ * Real.sqrt (x j)))
    have hLone : 1 ≤ (cutoffL σ (x j) : ℝ) := by
      have hodd : 1 ≤ largestOddCutoff ((2 : ℝ) ^ (σ * Real.sqrt (x j))) := by
        dsimp [largestOddCutoff]
        omega
      exact_mod_cast hodd
    have hlogbounds := logb_four_mul_KL_add_one_bounds
      (momentK σ (x j) : ℝ) (cutoffL σ (x j) : ℝ) hKone hLone
    have hceil : (cutoffRc σ (x j) : ℝ) ≤
        Real.logb 2 (4 * (momentK σ (x j) : ℝ) *
          (cutoffL σ (x j) : ℝ) + 1) + 1 :=
      natCeil_le_add_one _ (by
        have hKL : 1 ≤ (momentK σ (x j) : ℝ) *
            (cutoffL σ (x j) : ℝ) := by
          nlinarith [mul_nonneg
            (show 0 ≤ (momentK σ (x j) : ℝ) - 1 by linarith)
            (show 0 ≤ (cutoffL σ (x j) : ℝ) - 1 by linarith)]
        have harg : 1 < 4 * (momentK σ (x j) : ℝ) *
            (cutoffL σ (x j) : ℝ) + 1 := by nlinarith [hKL]
        have hpos := Real.logb_pos (by norm_num : 1 < (2 : ℝ)) harg
        exact hpos.le)
    have hup : (cutoffRc σ (x j) : ℝ) ≤
        Real.logb 2 5 + Real.logb 2 (momentK σ (x j) : ℝ) +
          Real.logb 2 (cutoffL σ (x j) : ℝ) + 1 := by
      linarith [hceil, hlogbounds.2]
    have hnormalized : (cutoffRc σ (x j) : ℝ) / Real.sqrt (x j) ≤
        Real.logb 2 5 * (Real.sqrt (x j))⁻¹ +
          Real.logb 2 (momentK σ (x j) : ℝ) / Real.sqrt (x j) +
          Real.logb 2 (cutoffL σ (x j) : ℝ) / Real.sqrt (x j) +
          (Real.sqrt (x j))⁻¹ := by
      rw [div_le_iff₀ hs]
      field_simp
      nlinarith [hup]
    exact hnormalized

/-- The leading constant in the paper's moment cutoff: `K/sqrt(x) → 10σ`. -/
theorem momentK_sqrt_ratio_tendsto (σ : ℝ) (hσ : 0 ≤ σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (momentK σ (x j) : ℝ) / Real.sqrt (x j))
      atTop (𝓝 (10 * σ)) := by
  have hroot : Tendsto (fun j => (x j) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
  have hrootSqrt : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    simpa [Real.sqrt_eq_rpow] using hroot
  have hinvRoot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hrootSqrt.inv_tendsto_atTop
  have hlow : Tendsto (fun _ : ℕ => 10 * σ) atTop (𝓝 (10 * σ)) :=
    tendsto_const_nhds
  have hhigh : Tendsto (fun j => 10 * σ + 2 * (Real.sqrt (x j))⁻¹)
      atTop (𝓝 (10 * σ)) := by
    simpa using hlow.add (hinvRoot.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hsqrtpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hxj
    have hceilLower : 5 * σ * Real.sqrt (x j) ≤
        (Nat.ceil (5 * σ * Real.sqrt (x j)) : ℝ) := Nat.le_ceil _
    have hKLower : 10 * σ * Real.sqrt (x j) ≤ (momentK σ (x j) : ℝ) := by
      dsimp [momentK]
      push_cast
      nlinarith [hceilLower]
    rw [le_div_iff₀ hsqrtpos]
    nlinarith [hKLower]
  · filter_upwards [hx.eventually_gt_atTop 0] with j hxj
    have hsqrtpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hxj
    have hceilUpper := natCeil_le_add_one
      (5 * σ * Real.sqrt (x j)) (by positivity)
    have hKUpper : (momentK σ (x j) : ℝ) ≤
        10 * σ * Real.sqrt (x j) + 2 := by
      dsimp [momentK]
      push_cast
      nlinarith [hceilUpper]
    rw [div_le_iff₀ hsqrtpos]
    field_simp [ne_of_gt hsqrtpos]
    nlinarith [hKUpper]

/-- Substitution of the chosen `K` and `r_c` cutoffs gives the paper's
leading `q/x → 20σ²` asymptotic. -/
theorem cutoffQ_ratio_tendsto (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => (cutoffQ σ (x j) : ℝ) / x j)
      atTop (𝓝 (20 * σ ^ 2)) := by
  have hK := momentK_sqrt_ratio_tendsto σ hσ.le x hx
  have hR := cutoffRc_sqrt_ratio_tendsto σ hσ x hx
  have hroot : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
    simpa only [Real.sqrt_eq_rpow] using hp
  have hinvroot : Tendsto (fun j => (Real.sqrt (x j))⁻¹) atTop (𝓝 0) :=
    hroot.inv_tendsto_atTop
  have hinvx : Tendsto (fun j => (x j)⁻¹) atTop (𝓝 0) := hx.inv_tendsto_atTop
  have hinner : Tendsto
      (fun j => (2 * (cutoffRc σ (x j) : ℝ) + 1) / Real.sqrt (x j))
      atTop (𝓝 (2 * σ)) := by
    have h := (hR.const_mul 2).add hinvroot
    have heq : (fun j => (2 * (cutoffRc σ (x j) : ℝ) + 1) /
        Real.sqrt (x j)) =ᶠ[atTop]
        fun j => 2 * ((cutoffRc σ (x j) : ℝ) / Real.sqrt (x j)) +
          (Real.sqrt (x j))⁻¹ := by
      filter_upwards [hx.eventually_gt_atTop 0] with j hj
      have hs : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hj)
      field_simp [hs]
      <;> ring
    simpa using h.congr' heq.symm
  have hprod : Tendsto
      (fun j => ((momentK σ (x j) : ℝ) / Real.sqrt (x j)) *
        ((2 * (cutoffRc σ (x j) : ℝ) + 1) / Real.sqrt (x j)))
      atTop (𝓝 (20 * σ ^ 2)) := by
    have hp := hK.mul hinner
    convert hp using 1 <;> ring
  have hsum : Tendsto
      (fun j => ((momentK σ (x j) : ℝ) / Real.sqrt (x j)) *
        ((2 * (cutoffRc σ (x j) : ℝ) + 1) / Real.sqrt (x j)) +
        2 * (x j)⁻¹)
      atTop (𝓝 (20 * σ ^ 2)) := by
    have hsmall := hinvx.const_mul 2
    simpa using hprod.add hsmall
  have heq : (fun j =>
      ((momentK σ (x j) : ℝ) / Real.sqrt (x j)) *
        ((2 * (cutoffRc σ (x j) : ℝ) + 1) / Real.sqrt (x j)) +
        2 * (x j)⁻¹) =ᶠ[atTop]
      fun j => (cutoffQ σ (x j) : ℝ) / x j := by
    filter_upwards [hx.eventually_gt_atTop 0] with j hj
    have hs : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hj)
    have hsq : Real.sqrt (x j) * Real.sqrt (x j) = x j := by
      nlinarith [Real.sq_sqrt hj.le]
    simp only [cutoffQ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hsq]
    field_simp [ne_of_gt hj, hs]
    <;> ring
  exact hsum.congr' heq

/-- The critical radius tends to infinity, since its square-root-normalized
limit is the positive constant `σ`. -/
theorem cutoffRc_tendsto_atTop (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => cutoffRc σ (x j)) atTop atTop := by
  have hR := cutoffRc_sqrt_ratio_tendsto σ hσ x hx
  have hroot : Tendsto (fun j => Real.sqrt (x j)) atTop atTop := by
    have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
    simpa only [Real.sqrt_eq_rpow] using hp
  have hreal : Tendsto (fun j => (cutoffRc σ (x j) : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    have hratio : ∀ᶠ j in atTop,
        σ / 2 < (cutoffRc σ (x j) : ℝ) / Real.sqrt (x j) :=
      hR.eventually (Ioi_mem_nhds (by linarith : σ / 2 < σ))
    have hsqrt : ∀ᶠ j in atTop,
        (2 * (max B 0 + 1)) / σ < Real.sqrt (x j) :=
      hroot.eventually_gt_atTop ((2 * (max B 0 + 1)) / σ)
    filter_upwards [hratio, hsqrt, hx.eventually_gt_atTop 0] with j hjR hjS hjx
    have hrootpos : 0 < Real.sqrt (x j) := Real.sqrt_pos.2 hjx
    have hfirst : max B 0 + 1 < (σ / 2) * Real.sqrt (x j) := by
      have hmul := (div_lt_iff₀ hσ).1 hjS
      nlinarith
    have hsecond : (σ / 2) * Real.sqrt (x j) <
        ((cutoffRc σ (x j) : ℝ) / Real.sqrt (x j)) * Real.sqrt (x j) :=
      mul_lt_mul_of_pos_right hjR hrootpos
    have heq : (cutoffRc σ (x j) : ℝ) =
        ((cutoffRc σ (x j) : ℝ) / Real.sqrt (x j)) * Real.sqrt (x j) := by
      field_simp [ne_of_gt hrootpos]
    rw [heq]
    have hBt : B < max B 0 + 1 := by
      by_cases hB : B ≤ 0
      · rw [max_eq_right hB]
        linarith
      · rw [max_eq_left (le_of_not_ge hB)]
        linarith
    exact (calc
      B ≤ max B 0 + 1 := hBt.le
      _ < (σ / 2) * Real.sqrt (x j) := hfirst
      _ < ((cutoffRc σ (x j) : ℝ) / Real.sqrt (x j)) * Real.sqrt (x j) := hsecond).le
  apply tendsto_atTop.2
  intro n
  have hn : ∀ᶠ j in atTop, (n : ℝ) < (cutoffRc σ (x j) : ℝ) :=
    hreal.eventually_gt_atTop n
  filter_upwards [hn] with j hj
  exact_mod_cast hj.le

/-- The normalized ceiling penalty in the `d_*` exponent vanishes. -/
theorem cutoffPenalty_tendsto_zero (σ : ℝ) (hσ : 0 < σ)
    (x : ℕ → ℝ) (hx : Tendsto x atTop atTop) :
    Tendsto (fun j => cutoffPenalty σ (x j)) atTop (𝓝 0) := by
  have hS := cutoffS_ratio_tendsto x hx
  have hR := cutoffRc_tendsto_atTop σ hσ x hx
  have hden : Tendsto (fun j => 2 * cutoffRc σ (x j) - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    have hRlarge := hR.eventually_ge_atTop (max n 1)
    filter_upwards [hRlarge] with j hj
    omega
  have hdenReal : Tendsto
      (fun j => ((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hden
  have hinvden : Tendsto
      (fun j => (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) := hdenReal.inv_tendsto_atTop
  have hSsmall : ∀ᶠ j in atTop, (cutoffS (x j) : ℝ) / x j < 1 :=
    hS.eventually (Iio_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1))
  have hSpos : ∀ᶠ j in atTop, 0 < (cutoffS (x j) : ℝ) / x j :=
    hS.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  apply squeeze_zero'
    (show ∀ᶠ j in atTop, 0 ≤ cutoffPenalty σ (x j) from ?_)
    ?_ hinvden
  · filter_upwards [hx.eventually_gt_atTop 0,
      hden.eventually_ge_atTop 1] with j hj hdenj
    have hdenpos : 0 < ((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2 * cutoffRc σ (x j) - 1)
    unfold cutoffPenalty
    positivity
  · filter_upwards [hx.eventually_gt_atTop 0, hden.eventually_ge_atTop 1,
      hSsmall, hSpos] with j hj hdenj hSlt hSposj
    have hdenpos : 0 < ((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2 * cutoffRc σ (x j) - 1)
    have hnumle : ((cutoffS (x j) - 1 : ℕ) : ℝ) ≤ (cutoffS (x j) : ℝ) := by
      exact_mod_cast (Nat.sub_le (cutoffS (x j)) 1)
    have hA : ((cutoffS (x j) - 1 : ℕ) : ℝ) / x j ≤ 1 := by
      have hle := div_le_div_of_nonneg_right hnumle hj.le
      exact le_trans hle hSlt.le
    have hsNat : 1 ≤ cutoffS (x j) := by
      by_contra hn
      have hz : cutoffS (x j) = 0 := by omega
      simp [hz] at hSposj
    have hA_nonneg : 0 ≤ ((cutoffS (x j) - 1 : ℕ) : ℝ) / x j :=
      div_nonneg (Nat.cast_nonneg _) hj.le
    have hInv_nonneg : 0 ≤ (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr hdenpos.le
    have heq : cutoffPenalty σ (x j) =
        (((cutoffS (x j) - 1 : ℕ) : ℝ) / x j) *
          (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹ := by
      have hrearrange : ∀ (a b c : ℝ), b ≠ 0 → c ≠ 0 →
          (a / b) / c = (a / c) * b⁻¹ := by
        intro a b c hb hc
        by_cases ha : a = 0
        · simp [ha]
        · field_simp [hb, hc, ha]
          ring
      unfold cutoffPenalty
      exact hrearrange _ _ _ (ne_of_gt hdenpos) (ne_of_gt hj)
    rw [heq]
    calc
      (((cutoffS (x j) - 1 : ℕ) : ℝ) / x j) *
          (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹ ≤
        1 * (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hA hInv_nonneg
      _ = (((2 * cutoffRc σ (x j) - 1 : ℕ) : ℝ))⁻¹ := one_mul _




end Erdos1016.Proof.CutoffLimits

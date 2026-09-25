import Erdos1016.Expansion.ConnectorRadiusBound
import Erdos1016.Cycles.Selection.CutoffLimits

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.ConnectorCutoffLimits

/-- A logarithm divided by any fixed positive power tends to zero. -/
theorem log_div_rpow_tendsto_zero
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j => Real.log (n j) / (n j) ^ α) atTop (𝓝 0) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hα).tendsto_div_nhds_zero
  have hsmall' : Tendsto (fun x : ℝ => Real.log x / x ^ α) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hsmall
  exact hsmall'.comp hn

/-- The shifted logarithm in the shore-radius cutoff has the same power decay. -/
theorem log_add_one_div_rpow_tendsto_zero
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j => Real.log (n j + 1) / (n j) ^ α) atTop (𝓝 0) := by
  have hlog := log_div_rpow_tendsto_zero n hn α hα
  have hpow : Tendsto (fun j => (n j) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp hn
  have hinv : Tendsto (fun j => ((n j) ^ α)⁻¹) atTop (𝓝 0) :=
    hpow.inv_tendsto_atTop
  have hconst : Tendsto (fun j => Real.log 2 * ((n j) ^ α)⁻¹)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := Real.log 2)).mul hinv
  have hmajor : Tendsto
      (fun j => Real.log (n j) / (n j) ^ α +
        Real.log 2 * ((n j) ^ α)⁻¹) atTop (𝓝 0) := by
    simpa using hlog.add hconst
  have hpos : ∀ᶠ j in atTop, 1 ≤ n j := hn.eventually_ge_atTop 1
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ Real.log (n j + 1) / (n j) ^ α := by
    filter_upwards [hpos] with j hj
    apply div_nonneg
    · exact Real.log_nonneg (by linarith)
    · exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
  have hle : ∀ᶠ j in atTop,
      Real.log (n j + 1) / (n j) ^ α ≤
        Real.log (n j) / (n j) ^ α + Real.log 2 * ((n j) ^ α)⁻¹ := by
    filter_upwards [hpos] with j hj
    have hlog : Real.log (n j + 1) ≤ Real.log (n j) + Real.log 2 := by
      calc
        Real.log (n j + 1) ≤ Real.log (2 * n j) :=
          Real.log_le_log (by positivity) (by nlinarith)
        _ = Real.log (n j) + Real.log 2 := by
          rw [mul_comm (2 : ℝ) (n j),
            Real.log_mul (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
    have hden : 0 < (n j) ^ α := Real.rpow_pos_of_pos (by linarith) _
    have hdiv := div_le_div_of_nonneg_right hlog hden.le
    convert hdiv using 1 <;> field_simp
  exact squeeze_zero' hnonneg hle hmajor

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

def polynomialPackingCutoff (n : ℝ) : ℕ := Nat.ceil (n ^ (3 / 4 : ℝ))

/-- The paper's `ceil(n^(3/4))` packing threshold is `o(n^(25/32))`. -/
theorem polynomialPackingCutoff_ratio_tendsto_zero
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun j => (polynomialPackingCutoff (n j) : ℝ) /
      (n j) ^ (25 / 32 : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun j => (n j) ^ (1 / 32 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp hn
  have hinv : Tendsto (fun j => ((n j) ^ (1 / 32 : ℝ))⁻¹)
      atTop (𝓝 0) := hpow.inv_tendsto_atTop
  have hnegEq : (fun j => (n j) ^ (-1 / 32 : ℝ)) =ᶠ[atTop]
      fun j => ((n j) ^ (1 / 32 : ℝ))⁻¹ := by
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    simpa only [neg_div] using Real.rpow_neg hj.le (1 / 32 : ℝ)
  have hsmall : Tendsto (fun j => (n j) ^ (-1 / 32 : ℝ)) atTop (𝓝 0) :=
    (tendsto_congr' hnegEq).2 hinv
  have hpowEq : ∀ᶠ j in atTop,
      (n j) ^ (3 / 4 : ℝ) / (n j) ^ (25 / 32 : ℝ) =
        (n j) ^ (-1 / 32 : ℝ) := by
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    rw [div_eq_mul_inv, ← Real.rpow_neg hj.le (25 / 32 : ℝ),
      ← Real.rpow_add hj]
    congr 1 <;> norm_num
  have hbase : Tendsto
      (fun j => (n j) ^ (3 / 4 : ℝ) / (n j) ^ (25 / 32 : ℝ))
      atTop (𝓝 0) := (tendsto_congr' hpowEq).2 hsmall
  have hden : Tendsto (fun j => (n j) ^ (25 / 32 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 25 / 32)).comp hn
  have hinvDen : Tendsto (fun j => ((n j) ^ (25 / 32 : ℝ))⁻¹)
      atTop (𝓝 0) := hden.inv_tendsto_atTop
  have hmajor : Tendsto (fun j =>
      (n j) ^ (3 / 4 : ℝ) / (n j) ^ (25 / 32 : ℝ) +
        ((n j) ^ (25 / 32 : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hbase.add hinvDen
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ (polynomialPackingCutoff (n j) : ℝ) / (n j) ^ (25 / 32 : ℝ) := by
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hj _))
  have hle : ∀ᶠ j in atTop,
      (polynomialPackingCutoff (n j) : ℝ) / (n j) ^ (25 / 32 : ℝ) ≤
        (n j) ^ (3 / 4 : ℝ) / (n j) ^ (25 / 32 : ℝ) +
          ((n j) ^ (25 / 32 : ℝ))⁻¹ := by
    filter_upwards [hn.eventually_gt_atTop 0] with j hj
    have harg : 0 ≤ (n j) ^ (3 / 4 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hj _)
    have hceil := natCeil_le_add_one ((n j) ^ (3 / 4 : ℝ)) harg
    have hdenpos : 0 < (n j) ^ (25 / 32 : ℝ) := Real.rpow_pos_of_pos hj _
    have hdiv := div_le_div_of_nonneg_right hceil hdenpos.le
    rw [add_div] at hdiv
    simpa only [one_div] using hdiv
  exact squeeze_zero' hnonneg hle hmajor

def logarithmicGirthCutoff (n : ℝ) : ℕ :=
  Erdos1016.Proof.CutoffLimits.cutoffD
    (Real.logb 2 n)

/-- The paper's logarithmic depth cutoff is negligible at every positive
power scale of the ambient size. -/
theorem logarithmicGirthCutoff_ratio_tendsto_zero
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (α : ℝ) (hα : 0 < α) :
    Tendsto (fun j => (logarithmicGirthCutoff (n j) : ℝ) / (n j) ^ α)
      atTop (𝓝 0) := by
  have hlog := log_div_rpow_tendsto_zero n hn α hα
  have hlogb : Tendsto
      (fun j => Real.logb 2 (n j) / (n j) ^ α) atTop (𝓝 0) := by
    have heq : (fun j => Real.logb 2 (n j) / (n j) ^ α) =
        fun j => (Real.log (n j) / (n j) ^ α) / Real.log 2 := by
      funext j
      change (Real.log (n j) / Real.log 2) / (n j) ^ α = _
      ring
    rw [heq]
    simpa using hlog.div_const (Real.log 2)
  have hNpos : ∀ᶠ j in atTop, 0 < n j := hn.eventually_gt_atTop 0
  have hcutpos : ∀ᶠ j in atTop, 0 < Real.logb 2 (n j) := by
    have hlogbTop : Tendsto (fun j => Real.logb 2 (n j)) atTop atTop := by
      exact (Real.tendsto_logb_atTop (by norm_num : 1 < (2 : ℝ))).comp hn
    exact hlogbTop.eventually_gt_atTop 0
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ (logarithmicGirthCutoff (n j) : ℝ) / (n j) ^ α := by
    filter_upwards [hNpos] with j hj
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hj _))
  have hle : ∀ᶠ j in atTop,
      (logarithmicGirthCutoff (n j) : ℝ) / (n j) ^ α ≤
        (1 / 2 : ℝ) * (Real.logb 2 (n j) / (n j) ^ α) := by
    filter_upwards [hcutpos, hNpos] with j hx hj
    have hfloor : (logarithmicGirthCutoff (n j) : ℝ) ≤ Real.logb 2 (n j) / 2 := by
      dsimp [logarithmicGirthCutoff,
        Erdos1016.Proof.CutoffLimits.cutoffD]
      exact Nat.floor_le (by linarith)
    have hden : 0 < (n j) ^ α := Real.rpow_pos_of_pos hj _
    calc
      (logarithmicGirthCutoff (n j) : ℝ) / (n j) ^ α ≤
          (Real.logb 2 (n j) / 2) / (n j) ^ α :=
        div_le_div_of_nonneg_right hfloor hden.le
      _ = (1 / 2 : ℝ) * (Real.logb 2 (n j) / (n j) ^ α) := by
        field_simp
  have hmajor : Tendsto
      (fun j => (1 / 2 : ℝ) * (Real.logb 2 (n j) / (n j) ^ α))
      atTop (𝓝 0) := by simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul hlogb
  exact squeeze_zero' hnonneg hle hmajor

def logarithmicConnectorRadius (c n : ℝ) : ℕ :=
  Nat.ceil (4 * Real.log (n + 1) / (c * n ^ (-(1 / 8 : ℝ))))

/-- Under the paper's expansion scale `κ ≥ c n^(-1/8)`, the connector
radius ceiling is negligible compared to `n^(5/32)`. -/
theorem logarithmicConnectorRadius_ratio_tendsto_zero
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (c : ℝ) (hc : 0 < c)
    (hnge : ∀ j, 1 ≤ n j) :
    Tendsto (fun j => (logarithmicConnectorRadius c (n j) : ℝ) /
      (n j) ^ (5 / 32 : ℝ)) atTop (𝓝 0) := by
  have hlog := log_add_one_div_rpow_tendsto_zero n hn (1 / 32 : ℝ)
    (by norm_num)
  have hpow : Tendsto (fun j => (n j) ^ (5 / 32 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 32)).comp hn
  have hinv : Tendsto (fun j => ((n j) ^ (5 / 32 : ℝ))⁻¹)
      atTop (𝓝 0) := hpow.inv_tendsto_atTop
  have hscale : Tendsto (fun j => (4 / c) *
      (Real.log (n j + 1) / (n j) ^ (1 / 32 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 4 / c)).mul hlog
  have hmajor : Tendsto (fun j => (4 / c) *
      (Real.log (n j + 1) / (n j) ^ (1 / 32 : ℝ)) +
      ((n j) ^ (5 / 32 : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using hscale.add hinv
  have hNpos : ∀ j, 0 < n j := fun j => lt_of_lt_of_le zero_lt_one (hnge j)
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ (logarithmicConnectorRadius c (n j) : ℝ) /
        (n j) ^ (5 / 32 : ℝ) := by
    filter_upwards with j
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact le_of_lt (Real.rpow_pos_of_pos (hNpos j) _)
  have hle : ∀ᶠ j in atTop,
      (logarithmicConnectorRadius c (n j) : ℝ) / (n j) ^ (5 / 32 : ℝ) ≤
        (4 / c) * (Real.log (n j + 1) / (n j) ^ (1 / 32 : ℝ)) +
          ((n j) ^ (5 / 32 : ℝ))⁻¹ := by
    filter_upwards with j
    let N := n j
    have hN : 0 < N := hNpos j
    have hN1 : 1 ≤ N := hnge j
    have hbase : 0 < N ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hN _
    have hsmall : 0 < N ^ (1 / 32 : ℝ) := Real.rpow_pos_of_pos hN _
    have hlarge : 0 < N ^ (5 / 32 : ℝ) := Real.rpow_pos_of_pos hN _
    have hneg : N ^ (-(1 / 8 : ℝ)) = (N ^ (1 / 8 : ℝ))⁻¹ := by
      simpa using Real.rpow_neg hN.le (1 / 8 : ℝ)
    have harg : 0 ≤ 4 * Real.log (N + 1) /
        (c * N ^ (-(1 / 8 : ℝ))) := by
      apply div_nonneg
      · apply mul_nonneg
        · positivity
        · exact Real.log_nonneg (by linarith)
      · positivity
    have hceil := natCeil_le_add_one
      (4 * Real.log (N + 1) / (c * N ^ (-(1 / 8 : ℝ)))) harg
    have hargEq :
        4 * Real.log (N + 1) / (c * N ^ (-(1 / 8 : ℝ))) =
          (4 / c) * Real.log (N + 1) * N ^ (1 / 8 : ℝ) := by
      rw [hneg]
      field_simp [ne_of_gt hc, ne_of_gt hbase]
      <;> ring
    have hpowEq : N ^ (1 / 8 : ℝ) / N ^ (5 / 32 : ℝ) =
        (N ^ (1 / 32 : ℝ))⁻¹ := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hN.le (5 / 32 : ℝ),
        ← Real.rpow_add hN]
      rw [show (1 / 8 : ℝ) + -(5 / 32 : ℝ) = -(1 / 32 : ℝ) by norm_num]
      exact Real.rpow_neg hN.le (1 / 32 : ℝ)
    have hargNorm :
        (4 * Real.log (N + 1) / (c * N ^ (-(1 / 8 : ℝ)))) /
            N ^ (5 / 32 : ℝ) =
          (4 / c) * (Real.log (N + 1) / N ^ (1 / 32 : ℝ)) := by
      rw [hargEq]
      calc
        (4 / c) * Real.log (N + 1) * N ^ (1 / 8 : ℝ) /
            N ^ (5 / 32 : ℝ) =
          (4 / c) * Real.log (N + 1) *
            (N ^ (1 / 8 : ℝ) / N ^ (5 / 32 : ℝ)) := by ring
        _ = (4 / c) * (Real.log (N + 1) / N ^ (1 / 32 : ℝ)) := by
          rw [hpowEq]
          field_simp [ne_of_gt hsmall]
    have hresult :
        (logarithmicConnectorRadius c N : ℝ) / N ^ (5 / 32 : ℝ) ≤
          (4 / c) * (Real.log (N + 1) / N ^ (1 / 32 : ℝ)) +
            (N ^ (5 / 32 : ℝ))⁻¹ := by
      have hceil' : (logarithmicConnectorRadius c N : ℝ) ≤
          4 * Real.log (N + 1) / (c * N ^ (-(1 / 8 : ℝ))) + 1 := by
        exact hceil
      have hdivide := div_le_div_of_nonneg_right hceil'
        (le_of_lt hlarge)
      rw [add_div, hargNorm] at hdivide
      simpa only [one_div] using hdivide
    simpa [logarithmicConnectorRadius, N] using hresult
  exact squeeze_zero' hnonneg hle hmajor



end Erdos1016.Proof.ConnectorCutoffLimits

end

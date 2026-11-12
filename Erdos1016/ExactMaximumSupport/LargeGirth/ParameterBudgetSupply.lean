import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetDecay
import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetScales

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Trace, deficit, and lower-girth budgets

The deleted-set envelopes come from the proved dyadic packing exponents.
The supply bounds are uniform over every retained order in the required range.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

theorem polynomial_rpow_quotient_zero (n : ℕ) (a b : ℝ) (hab : a < b) :
    Tendsto (fun x : ℝ => x^n*(2 : ℝ)^(a*x)/(2 : ℝ)^(b*x)) atTop (𝓝 0) := by
  have h := polynomial_rpow_decay n (b-a) (by linarith)
  convert h using 1
  funext x
  rw [mul_div_assoc, ← Real.rpow_sub (by norm_num)]
  congr 2
  ring

theorem removed_fraction_zero :
    Tendsto (fun x : ℝ => (3*x+(2 : ℝ)^(x/3)+2)/(2 : ℝ)^x) atTop (𝓝 0) := by
  have h1 := (polynomial_rpow_quotient_zero 1 0 1 (by norm_num)).const_mul 3
  have h2 := polynomial_rpow_quotient_zero 0 (1/3) 1 (by norm_num)
  have h3 := (polynomial_rpow_quotient_zero 0 0 1 (by norm_num)).const_mul 2
  have h := (h1.add h2).add h3
  simp only [mul_zero, zero_add, add_zero] at h
  convert h using 1
  funext x
  simp only [pow_one, pow_zero, zero_mul, Real.rpow_zero, mul_one, one_mul]
  rw [show 1/3*x=x/3 by ring]
  ring

theorem deficit_budget_zero :
    Tendsto (fun x : ℝ => 3*(3*x+(2 : ℝ)^(x/3))*(amplitude*x)/(2 : ℝ)^x)
      atTop (𝓝 0) := by
  have h1 := (polynomial_rpow_quotient_zero 2 0 1 (by norm_num)).const_mul (9*amplitude)
  have h2 := (polynomial_rpow_quotient_zero 1 (1/3) 1 (by norm_num)).const_mul (3*amplitude)
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext x
  simp only [pow_one, zero_mul, Real.rpow_zero, mul_one, one_mul]
  rw [show 1/3*x=x/3 by ring]
  ring

theorem trace_error_zero :
    Tendsto (fun x : ℝ => 6*(2 : ℝ)^x/(2 : ℝ)^(3*x)) atTop (𝓝 0) := by
  simpa only [pow_zero, one_mul, mul_zero, mul_div_assoc] using
    (polynomial_rpow_quotient_zero 0 1 3 (by norm_num)).const_mul 6

/-- The retained order is at least the rank once the deleted-set bound is inserted. -/
theorem eventually_removed_plus_two : ∀ᶠ (x : ℝ) in atTop,
    3*x+(2 : ℝ)^(x/3)+2 ≤ (2 : ℝ)^x := by
  filter_upwards [removed_fraction_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with x hx
  exact (div_le_one (by positivity)).mp hx.le

/-- The exact finite trace hypotheses hold for every admissible retained order. -/
theorem eventually_supply_budgets : ∀ᶠ (x : ℝ) in atTop, ∀ p S v : ℕ,
    (p : ℝ) ≤ 3*x → (S : ℝ) ≤ (2 : ℝ)^(x/3) →
    (2 : ℝ)^x ≤ v → (v : ℝ) ≤ (2 : ℝ)^(x+1) →
    0 < v ∧ 0 < traceStart x ∧ traceStart x ≤ halfCutoff x+1 ∧
    3*((p+S : ℕ) : ℝ) < v ∧
    3*((p+S : ℕ) : ℝ)*(halfCutoff x : ℝ)/v ≤ 1/200 ∧
    3*(v : ℝ)/(2 : ℝ)^traceStart x ≤ 1/200 := by
  have ha := amplitude_pos
  have hd := deficit_budget_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1/200)
  have he := trace_error_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1/200)
  have hM := traceStart_ratio.eventually_lt_const (by norm_num : (3 : ℝ) < 4)
  have hK := halfCutoff_ratio.eventually_const_lt
    (show (4 : ℝ) < amplitude/2 by
      have h := Real.add_one_le_exp (124 : ℝ)
      dsimp [amplitude]
      linarith)
  filter_upwards [hd,he,hM,hK,eventually_cutoff_bounds,eventually_ge_atTop (1 : ℝ)]
    with x hd he hM hK hL hx
  intro p S v hp hS hv hv'
  have hx0 : 0 < x := by linarith
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le (by positivity) hv
  have hM0 : 0 < traceStart x := by
    have hm := Nat.le_ceil (3*x)
    change 3*x ≤ (traceStart x : ℝ) at hm
    exact_mod_cast (show (0 : ℝ) < traceStart x by linarith)
  have hMK : traceStart x ≤ halfCutoff x+1 := by
    have hm := (div_lt_iff₀ hx0).mp hM
    have hk := (lt_div_iff₀ hx0).mp hK
    have hh : (traceStart x : ℝ) ≤ halfCutoff x := by linarith
    exact Nat.le_succ_of_le (by exact_mod_cast hh)
  have hK0 : 1 ≤ halfCutoff x := by
    dsimp [cutoff] at hL
    omega
  have hKr : (halfCutoff x : ℝ) ≤ amplitude*x := by
    have hh := hL.2.1
    dsimp [cutoff] at hh
    push_cast at hh
    linarith
  have hps : ((p+S : ℕ) : ℝ) ≤ 3*x+(2 : ℝ)^(x/3) := by push_cast; linarith
  have hb : 3*((p+S : ℕ) : ℝ)*(halfCutoff x : ℝ)/v ≤ 1/200 := by
    calc
      _ ≤ 3*(3*x+(2 : ℝ)^(x/3))*(amplitude*x)/(2 : ℝ)^x := by
        apply div_le_div₀ (by positivity) _ (by positivity) hv
        gcongr
      _ ≤ 1/200 := hd.le
  have hdef : 3*((p+S : ℕ) : ℝ) < v := by
    have hb' := (div_le_iff₀ hv0).mp hb
    have hk : (1 : ℝ) ≤ halfCutoff x := by exact_mod_cast hK0
    have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ 3*((p+S : ℕ) : ℝ) by positivity)
    nlinarith
  have htrace : 3*(v : ℝ)/(2 : ℝ)^traceStart x ≤ 1/200 := by
    have hm := Nat.le_ceil (3*x)
    have hpw : (2 : ℝ)^(3*x) ≤ (2 : ℝ)^traceStart x := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
    have hvb : (v : ℝ) ≤ 2*(2 : ℝ)^x := by
      simpa [Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_comm] using hv'
    calc
      _ ≤ 6*(2 : ℝ)^x/(2 : ℝ)^(3*x) := by
        apply div_le_div₀ (by positivity) (by linarith) (by positivity) hpw
      _ ≤ 1/200 := he.le
  exact ⟨by exact_mod_cast hv0,hM0,hMK,hdef,hb,htrace⟩

theorem eventually_low_girth_budget (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ (x : ℝ) in atTop,
    C*Real.logb 2 ((cutoff x : ℝ)+2) ≤ Real.sqrt x := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)
  have hl : Tendsto (fun x => logScale x / Real.sqrt x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
    convert h.div_const (Real.log 2) using 1
    · funext x
      rw [Real.sqrt_eq_rpow]
      dsimp [logScale,Real.logb]
      ring
    · simp
  have hc : Tendsto (fun x => Real.logb 2 (2*amplitude+2)/Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hb := ((hc.add hl).const_mul C).eventually_lt_const
    (by norm_num : C*(0+0)<1)
  filter_upwards [hb,eventually_cutoff_bounds,eventually_ge_atTop (1 : ℝ)] with x hb hL hx
  have hx0 : 0 < x := by linarith
  have ha : 0 < 2*amplitude+2 := by have := amplitude_pos; positivity
  have harg : (cutoff x : ℝ)+2 ≤ (2*amplitude+2)*x := by nlinarith [hL.2.1]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (by positivity : (0 : ℝ)<(cutoff x : ℝ)+2) harg
  rw [Real.logb_mul ha.ne' hx0.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hC
  have hb' := (div_lt_iff₀ (Real.sqrt_pos.mpr hx0)).mp
    (show C*(Real.logb 2 (2*amplitude+2)+logScale x)/Real.sqrt x<1 by
      simpa only [add_div,mul_add,mul_div_assoc] using hb)
  dsimp [logScale] at hb'
  linarith

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

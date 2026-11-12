import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainPackingCutoff

/-- One large-girth threshold supplies the logarithmic piece budget for every
cut size at most twice the girth, including cut sizes two and three. -/
theorem exists_cutoff (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℕ, 256 ≤ D ∧ ∀ g d : ℕ, D ≤ g → d ≤ 2*g →
      C * Real.logb 2 ((max d 4 : ℕ)+2) ≤ g := by
  have hc : Tendsto (fun x : ℝ => (2*C)/x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hr : Tendsto (fun x : ℝ => C*(2+Real.logb 2 x)/x) atTop (𝓝 0) := by
    convert hc.add (LargeGirth.ParameterBudget.logScale_ratio.const_mul C) using 1
    · funext x
      dsimp [LargeGirth.ParameterBudget.logScale]
      ring
    · simp
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp
    (hr.eventually_lt_const (by norm_num : (0:ℝ)<1))
  refine ⟨max 256 ⌈x₀⌉₊,le_max_left _ _,?_⟩
  intro g d hg hd
  have hg256 : 256 ≤ g := (le_max_left _ _).trans hg
  have hceil : ⌈x₀⌉₊ ≤ g := (le_max_right _ _).trans hg
  have hg0 : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hx : x₀ ≤ (g:ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hceil)
  have hsmall : C*(2+Real.logb 2 (g:ℝ)) ≤ g :=
    ((div_lt_one hg0).mp (hx₀ (g:ℝ) hx)).le
  have hmax : max d 4 + 2 ≤ 4*g := by omega
  have hm : Real.logb 2 ((max d 4 : ℕ)+2) ≤ 2+Real.logb 2 (g:ℝ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by positivity : (0:ℝ)<((max d 4 : ℕ)+2))
      (by exact_mod_cast hmax : (((max d 4 : ℕ)+2):ℝ)≤4*(g:ℝ))
    rw [Real.logb_mul (by norm_num) hg0.ne'] at hh
    have h4 : Real.logb 2 4 = 2 := by
      rw [show (4:ℝ)=2*2 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rwa [h4] at hh
  exact (mul_le_mul_of_nonneg_left hm hC).trans hsmall

end Erdos1016.ExactMaximumSupport.Shortening.ChainPackingCutoff

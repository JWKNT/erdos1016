import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetBlocks
import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetSupply

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Eventual numerical parameters from the ambient rank scale

Every parameter is an explicit scalar choice. The conclusions are the finite
budgets consumed by the actual packing contradiction.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

theorem eventually_link_geometry : ∀ᶠ (x : ℝ) in atTop, ∀ D : ℕ,
    x/16 ≤ D → (D : ℝ) ≤ x/8 →
    8 ≤ D ∧ D ≤ cutoff x ∧ 1 ≤ parallelDepth x ∧
    2*(parallelDepth x+2*(D/8)) ≤ D ∧ 0 < D/2 ∧ 2*(D/2) ≤ D := by
  have ht := parallelDepth_div_x.eventually_lt_const (by norm_num : (0 : ℝ)<1/128)
  have ht1 := parallelDepth_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [ht,ht1,eventually_cutoff_bounds,eventually_ge_atTop (128 : ℝ)]
    with x ht ht1 hL hx
  intro D hD hD'
  have hx0 : 0<x := by linarith
  have hD8 : 8 ≤ D := by exact_mod_cast (show (8 : ℝ)≤D by linarith)
  have hDL : D ≤ cutoff x := by exact_mod_cast (show (D : ℝ)≤cutoff x by linarith [hL.2.2])
  have htr := (div_lt_iff₀ hx0).mp ht
  have htD : 8*parallelDepth x ≤ D := by
    exact_mod_cast (show (8 : ℝ)*parallelDepth x ≤ D by linarith)
  have hdiv := Nat.div_mul_le_self D 8
  exact ⟨hD8,hDL,ht1,by omega,by omega,by omega⟩

theorem packing_size_to_real (S e : ℕ) (b : ℝ)
    (hS : S+1 ≤ 2^e) (he : (e : ℝ)≤b) : (S : ℝ)≤(2 : ℝ)^b := by
  have hSr : (S : ℝ)≤(2 : ℝ)^e := by exact_mod_cast (show S≤2^e by omega)
  rw [←Real.rpow_natCast] at hSr
  exact hSr.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)

/-- Both selected dyadic indices are ordered and have the stated scale ranges. -/
theorem eventually_scale_choices (D₀ : ℕ) (hD₀ : 0<D₀) : ∀ᶠ (x : ℝ) in atTop,
    let i := scaleIndex D₀ (Real.sqrt x)
    let j := scaleIndex D₀ (x/16)
    i ≤ j ∧
    Real.sqrt x ≤ (GirthRaiseBounds.scale D₀ i : ℝ) ∧
    (GirthRaiseBounds.scale D₀ i : ℝ)<2*Real.sqrt x ∧
    x/16 ≤ (GirthRaiseBounds.scale D₀ j : ℝ) ∧
    (GirthRaiseBounds.scale D₀ j : ℝ)<x/8 ∧
    3 ≤ GirthRaiseBounds.scale D₀ i := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)
  filter_upwards [hs.eventually (eventually_ge_atTop (D₀ : ℝ)),
    eventually_ge_atTop (16*(D₀ : ℝ)), eventually_ge_atTop (4096 : ℝ)] with x hs hx hx'
  dsimp only
  have hlo := chosen_scale_bounds D₀ hD₀ (Real.sqrt x) hs
  have hhi := chosen_scale_bounds D₀ hD₀ (x/16) (by linarith)
  have hgap : 2*Real.sqrt x ≤ x/16 := by
    have hsq := Real.sq_sqrt (show 0≤x by linarith)
    have hpos := Real.sqrt_nonneg x
    nlinarith
  have horder : scaleIndex D₀ (Real.sqrt x) ≤ scaleIndex D₀ (x/16) := by
    by_contra hn
    have hh := GirthRaiseBounds.scale_mono D₀ (le_of_lt (Nat.lt_of_not_ge hn))
    have hhR : (GirthRaiseBounds.scale D₀ (scaleIndex D₀ (x/16)) : ℝ) ≤
        GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x)) := by exact_mod_cast hh
    linarith
  have hthree : 3 ≤ GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x)) := by
    have hsq := Real.sq_sqrt (show 0≤x by linarith)
    have hpos := Real.sqrt_nonneg x
    exact_mod_cast (show (3 : ℝ)≤GirthRaiseBounds.scale D₀ (scaleIndex D₀ (Real.sqrt x)) by nlinarith [hlo.1])
  exact ⟨horder,hlo.1,hlo.2,hhi.1,by linarith [hhi.2],hthree⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

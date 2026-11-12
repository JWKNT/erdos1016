import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetDecay
import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetScales

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Load and clean-block budgets

The block span has a fixed margin for the rounded even cycle cutoff.
The estimates are uniform in both admissible dyadic scales.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

def blockSpan (x : ℝ) : ℕ := ⌈512 * amplitude^2 * x⌉₊ + 2

theorem blockSpan_bounds (x : ℝ) (hx : 1 ≤ x) :
    512 * amplitude^2 * x ≤ (blockSpan x - 1 : ℕ) ∧
    (blockSpan x : ℝ) ≤ (512 * amplitude^2 + 3)*x := by
  have hp : 0 ≤ 512 * amplitude^2 * x := by positivity
  have hlo := Nat.le_ceil (512 * amplitude^2 * x)
  have hhi := Nat.ceil_lt_add_one hp
  constructor
  · have heq : blockSpan x - 1 = ⌈512 * amplitude^2 * x⌉₊ + 1 := by
      simp [blockSpan]
    rw [heq, Nat.cast_add, Nat.cast_one]
    linarith
  · dsimp [blockSpan]
    push_cast
    nlinarith

theorem blockSpan_size (x : ℝ) (hx : 1 ≤ x) (D : ℕ) (hD : x/16 ≤ D)
    (hL : (cutoff x : ℝ) ≤ 2*amplitude*x) :
    8*(cutoff x)^2 ≤ (blockSpan x-1)*(D+1) := by
  have hw := (blockSpan_bounds x hx).1
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (cutoff x)) hL 2
  have hDp : x/16 ≤ ((D+1 : ℕ) : ℝ) := by push_cast; linarith
  have hm := mul_le_mul hw hDp (by positivity) (Nat.cast_nonneg _)
  have hb : (8 : ℝ)*(cutoff x : ℝ)^2 ≤
      ((blockSpan x-1 : ℕ) : ℝ) * ((D+1 : ℕ) : ℝ) := by nlinarith
  exact_mod_cast hb

theorem half_pow_le (x : ℝ) (s : ℕ) (hs : x/32-1 ≤ s) :
    (1/2 : ℝ)^s ≤ 2*(2 : ℝ)^(-x/32) := by
  have heq : (1/2 : ℝ)^s = (2 : ℝ)^(-(s : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow]
    simp [one_div]
  rw [heq]
  calc
    (2 : ℝ)^(-(s : ℝ)) ≤ (2 : ℝ)^(1-x/32) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2*(2 : ℝ)^(-x/32) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
      simp only [neg_div]

theorem halfScale_lower (x : ℝ) (D : ℕ) (hD : x/16 ≤ D) :
    x/32-1 ≤ (D/2 : ℕ) := by
  have hd : D ≤ 2*(D/2)+1 := by omega
  have hdR : (D : ℝ) ≤ 2*((D/2 : ℕ) : ℝ)+1 := by exact_mod_cast hd
  linarith

def loadUpper (x : ℝ) : ℝ :=
  3*(2*amplitude)^3*x^3*(2 : ℝ)^(-x/64)

theorem loadUpper_zero : Tendsto loadUpper atTop (𝓝 0) := by
  have h := (polynomial_rpow_decay 3 (1/64) (by norm_num)).const_mul
    (3*(2*amplitude)^3)
  unfold loadUpper
  convert h using 1
  · funext x
    ring_nf
  · simp

theorem load_le_upper (x : ℝ) (hx : 1 ≤ x) (s : ℕ) (hs : x/32-1 ≤ s)
    (B : ℝ) (hB : B ≤ x/64) (hL : (cutoff x : ℝ) ≤ 2*amplitude*x) :
    (2 : ℝ)^B * cutoff x * cutoff x *
      ((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^s) ≤ loadUpper x := by
  have ha := amplitude_pos
  have hp := half_pow_le x s hs
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hB
  calc
    (2 : ℝ)^B * cutoff x * cutoff x * ((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^s)
        = (3/2 : ℝ)*(cutoff x : ℝ)^3*(2 : ℝ)^B*(1/2 : ℝ)^s := by ring
    _ ≤ (3/2 : ℝ)*(2*amplitude*x)^3*(2 : ℝ)^(x/64)*
        (2*(2 : ℝ)^(-x/32)) := by gcongr
    _ = loadUpper x := by
      dsimp [loadUpper]
      have he : (2 : ℝ)^(x/64)*(2 : ℝ)^(-x/32) = (2 : ℝ)^(-x/64) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc
        _ = 3*(2*amplitude)^3*x^3*((2 : ℝ)^(x/64)*(2 : ℝ)^(-x/32)) := by ring
        _ = _ := by rw [he]

theorem eventually_load_budgets : ∀ᶠ (x : ℝ) in atTop, ∀ D : ℕ,
    x/16 ≤ D →
    (9/4 : ℝ)*(cutoff x : ℝ)^2*(1/2 : ℝ)^(D/2) ≤ 1/100 ∧
    (cutoff x : ℝ)*((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^(D/2)) ≤ 1/2 ∧
    ∀ B : ℝ, B ≤ x/64 → (2 : ℝ)^B*cutoff x*cutoff x*
      ((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^(D/2)) ≤ 1/2 := by
  have he := loadUpper_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1/300)
  filter_upwards [he, eventually_cutoff_bounds, eventually_ge_atTop (1 : ℝ)] with x he hL hx
  intro D hD
  have hs := halfScale_lower x D hD
  have hbase := load_le_upper x hx (D/2) hs 0 (by linarith) hL.2.1
  simp only [Real.rpow_zero, one_mul] at hbase
  have hL1 : (1 : ℝ) ≤ cutoff x := by exact_mod_cast (show 1 ≤ cutoff x by omega)
  have hp : 0 ≤ (1/2 : ℝ)^(D/2) := by positivity
  have hpoly : (cutoff x : ℝ)^2 ≤ (cutoff x : ℝ)^3 := by
    simpa using pow_le_pow_right₀ hL1 (by decide : 2 ≤ 3)
  have hm := mul_le_mul_of_nonneg_right hpoly hp
  have hc : (9/4 : ℝ)*(cutoff x : ℝ)^2*(1/2 : ℝ)^(D/2) ≤ 1/100 := by
    nlinarith
  have hj : (cutoff x : ℝ)*((3/2 : ℝ)*cutoff x*(1/2 : ℝ)^(D/2)) ≤ 1/2 := by
    nlinarith
  refine ⟨hc,hj,?_⟩
  intro B hB
  exact (load_le_upper x hx (D/2) hs B hB hL.2.1).trans (by linarith)

def chainUpper (x : ℝ) : ℝ :=
  (3*(2*amplitude+3)*(512*amplitude^2+3)*(2*amplitude)^3)*
    x^5*(2 : ℝ)^(-(3/128)*x)

theorem chainUpper_zero : Tendsto chainUpper atTop (𝓝 0) := by
  have h := (polynomial_rpow_decay 5 (3/128) (by norm_num)).const_mul
    (3*(2*amplitude+3)*(512*amplitude^2+3)*(2*amplitude)^3)
  unfold chainUpper
  simpa only [mul_assoc, mul_zero] using h

theorem eventually_clean_chain_budget : ∀ᶠ (x : ℝ) in atTop, ∀ D S : ℕ,
    x/16 ≤ D → (S : ℝ) ≤ (2 : ℝ)^(x/128) →
    (((cutoff x+S+2)*blockSpan x : ℕ) : ℝ)*(3/2 : ℝ)*(cutoff x : ℝ)^3*
      (1/2 : ℝ)^(D/2) ≤ 8 := by
  have ha := amplitude_pos
  have he := chainUpper_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 8)
  filter_upwards [he, eventually_cutoff_bounds, eventually_ge_atTop (1 : ℝ)] with x he hL hx
  intro D S hD hS
  have hLc := hL.2.1
  have hp := half_pow_le x (D/2) (halfScale_lower x D hD)
  have hw := (blockSpan_bounds x hx).2
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ)^(x/128) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hcount : ((cutoff x+S+2 : ℕ) : ℝ) ≤
      (2*amplitude+3)*x*(2 : ℝ)^(x/128) := by
    push_cast
    have hxp := mul_le_mul_of_nonneg_left hpow1 (show 0 ≤ x by linarith)
    have hAxp := mul_le_mul_of_nonneg_left hxp (show 0 ≤ 2*amplitude by positivity)
    nlinarith [hL.2.1]
  calc
    _ = ((cutoff x+S+2 : ℕ) : ℝ)*(blockSpan x : ℝ)*(3/2 : ℝ)*
        (cutoff x : ℝ)^3*(1/2 : ℝ)^(D/2) := by push_cast; ring
    _ ≤ ((2*amplitude+3)*x*(2 : ℝ)^(x/128))*((512*amplitude^2+3)*x)*
        (3/2 : ℝ)*(2*amplitude*x)^3*(2*(2 : ℝ)^(-x/32)) := by gcongr
    _ = chainUpper x := by
      have heq : (2 : ℝ)^(x/128)*(2 : ℝ)^(-x/32) = (2 : ℝ)^(-(3/128)*x) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      dsimp [chainUpper]
      calc
        _ = (3*(2*amplitude+3)*(512*amplitude^2+3)*(2*amplitude)^3)*x^5*
            ((2 : ℝ)^(x/128)*(2 : ℝ)^(-x/32)) := by ring
        _ = _ := by rw [heq]
    _ ≤ 8 := he.le

end Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget

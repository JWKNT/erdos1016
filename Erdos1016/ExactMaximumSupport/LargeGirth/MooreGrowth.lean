import Erdos1016.ExactMaximumSupport.LargeGirth.WeightedMoore
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Numerical growth consequences of the weighted Moore bound

These estimates use integer logarithms with base two and integer radii.
The fixed-ratio pole regime has an absolute rank threshold of 256.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.MooreGrowth

/-- An elementary logarithmic estimate beyond a fixed small range. -/
theorem linear_clog_lt (h : ℕ) (hh : 256 ≤ h) :
    32 * Nat.clog 2 (8 * h) < 3 * (h - 1) := by
  have hpos : h ≠ 0 := by omega
  have hlog : 8 ≤ Nat.log 2 h := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hh)
  have hpow := Nat.pow_log_le_self 2 hpos
  have hclog : Nat.clog 2 (8 * h) ≤ Nat.log 2 h + 4 := by
    apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hl := Nat.lt_pow_succ_log_self (by decide : 1 < 2) h
    have hp : 2 ^ (Nat.log 2 h + 4) = 8 * 2 ^ (Nat.log 2 h + 1) := by
      rw [show Nat.log 2 h + 4 = (Nat.log 2 h + 1) + 3 by omega, pow_add]
      norm_num
      ring
    rw [hp]
    omega
  have hexp (q : ℕ) (hq : 8 ≤ q) : 32 * (q + 4) + 3 < 3 * 2 ^ q := by
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ q := by positivity
      nlinarith
  have hx := hexp (Nat.log 2 h) hlog
  omega

/-- Rank 256 and deficit at most four times the girth force the logarithmic branch. -/
theorem girth_lt_eight_clog (h k g : ℕ) (hh : 256 ≤ h) (hk : k ≤ 4 * g)
    (hm : g * (3 * (h - 1)) ≤ 4 * Nat.clog 2 (8 * h) * (3 * (h - 1) + k)) :
    g < 8 * Nat.clog 2 (8 * h) := by
  have ht := linear_clog_lt h hh
  have htpos : 0 < Nat.clog 2 (8 * h) := Nat.clog_pos (by decide) (by omega)
  have hbound : 4 * Nat.clog 2 (8 * h) * k ≤
      16 * Nat.clog 2 (8 * h) * g := by nlinarith
  by_contra hn
  have hg : 8 * Nat.clog 2 (8 * h) ≤ g := by omega
  have hdiff : 0 < 3 * (h - 1) - 16 * Nat.clog 2 (8 * h) := by omega
  have hmul := Nat.mul_le_mul_right (3 * (h - 1) - 16 * Nat.clog 2 (8 * h)) hg
  have hsub : 3 * (h - 1) - 16 * Nat.clog 2 (8 * h) +
      16 * Nat.clog 2 (8 * h) = 3 * (h - 1) := by omega
  nlinarith

/-- The square of the radius growth is bounded by the rank. -/
theorem radius_power_lt_rank (h k g : ℕ) (hh : 256 ≤ h) (hk : k ≤ 4 * g)
    (hm : g * (3 * (h - 1)) ≤ 4 * Nat.clog 2 (8 * h) * (3 * (h - 1) + k)) :
    2 ^ (2 * (g / 16)) < 8 * h := by
  have hg := girth_lt_eight_clog h k g hh hk hm
  apply (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mpr
  have hd := Nat.div_mul_le_self g 16
  omega

/-- This crude explicit threshold suffices for the union of all port balls. -/
theorem linear_radius_budget (s : ℕ) (hs : 16 ≤ s) :
    96 * (16 * s + 15) < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    nlinarith

theorem port_ball_budget (h k g : ℕ) (hh : 256 ≤ h) (hk : k ≤ 4 * g)
    (hg : 256 ≤ g)
    (hm : g * (3 * (h - 1)) ≤ 4 * Nat.clog 2 (8 * h) * (3 * (h - 1) + k)) :
    3 * k * 2 ^ (g / 16) < h := by
  have hs : 16 ≤ g / 16 := by omega
  have hsmall := linear_radius_budget (g / 16) hs
  have hdiv : g ≤ 16 * (g / 16) + 15 := by omega
  have hk' : 24 * k < 2 ^ (g / 16) := by omega
  have hsq := radius_power_lt_rank h k g hh hk hm
  rw [show 2 * (g / 16) = g / 16 + g / 16 by omega, pow_add] at hsq
  have hmul := Nat.mul_lt_mul_of_pos_right hk' (by positivity : 0 < 2 ^ (g / 16))
  nlinarith

/-- An exponential eventually exceeds any fixed cubic polynomial. -/
theorem eventually_cubic_budget (C : ℕ) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s → C * (s + 1)^3 < 2 ^ s := by
  open Filter in
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2)
  have hev := ht.eventually_lt_const (by positivity : (0 : ℝ) < 1 / (8 * (C + 1 : ℕ)))
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max S 1, ?_⟩
  intro s hs
  have h₁ : S ≤ s := (le_max_left _ _).trans hs
  have h₂ : 1 ≤ s := (le_max_right _ _).trans hs
  have hb := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ s)).mp (hS s h₁)
  have hc : (0 : ℝ) < 8 * (C + 1 : ℕ) := by positivity
  have hmul := (lt_div_iff₀ hc).mp (show (s : ℝ)^3 < 2^s / (8 * (C+1 : ℕ)) by
    simpa only [one_div_mul_eq_div] using hb)
  have hpoly : (C : ℝ) * (s + 1 : ℕ)^3 ≤ 8 * (C : ℝ) * (s : ℝ)^3 := by
    have hh : ((s + 1 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast (show s+1 ≤ 2*s by omega)
    have hh' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (s+1 : ℕ)) hh 3
    nlinarith
  have hlast : (C : ℝ) * (s + 1 : ℕ)^3 < 2 ^ s := by
    have hc0 : (0 : ℝ) ≤ C := by positivity
    have hs0 : (0 : ℝ) ≤ (s : ℝ)^3 := by positivity
    push_cast at hmul
    nlinarith
  exact_mod_cast hlast


/-- The second pole regime has deficit less than the core edge count. -/
theorem girth_lt_eight_clog_of_rank (h k g : ℕ) (hh : 4 ≤ h) (hk : k ≤ 2 * h)
    (hm : g * (3 * (h - 1)) ≤ 4 * Nat.clog 2 (8 * h) * (3 * (h - 1) + k)) :
    g < 8 * Nat.clog 2 (8 * h) := by
  have ht : 0 < Nat.clog 2 (8 * h) := Nat.clog_pos (by decide) (by omega)
  have hk' : k < 3 * (h - 1) := by omega
  have hp : 0 < 3 * (h - 1) := by omega
  have hb : 4 * Nat.clog 2 (8 * h) * (3 * (h - 1) + k) <
      8 * Nat.clog 2 (8 * h) * (3 * (h - 1)) := by nlinarith
  exact (Nat.mul_lt_mul_right hp).mp (hm.trans_lt hb)

theorem radius_power_lt_rank_of_clog (h g : ℕ)
    (hg : g < 8 * Nat.clog 2 (8 * h)) : 2 ^ (2 * (g / 16)) < 8 * h := by
  apply (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mpr
  have hd := Nat.div_mul_le_self g 16
  omega

/-- A radius budget can include an extra marker root when there are no ports. -/
theorem cover_budget_of_square (h k s : ℕ) (hr : 2 ^ (2 * s) < 8 * h)
    (hk : 24 * (k + 1) < 2 ^ s) : 3 * (k + 1) * 2 ^ s < h := by
  rw [show 2 * s = s + s by omega, pow_add] at hr
  have hp := Nat.mul_lt_mul_of_pos_right hk (by positivity : 0 < 2 ^ s)
  nlinarith

/-- Both numerical budgets hold eventually in the fixed-ratio regime. -/
theorem exists_fixed_ratio_budget (B : ℕ) :
    ∃ D : ℕ, 256 ≤ D ∧ ∀ g k : ℕ, D ≤ g → k ≤ 4*g →
      24*(k+1) < 2^(g/16) ∧ (2*(g/16)+1)*B*(k+2)^2 < 2^(g/16) := by
  obtain ⟨S, hS⟩ := eventually_cubic_budget (8192*B+1536)
  refine ⟨16 * max S 16, by omega, ?_⟩
  intro g k hg hk
  have hs : S ≤ g/16 := by omega
  have hb := hS (g/16) hs
  have hkd : k+2 ≤ 64*(g/16+1) := by omega
  have hcube : g/16+1 ≤ (g/16+1)^3 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ g/16+1) (by decide : 1 ≤ 3)
  constructor
  · have hh : 24*(k+1) ≤ 1536*(g/16+1)^3 := by nlinarith
    nlinarith
  · have hh := Nat.pow_le_pow_left hkd 2
    have hh' := Nat.mul_le_mul_left ((2*(g/16)+1)*B) hh
    nlinarith [Nat.zero_le (B*(g/16+1)^3)]

/-- A logarithmic girth budget controls all larger radii uniformly. -/
theorem exists_logarithmic_budget (B : ℕ) :
    ∃ C : ℕ, 64 ≤ C ∧ ∀ g k l : ℕ, 4 ≤ l → k ≤ 2*l →
      C * Nat.clog 2 (l+2) ≤ g →
      256 ≤ g ∧ 24*(k+1) < 2^(g/16) ∧
        (2*(g/16)+1)*B*(k+2)^2 < 2^(g/16) := by
  obtain ⟨S, hS⟩ := eventually_cubic_budget (64*(B+1))
  let A := max S 8
  refine ⟨16*(2*A+4), by dsimp [A]; omega, ?_⟩
  intro g k l hl hk hg
  let L := Nat.clog 2 (l+2)
  let s := g/16
  let u := s/2
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hpow : l+2 ≤ 2^L := Nat.le_pow_clog (by decide) (l+2)
  have hs : (2*A+4)*L ≤ s := by
    have hh : 16*((2*A+4)*L) ≤ g := by simpa only [Nat.mul_assoc] using hg
    dsimp [s]
    omega
  rw [show (2*A+4)*L = 2*(A*L)+4*L by ring] at hs
  have hA : 8 ≤ A := le_max_right _ _
  have hAS : S ≤ A := le_max_left _ _
  have hAL : A ≤ A*L := by nlinarith
  have huS : S ≤ u := by dsimp [u]; omega
  have huL : 2*L ≤ u := by dsimp [u]; omega
  have hu := hS u huS
  have hsu : s ≤ 2*u+1 := by dsimp [u]; omega
  have hus : 2*u ≤ s := by dsimp [u]; omega
  have hu0 : 1 ≤ (u+1)^3 := one_le_pow₀ (by omega)
  have hu1 : u+1 ≤ (u+1)^3 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ u+1) (by decide : 1 ≤ 3)
  have h48 : 48 < 2^u := by nlinarith
  have h16 : 16*B*(u+1) < 2^u := by nlinarith
  have hLpow : 2^L ≤ 2^u := Nat.pow_le_pow_right (by decide) (by omega)
  have hLpow2 : 2^(2*L) ≤ 2^u := Nat.pow_le_pow_right (by decide) huL
  have hpow2 : 2^u * 2^u ≤ 2^s := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsg : 16*s ≤ g := by dsimp [s]; omega
  refine ⟨by omega, ?_, ?_⟩
  · have hkp : 24*(k+1) ≤ 48*2^L := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right h48 (by positivity : 0 < 2^u)
    nlinarith
  · have hkp : k+2 ≤ 2*(l+2) := by omega
    have hkp' : (k+2)^2 ≤ 4*2^(2*L) := by
      have hh := Nat.pow_le_pow_left (hkp.trans (Nat.mul_le_mul_left 2 hpow)) 2
      simpa only [mul_pow, ← pow_mul, Nat.mul_comm L 2, show (2:ℕ)^2=4 by norm_num] using hh
    have hsmall : (2*s+1)*B*(k+2)^2 ≤ 16*B*(u+1)*2^u := by
      calc
        (2*s+1)*B*(k+2)^2 ≤ (2*s+1)*B*(4*2^(2*L)) := Nat.mul_le_mul_left _ hkp'
        _ = ((2*s+1)*B*4)*2^(2*L) := by ring
        _ ≤ ((2*s+1)*B*4)*2^u := Nat.mul_le_mul_left _ hLpow2
        _ = (4*(2*s+1)*B)*2^u := by ring
        _ ≤ (16*(u+1)*B)*2^u := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (by omega))
        _ = 16*B*(u+1)*2^u := by ring
    have hmul := Nat.mul_lt_mul_of_pos_right h16 (by positivity : 0 < 2^u)
    exact hsmall.trans_lt (hmul.trans_le hpow2)

end Erdos1016.ExactMaximumSupport.LargeGirth.MooreGrowth

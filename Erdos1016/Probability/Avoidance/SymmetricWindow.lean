import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Finite symmetric windows

A bounded monotone sequence of integer masses has a first window with
small relative increment. The number of expansion steps is bounded in
terms of the final mass, rather than the ambient graph order.
-/
noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Probability.SymmetricWindow

local instance windowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def Stops (M : ℕ → ℕ) (n : ℕ) : Prop :=
  (M (n+1) : ℝ) - M n ≤ (M n : ℝ)/(24*(Real.logb 2 (M n))^2)

/-- A bounded integer mass sequence cannot have a positive increment forever. -/
theorem exists_stop (M : ℕ → ℕ) (hstart : 0 < M 0)
    (hbounded : ∃ B, ∀ n, M n ≤ B) : ∃ n, Stops M n := by
  obtain ⟨B, hB⟩ := hbounded
  by_contra hn
  have hstep (n : ℕ) : M n < M (n+1) := by
    have hh : ¬ Stops M n := fun h => hn ⟨n, h⟩
    have hd : (0 : ℝ) ≤ (M n : ℝ)/(24*(Real.logb 2 (M n))^2) := by positivity
    have hi : (M n : ℝ) < M (n+1) := by
      unfold Stops at hh
      push_neg at hh
      linarith
    exact_mod_cast hi
  have hgrow (n : ℕ) : M 0 + n ≤ M n := by
    induction n with
    | zero => omega
    | succ n ih => have := hstep n; omega
  have := hgrow B
  have := hB B
  omega

/-- A small logarithmic increment has a uniform logarithmic lower bound. -/
theorem log_growth_lower {L : ℝ} (hL : 1 ≤ L) :
    1/(48*L^2) ≤ Real.log (1+1/(24*L^2)) := by
  have hL2 : 1 ≤ L^2 := by nlinarith
  have hden : 0 < 24*L^2 := by positivity
  let u := 1/(24*L^2)
  have hu : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by apply (div_le_iff₀ hden).mpr; nlinarith
  have hh := Real.le_log_one_add_of_nonneg hu
  have hsmall : u/2 ≤ 2*u/(u+2) := by
    apply (le_div_iff₀ (by positivity : 0 < u+2)).mpr
    nlinarith
  calc
    _ = u/2 := by dsimp [u]; ring
    _ ≤ _ := hsmall.trans hh

/-- The first stopped window needs at most 48 times the cube of its binary log mass. -/
theorem stopping_index_le (M : ℕ → ℕ) (hmono : Monotone M) (hstart : 2 ≤ M 0)
    (N : ℕ) (hprior : ∀ k < N, ¬ Stops M k) :
    (N : ℝ) ≤ 48*(Real.logb 2 (M N))^3 := by
  let μ : ℝ := M N
  let L := Real.logb 2 μ
  have hμ : 2 ≤ μ := by dsimp [μ]; exact_mod_cast hstart.trans (hmono (Nat.zero_le N))
  have hμpos : 0 < μ := by linarith
  have hL : 1 ≤ L := by
    have hh : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 μ :=
      (Real.logb_le_logb (by norm_num) (by norm_num) hμpos).mpr hμ
    simpa [L] using hh
  have hLpos : 0 < L := by linarith
  let a := 1+1/(24*L^2)
  have ha : 0 < a := by positivity
  have hstep (k : ℕ) (hk : k < N) : (M k : ℝ)*a ≤ M (k+1) := by
    have hklo : (2 : ℝ) ≤ M k := by exact_mod_cast hstart.trans (hmono (Nat.zero_le k))
    have hkpos : (0 : ℝ) < M k := by linarith
    have hkhi : (M k : ℝ) ≤ μ := by dsimp [μ]; exact_mod_cast hmono hk.le
    have hlk : 0 < Real.logb 2 (M k) := Real.logb_pos (by norm_num) (by linarith)
    have hlog : Real.logb 2 (M k) ≤ L :=
      (Real.logb_le_logb (by norm_num) hkpos hμpos).mpr hkhi
    have hsq : (Real.logb 2 (M k))^2 ≤ L^2 := by nlinarith
    have hdiv : (M k : ℝ)/(24*L^2) ≤ (M k : ℝ)/(24*(Real.logb 2 (M k))^2) :=
      div_le_div_of_nonneg_left hkpos.le (by positivity) (by nlinarith)
    have hh := hprior k hk
    unfold Stops at hh
    push_neg at hh
    dsimp [a]
    have he : (M k : ℝ)*(1+1/(24*L^2)) = (M k : ℝ) + (M k : ℝ)/(24*L^2) := by ring
    rw [he]
    linarith
  have hgrow (k : ℕ) (hk : k ≤ N) : a^k ≤ (M k : ℝ) := by
    induction k with
    | zero => simp only [pow_zero]; exact (by exact_mod_cast hstart : (2 : ℝ) ≤ M 0).trans' (by norm_num)
    | succ k ih =>
        have hk' : k < N := by omega
        calc
          a^(k+1) = a^k*a := pow_succ _ _
          _ ≤ (M k : ℝ)*a := mul_le_mul_of_nonneg_right (ih hk'.le) ha.le
          _ ≤ _ := hstep k hk'
  have hpow : a^N ≤ μ := hgrow N le_rfl
  have hlogpow := Real.log_le_log (pow_pos ha N) hpow
  rw [Real.log_pow] at hlogpow
  have hgrowth : 1/(48*L^2) ≤ Real.log a := log_growth_lower hL
  have hweight : (N : ℝ)/(48*L^2) ≤ Real.log μ := by
    calc
      _ = (N : ℝ)*(1/(48*L^2)) := by ring
      _ ≤ (N : ℝ)*Real.log a := mul_le_mul_of_nonneg_left hgrowth (Nat.cast_nonneg N)
      _ ≤ _ := hlogpow
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hidentity : Real.log μ = L * Real.log 2 := by
    dsimp [L, Real.logb]
    field_simp
  have hln : Real.log μ ≤ L := by rw [hidentity]; nlinarith
  have hh := (div_le_iff₀ (by positivity : 0 < 48*L^2)).mp (hweight.trans hln)
  nlinarith

/-- Choose the first stopped window and retain both its boundary and span bounds. -/
theorem exists_short_stopped_window (M : ℕ → ℕ) (hmono : Monotone M)
    (hstart : 2 ≤ M 0) (hbounded : ∃ B, ∀ n, M n ≤ B) :
    ∃ N, Stops M N ∧ (N : ℝ) ≤ 48*(Real.logb 2 (M N))^3 := by
  have he := exists_stop M (by omega) hbounded
  refine ⟨Nat.find he, Nat.find_spec he, ?_⟩
  apply stopping_index_le M hmono hstart
  intro k hk
  exact Nat.find_min he hk

/-- A fixed multiple of the fifth logarithmic power is eventually below the square root. -/
theorem eventually_window_overhead_budget :
    ∀ᶠ μ : ℝ in atTop, 1 ≤ Real.logb 2 μ ∧
      3000*(Real.logb 2 μ)^5 ≤ Real.sqrt μ := by
  have h := (isLittleO_log_rpow_rpow_atTop (5 : ℝ)
    (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
  have hraw : Tendsto (fun μ : ℝ => (Real.log μ)^5 / Real.sqrt μ) atTop (𝓝 0) := by
    convert h using 1
    ext μ
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log μ) 5]
    norm_num
  have hh := hraw.div_const ((Real.log 2)^5)
  have hb : Tendsto (fun μ : ℝ => (Real.logb 2 μ)^5 / Real.sqrt μ) atTop (𝓝 0) := by
    convert hh using 1
    · ext μ; simp only [Real.logb]; ring
    · simp
  have hlog : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  filter_upwards [hb.eventually_lt_const (by norm_num : (0 : ℝ) < 1/3000),
    hlog.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with μ hh hl hp
  refine ⟨hl, ?_⟩
  have hd := (div_lt_iff₀ (Real.sqrt_pos.mpr hp)).mp hh
  nlinarith

/-- The final marker-incidence overhead fits the remaining half of the boundary budget. -/
theorem marker_overhead_le {μ L k : ℝ} (hμ : 0 ≤ μ) (hL : 1 ≤ L) (hk : 0 ≤ k)
    (hk2 : k^2 ≤ μ) (hbudget : 3000*L^5 ≤ Real.sqrt μ) :
    3*k*(96*L^3+3) ≤ μ/(8*L^2) := by
  have hroot := Real.sq_sqrt hμ
  have hsqrt := Real.sqrt_nonneg μ
  have hkroot : k ≤ Real.sqrt μ := by nlinarith
  have hmass : 3000*k*L^5 ≤ μ := by
    have hh := mul_le_mul hbudget hkroot hk (by positivity : 0 ≤ Real.sqrt μ)
    nlinarith
  have hp : L^2 ≤ L^5 := by
    have hh : 1 ≤ L^3 := one_le_pow₀ hL
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg L)
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 8*L^2)).mpr
  have hh := mul_le_mul_of_nonneg_left hp hk
  nlinarith

end Erdos1016.Probability.SymmetricWindow

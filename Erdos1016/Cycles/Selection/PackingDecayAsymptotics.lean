import Erdos1016.Cycles.Selection.CorePackingProbability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-!
# The MANY exponent a < 1/4

The source's polynomial conflict bound gives an explicit majorant:
  11 C B^2 (log n)^2 / n^(1/4-a).
The geometric theorem is used, rather than an assumed independence bound.
The floor/log cutoff and the prescribed packing threshold can be supplied
by their displayed finite inequalities; no convergence-rate premise is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyManyAsymptoticsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem natCeil_le_add_one (x : ℝ) (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 := by
  by_cases hz : Nat.ceil x = 0
  · rw [hz, Nat.cast_zero]
    linarith
  · have hn : 1 ≤ Nat.ceil x := by omega
    have hcast : ((Nat.ceil x - 1 : ℕ) : ℝ) + 1 = (Nat.ceil x : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hn
    have hxpred : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
      by_contra h
      have hle : x ≤ ((Nat.ceil x - 1 : ℕ) : ℝ) := le_of_not_gt h
      have hceil : Nat.ceil x ≤ Nat.ceil x - 1 := (Nat.ceil_le).2 hle
      omega
    linarith

/-- A numerical upper bound for the exact source conflict polynomial. -/
theorem manyCycleConflictBound_le (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (D : ℕ) (hD : 1 ≤ D) :
    ((manyCycleConflictBound κ D + 1 : ℕ) : ℝ) ≤ 11 * (D : ℝ) ^ 2 / κ := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hs := natCeil_le_add_one ((D : ℝ) / κ) (div_nonneg hD0 hκ.le)
  have ht := natCeil_le_add_one ((2 * (D : ℝ)) / κ) (by positivity)
  have hexp : ((manyCycleConflictBound κ D + 1 : ℕ) : ℝ) =
      (D : ℝ) * ((Nat.ceil ((2 * (D : ℝ)) / κ) : ℝ) + 2) +
        2 * (Nat.ceil ((D : ℝ) / κ) : ℝ) + 2 := by
    simp only [manyCycleConflictBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hpre : ((manyCycleConflictBound κ D + 1 : ℕ) : ℝ) ≤
      2 * (D : ℝ) ^ 2 / κ + 3 * D + 2 * ((D : ℝ) / κ) + 4 := by
    rw [hexp]
    have ht' : (Nat.ceil ((2 * (D : ℝ)) / κ) : ℝ) + 2 ≤
        2 * (D : ℝ) / κ + 3 := by linarith
    have hs' : 2 * (Nat.ceil ((D : ℝ) / κ) : ℝ) + 2 ≤
        2 * ((D : ℝ) / κ) + 4 := by linarith
    have hfirst := mul_le_mul_of_nonneg_left ht' hD0
    calc
      _ = (D : ℝ) * (Nat.ceil ((2 * (D : ℝ)) / κ) + 2) +
          (2 * (Nat.ceil ((D : ℝ) / κ) : ℝ) + 2) := by ring
      _ ≤ (D : ℝ) * (2 * (D : ℝ) / κ + 3) +
          (2 * ((D : ℝ) / κ) + 4) := add_le_add hfirst hs'
      _ = _ := by ring
  have hDd : (D : ℝ) ≤ (D : ℝ) ^ 2 / κ := by
    apply (le_div_iff₀ hκ).2
    nlinarith [mul_nonneg hD0 (sub_nonneg.mpr (hκ1.trans hDr))]
  have hDdiv : (D : ℝ) / κ ≤ (D : ℝ) ^ 2 / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le
    nlinarith
  have hone : (1 : ℝ) ≤ (D : ℝ) ^ 2 / κ := hDr.trans hDd
  let X : ℝ := (D : ℝ) ^ 2 / κ
  calc
    _ ≤ 2 * X + 3 * (D : ℝ) + 2 * ((D : ℝ) / κ) + 4 := by
      convert hpre using 1 <;> ring
    _ ≤ 2 * X + 3 * X + 2 * X + 4 * X := by
      have hthree : 3 * (D : ℝ) ≤ 3 * X :=
        mul_le_mul_of_nonneg_left hDd (by norm_num)
      have htwo : 2 * ((D : ℝ) / κ) ≤ 2 * X :=
        mul_le_mul_of_nonneg_left hDdiv (by norm_num)
      have hfour : (4 : ℝ) ≤ 4 * X :=
        by nlinarith [hone]
      linarith
    _ = 11 * X := by ring
    _ = 11 * (D : ℝ) ^ 2 / κ := by simp [X]; ring

/-- The finite polynomial majorant in manuscript (9.3). `p` is the actual
packing cardinality, not a count of selected successful parity states. -/
theorem many_bound_power_majorant
    (n κ a C B : ℝ) (D p : ℕ)
    (hn : 1 ≤ n) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hD : 1 ≤ D)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hrecip : 1 / κ ≤ C * n ^ a)
    (hcutoff : (D : ℝ) ≤ B * Real.log n)
    (hbinary : (2 : ℝ) ^ D ≤ n ^ (1 / 2 : ℝ))
    (hpacking : n ^ (3 / 4 : ℝ) ≤ (p : ℝ)) :
    (2 : ℝ) ^ D * (manyCycleConflictBound κ D + 1) / p ≤
      (11 * C * B ^ 2) * (Real.log n) ^ 2 / n ^ ((1 / 4 : ℝ) - a) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlogB : 0 ≤ B * Real.log n := mul_nonneg hB hlog
  have hDs : (D : ℝ) ^ 2 ≤ (B * Real.log n) ^ 2 := by
    have hDn := Nat.cast_nonneg (α := ℝ) D
    nlinarith
  have hJ := manyCycleConflictBound_le κ hκ hκ1 D hD
  have hJ' : ((manyCycleConflictBound κ D + 1 : ℕ) : ℝ) ≤
      11 * (B * Real.log n) ^ 2 * (C * n ^ a) := by
    calc
      _ ≤ 11 * (D : ℝ) ^ 2 / κ := hJ
      _ = 11 * (D : ℝ) ^ 2 * (1 / κ) := by ring
      _ ≤ 11 * (B * Real.log n) ^ 2 * (1 / κ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith :
          11 * (D : ℝ) ^ 2 ≤ 11 * (B * Real.log n) ^ 2) (by positivity)
      _ ≤ 11 * (B * Real.log n) ^ 2 * (C * n ^ a) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
  have hJ'' : (manyCycleConflictBound κ D : ℝ) + 1 ≤
      11 * (B * Real.log n) ^ 2 * (C * n ^ a) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hJ'
  have hJ0 : (0 : ℝ) ≤ (manyCycleConflictBound κ D : ℝ) + 1 := by positivity
  have hnum : (2 : ℝ) ^ D * (manyCycleConflictBound κ D + 1) ≤
      n ^ (1 / 2 : ℝ) * (11 * (B * Real.log n) ^ 2 * (C * n ^ a)) :=
    mul_le_mul hbinary hJ'' hJ0 (Real.rpow_nonneg hn0.le _)
  have hp0 : (0 : ℝ) < p := (Real.rpow_pos_of_pos hn0 _).trans_le hpacking
  have hden0 : 0 < n ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hnum0 : 0 ≤ n ^ (1 / 2 : ℝ) *
      (11 * (B * Real.log n) ^ 2 * (C * n ^ a)) := by positivity
  have hratio : (2 : ℝ) ^ D * (manyCycleConflictBound κ D + 1) / p ≤
      n ^ (1 / 2 : ℝ) * (11 * (B * Real.log n) ^ 2 * (C * n ^ a)) /
        n ^ (3 / 4 : ℝ) := by
    apply (div_le_div_iff₀ hp0 hden0).2
    calc
      _ ≤ (n ^ (1 / 2 : ℝ) * (11 * (B * Real.log n) ^ 2 * (C * n ^ a))) *
          n ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right hnum hden0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hpacking hnum0
  have hpowers : n ^ (1 / 2 : ℝ) * n ^ a / n ^ (3 / 4 : ℝ) =
      1 / n ^ ((1 / 4 : ℝ) - a) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_sub hn0]
    have he : (1 / 2 : ℝ) + a - 3 / 4 = -((1 / 4 : ℝ) - a) := by ring
    rw [he, Real.rpow_neg hn0.le]
    simp only [one_div]
  calc
    _ ≤ n ^ (1 / 2 : ℝ) * (11 * (B * Real.log n) ^ 2 * (C * n ^ a)) /
        n ^ (3 / 4 : ℝ) := hratio
    _ = (11 * C * B ^ 2) * (Real.log n) ^ 2 *
        (n ^ (1 / 2 : ℝ) * n ^ a / n ^ (3 / 4 : ℝ)) := by ring
    _ = _ := by rw [hpowers]; ring







end Erdos1016.CycleSupply

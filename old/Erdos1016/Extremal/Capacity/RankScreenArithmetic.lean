import Erdos1016.Extremal.Capacity.ShortcutCalibration
import Erdos1016.Extremal.Capacity.OneShotRestriction

set_option autoImplicit false

/-!
# Finite arithmetic for the short-cycle witness rank screen

This isolates the source's `<5R` contradiction from its graph-composition
input.  The missing graph-specific estimate is kept explicit as
`hcomposition`; no capacity or probability claim is smuggled into the screen.
-/

noncomputable section

namespace Erdos1016.Proof.WitnessRankScreenArithmetic

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.Capacity
open Erdos1016.Proof.CapacityCalibrationShortcut

/-- A competitive cycle count and the source's composition estimate force
the selected witness support rank below `5R`. -/
theorem selectedWitness_rank_lt_fiveR
    (R r rw m : ℕ) (lambda : ℝ) (hR : 5 ≤ R) (hr : 5 * R + 2 ≤ r)
    (hsize : m + 1 ≤ 2 ^ (4 * R))
    (hcompetitive : (R : ℝ) / (2 : ℝ) ^ (R + 1) ≤
      lambda)
    (hcomposition : lambda ≤
      ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ rw +
        (m : ℝ) / (2 : ℝ) ^ r) : rw < 5 * R := by
  by_contra hnot
  have hrw : 5 * R ≤ rw := by omega
  have hpowW : (2 : ℝ) ^ (5 * R) ≤ (2 : ℝ) ^ rw := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrw)
  have hpowG : (2 : ℝ) ^ (5 * R + 2) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))
  have hnum1 : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * R) := by
    exact_mod_cast hsize
  have hnum2 : (m : ℝ) ≤ (2 : ℝ) ^ (4 * R) := by
    exact_mod_cast (Nat.le_of_succ_le hsize)
  have hprod1 : ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ R ≤ (2 : ℝ) ^ rw := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * R) * (2 : ℝ) ^ R :=
        mul_le_mul_of_nonneg_right hnum1 (by positivity)
      _ = (2 : ℝ) ^ (5 * R) := by
        have hexp : 4 * R + R = 5 * R := by omega
        rw [← pow_add, hexp]
      _ ≤ (2 : ℝ) ^ rw := hpowW
  have hprod2 : (m : ℝ) * (2 : ℝ) ^ (R + 2) ≤ (2 : ℝ) ^ r := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * R) * (2 : ℝ) ^ (R + 2) :=
        mul_le_mul_of_nonneg_right hnum2 (by positivity)
      _ = (2 : ℝ) ^ (5 * R + 2) := by
        have hexp : 4 * R + (R + 2) = 5 * R + 2 := by omega
        rw [← pow_add, hexp]
      _ ≤ (2 : ℝ) ^ r := hpowG
  have hdenW : 0 < (2 : ℝ) ^ rw := by positivity
  have hdenR : 0 < (2 : ℝ) ^ R := by positivity
  have hdenG : 0 < (2 : ℝ) ^ r := by positivity
  have hfirst : ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ rw ≤
      1 / (2 : ℝ) ^ R := by
    apply (div_le_div_iff₀ hdenW hdenR).2
    simpa using hprod1
  have hsecond : (m : ℝ) / (2 : ℝ) ^ r ≤
      1 / (2 : ℝ) ^ (R + 2) := by
    apply (div_le_div_iff₀ hdenG (by positivity)).2
    simpa using hprod2
  have hsum : ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ rw +
      (m : ℝ) / (2 : ℝ) ^ r ≤ (5 / 4 : ℝ) / (2 : ℝ) ^ R := by
    have hpow : (2 : ℝ) ^ (R + 2) = (2 : ℝ) ^ R * 4 := by
      rw [pow_add]
      norm_num
    rw [hpow] at hsecond
    have hsum' : 1 / (2 : ℝ) ^ R + 1 / ((2 : ℝ) ^ R * 4) =
        (5 / 4 : ℝ) / (2 : ℝ) ^ R := by ring
    calc
      _ ≤ 1 / (2 : ℝ) ^ R + 1 / ((2 : ℝ) ^ R * 4) := add_le_add hfirst hsecond
      _ = _ := hsum'
  have hRreal : (5 : ℝ) ≤ R := by exact_mod_cast hR
  have hstrict : (5 / 4 : ℝ) / (2 : ℝ) ^ R <
      (R : ℝ) / (2 : ℝ) ^ (R + 1) := by
    have hden : 0 < (2 : ℝ) ^ R := by positivity
    have hden' : 0 < (2 : ℝ) ^ (R + 1) := by positivity
    apply (div_lt_div_iff₀ hden hden').2
    rw [pow_succ]
    nlinarith [hRreal, hden]
  have hcontra : (R : ℝ) / (2 : ℝ) ^ (R + 1) ≤
      (5 / 4 : ℝ) / (2 : ℝ) ^ R :=
    hcompetitive.trans (hcomposition.trans hsum)
  exact (not_lt_of_ge hcontra) hstrict

/-- The canonical support of one selected cycle per required length has rank
at least `2R` and, by the one-shot restriction estimate, below `5R`. -/
theorem canonicalWitness_rank_screen
    (G : PhysicalGraph) (R : ℕ) (hR : 6 ≤ R)
    (hr : 5 * R + 2 ≤ G.cycleRank)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1))
    (hcycleCount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank) :
    2 * R ≤ (witnessSupportGraph G
      (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).cycleRank ∧
    (witnessSupportGraph G
      (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).cycleRank < 5 * R := by
  let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
  let E := witnessSupportEdges G F
  let W := witnessSupportGraph G F
  have hwcov : W.InitialCoverage (2 ^ (2 * R) + 1) :=
    canonicalWitnessSupport_initialCoverage G (2 ^ (2 * R) + 1) hcov
  have hlow := W.coverage_bound hwcov
  have hpow : 2 ^ (2 * R) ≤ 2 ^ W.cycleRank := by omega
  have hranklow : 2 * R ≤ W.cycleRank :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow
  have hsize : E.card + 1 ≤ 2 ^ (4 * R) := by
    dsimp [E, F]
    exact canonicalWitnessSupport_add_one_le_power G R (by omega) hcov
  have hcal := calibration_lower_bound_of_six_le R hR
  have hcompetitive : (R : ℝ) / (2 : ℝ) ^ (R + 1) ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
    have hpow : (2 : ℝ) ^ (R + 1) = (2 : ℝ) ^ R * 2 := by rw [pow_succ]
    have hlower : (R : ℝ) / (2 : ℝ) ^ (R + 1) ≤ tailCapacity R / 2 := by
      calc
        (R : ℝ) / (2 : ℝ) ^ (R + 1) =
            ((R : ℝ) / (2 : ℝ) ^ R) / 2 := by rw [hpow]; ring
        _ ≤ tailCapacity R / 2 :=
          div_le_div_of_nonneg_right hcal (by norm_num)
    exact hlower.trans hcycleCount
  have hcomp : (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      ((E.card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ W.cycleRank +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
    simpa [E, W, F] using G.canonicalWitness_oneShot_composition R hcov
  have hupper := selectedWitness_rank_lt_fiveR R G.cycleRank W.cycleRank E.card
    ((G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank)
    (by omega) hr hsize hcompetitive hcomp
  exact ⟨hranklow, hupper⟩

end Erdos1016.Proof.WitnessRankScreenArithmetic

import Erdos1016.Extremal.Construction.RecursiveShortcutGraph
import Erdos1016.Extremal.PancyclicGraphTransfer
import Erdos1016.Extremal.Capacity.Basic
import Erdos1016.Extremal.Capacity.Tail

set_option autoImplicit false

/-!
# A sparse pancyclic witness for capacity calibration

The recursive shortcut graph from the extremal construction is a convenient
fully formal substitute for a fan graph.  Its order is `2^k + k`; its excess
is at most the number of added shortcut edges.  Consequently it gives a
calibration lower bound whenever its rank budget fits the capacity index.
-/

noncomputable section

namespace Erdos1016.Proof.CapacityCalibrationShortcut

open Erdos1016
open Erdos1016.Extremal

private theorem succ_le_expTower (n : ℕ) : n + 1 ≤ expTower n := by
  induction n with
  | zero => simp [expTower]
  | succ n ih =>
      rw [expTower]
      calc
        n + 2 ≤ expTower n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ expTower n := succ_le_two_pow (expTower n)

private theorem logStar_le_pred_of_pos {n : ℕ} (hn : 0 < n) :
    logStar n ≤ n - 1 := by
  have hpow : n ≤ expTower (n - 1) := by
    have h := succ_le_expTower (n - 1)
    rwa [Nat.sub_add_cancel (by omega)] at h
  exact logStar_min_le hpow

private theorem pow_two_dominates_linear (n : ℕ) (hn : 3 ≤ n) :
    n + 3 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      rw [hpow]
      omega

/-- The recursive shortcut construction witnesses at least `2^k+k` covered
cycle lengths at rank at most its explicit chord budget plus one. -/
theorem initialCapacity_ge_shortcut_order (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k + k ≤ initialCapacity
      (k + (recursiveClosureLevels k).length + 2) := by
  let n := shortcutSize k + 1
  have hn : 3 ≤ n := by
    dsimp [n]
    rw [shortcutSize_eq]
    have hp : 4 ≤ 2 ^ k := by
      exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
    have hp' : 2 ≤ 2 ^ k := by omega
    omega
  have hnk : shortcutSize k + 1 ≤ n := le_rfl
  let G : SimpleGraph (Fin n) := recursiveShortcutGraph n k hnk
  have hpan : Problem1016.IsPancyclic G := by
    simpa [G, n, shortcutSize, shortcutSize_eq] using
      (recursiveShortcutGraph_pancyclic k hk)
  have hfinal : Extremal.IsPancyclic (Problem1016.physicalOfSimpleGraph G) :=
    Problem1016.final_isPancyclic_of_isPancyclic G hn hpan
  have hconn : G.Connected := by
    have hc : (Problem1016.physicalOfSimpleGraph G).toSimpleGraph.Connected := hfinal.1
    rw [Problem1016.physicalOfSimpleGraph_toSimpleGraph] at hc
    exact hc
  have hrank := Problem1016.physicalOfSimpleGraph_rank_eq_excess_add_one
    G hconn hn hpan
  have hexcess := recursiveShortcutGraph_excess_le n k hnk hn
  have hexcess' : Problem1016.excess n G ≤
      (recursiveShortcutExtraEdges n k hnk).card := by
    simpa [G] using hexcess
  have hcard := recursiveShortcutExtraEdges_card_le n k hnk
  have hrankbound : (Problem1016.physicalOfSimpleGraph G).cycleRank ≤
      k + (recursiveClosureLevels k).length + 2 := by
    rw [hrank]
    calc
      Problem1016.excess n G + 1 ≤
          (recursiveShortcutExtraEdges n k hnk).card + 1 := Nat.add_le_add_right hexcess' 1
      _ ≤ k + (recursiveClosureLevels k).length + 2 := by omega
  have hcoverage : (Problem1016.physicalOfSimpleGraph G).InitialCoverage n := by
    simpa [Extremal.IsPancyclic, Problem1016.physicalOfSimpleGraph_vertexCount] using hfinal.2.2
  have hcap := coverage_le_initialCapacity
    (Problem1016.physicalOfSimpleGraph G) hrankbound hcoverage
  have hnval : n = 2 ^ k + k := by
    dsimp [n]
    rw [shortcutSize_eq]
    have hp : 0 < 2 ^ k := Nat.pow_pos (by omega)
    omega
  rw [hnval] at hcap
  exact hcap

/-- Tail capacity dominates the normalized coverage surplus of every
recursive shortcut witness whose rank fits the requested index. -/
theorem shortcut_surplus_le_tailCapacity (R k : ℕ) (hk : 2 ≤ k)
    (hrank : k + (recursiveClosureLevels k).length + 2 ≤ R) :
    (((2 ^ k + k : ℕ) : ℝ) - 2) / (2 : ℝ) ^ R ≤ tailCapacity R := by
  have hcap := initialCapacity_ge_shortcut_order k hk
  have hmono := initialCapacity_mono hrank
  have horder : 2 ^ k + k ≤ initialCapacity R := hcap.trans hmono
  have hmem : initialCapacityExcess R ∈
      {x : ℝ | ∃ n : ℕ, R ≤ n ∧ x = initialCapacityExcess n} := by
    exact ⟨R, le_rfl, rfl⟩
  have hbounded : BddAbove
      {x : ℝ | ∃ n : ℕ, R ≤ n ∧ x = initialCapacityExcess n} := by
    refine ⟨1, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    exact initialCapacityExcess_le_one n
  have hle : initialCapacityExcess R ≤ tailCapacity R := by
    unfold tailCapacity
    exact le_csSup hbounded hmem
  unfold initialCapacityExcess at hle
  have hI : 2 ≤ initialCapacity R := two_le_initialCapacity R
  have hK : 2 ≤ 2 ^ k + k := by
    have hp : 4 ≤ 2 ^ k := by
      exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk
    have hp' : 2 ≤ 2 ^ k := by omega
    omega
  have hnumNat : 2 ^ k + k - 2 ≤ initialCapacity R - 2 := by omega
  have hnumCast : (((2 ^ k + k - 2 : ℕ) : ℝ)) ≤
      ((initialCapacity R - 2 : ℕ) : ℝ) := by exact_mod_cast hnumNat
  have hnum : (((2 ^ k + k : ℕ) : ℝ) - 2) ≤
      (initialCapacity R : ℝ) - 2 := by
    simpa [Nat.cast_sub hK, Nat.cast_sub hI] using hnumCast
  have hpow : 0 < (2 : ℝ) ^ R := by positivity
  rw [div_le_iff₀ hpow] at hle ⊢
  nlinarith

/-- The desired `R · 2⁻ᴿ` calibration follows whenever one shortcut witness
has order at least `R+2` and its explicit rank budget at most `R`. -/
theorem calibration_lower_bound_of_shortcut (R k : ℕ) (hk : 2 ≤ k)
    (horder : R + 2 ≤ 2 ^ k + k)
    (hrank : k + (recursiveClosureLevels k).length + 2 ≤ R) :
    (R : ℝ) / (2 : ℝ) ^ R ≤ tailCapacity R := by
  have hs := shortcut_surplus_le_tailCapacity R k hk hrank
  have hnat : R ≤ 2 ^ k + k - 2 := by omega
  have horder2 : 2 ≤ 2 ^ k + k := by omega
  have hcast : (R : ℝ) ≤ ((2 ^ k + k - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hnum : (R : ℝ) ≤ ((2 ^ k + k : ℕ) : ℝ) - 2 := by
    simpa [Nat.cast_sub horder2] using hcast
  have hden : 0 < (2 : ℝ) ^ R := by positivity
  exact (div_le_div_of_nonneg_right hnum (le_of_lt hden)).trans hs

/-- Uniform calibration from the recursive shortcut witness for every
`R ≥ 6`, choosing its main shortcut level to be `R/2`. -/
theorem calibration_lower_bound_of_six_le (R : ℕ) (hR : 6 ≤ R) :
    (R : ℝ) / (2 : ℝ) ^ R ≤ tailCapacity R := by
  let k := R / 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hiter : shortcutIterationCount k ≤ k - 2 := by
    have hstar := logStar_le_pred_of_pos (show 0 < k by omega)
    have hcount := shortcutIterationCount_eq_logStar_sub_one hk
    omega
  have hlen : (recursiveClosureLevels k).length = shortcutIterationCount k :=
    recursiveClosureLevels_length k
  have hrank : k + (recursiveClosureLevels k).length + 2 ≤ R := by
    rw [hlen]
    have htwok : 2 * k ≤ R := by
      dsimp [k]
      omega
    omega
  have hlin : k + 3 ≤ 2 ^ k := by
    exact pow_two_dominates_linear k (by omega)
  have hdiv : R ≤ 2 * k + 1 := by dsimp [k]; omega
  have horder : R + 2 ≤ 2 ^ k + k := by omega
  exact calibration_lower_bound_of_shortcut R k hk horder hrank

end Erdos1016.Proof.CapacityCalibrationShortcut

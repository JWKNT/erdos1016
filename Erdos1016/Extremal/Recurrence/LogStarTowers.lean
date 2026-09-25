import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Tower characterization of binary log-star

The convention is the paper's: `logStar n` is the least number of successive
binary logarithms needed to reach a value at most one. Equivalently, it is the
least `j` for which `n ≤ tower j`, where `tower 0 = 1` and
`tower (j+1) = 2^(tower j)`.
-/

namespace Erdos1016.Extremal

/-- The binary exponential tower, with bottom level one. -/
def expTower : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ expTower j

lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  exact Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))

lemma le_expTower (n : ℕ) : n ≤ expTower n := by
  induction n with
  | zero => simp [expTower]
  | succ n ih =>
      rw [expTower]
      have htpos : 0 < expTower n := by
        cases n with
        | zero => simp [expTower]
        | succ n => simp [expTower]
      calc
        n + 1 ≤ expTower n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ expTower n := succ_le_two_pow (expTower n)

/-- Every tower level is strictly smaller than the next one. -/
lemma expTower_lt_succ (j : ℕ) : expTower j < expTower (j + 1) := by
  rw [expTower]
  exact Nat.lt_two_pow_self (n := expTower j)

/-- The tower levels are strictly increasing. -/
theorem expTower_strictMono : StrictMono expTower :=
  strictMono_nat_of_lt_succ expTower_lt_succ

/-- There is always a tower level at least as large as `n`. -/
theorem exists_expTower_ge (n : ℕ) : ∃ j, n ≤ expTower j :=
  ⟨n, le_expTower n⟩

/-- Binary log-star, defined as the least tower height that dominates `n`.
For `n ≥ 1` this is exactly the repeated-log stopping convention in the paper. -/
noncomputable def logStar (n : ℕ) : ℕ :=
  Nat.find (exists_expTower_ge n)

@[simp] theorem le_expTower_logStar (n : ℕ) : n ≤ expTower (logStar n) :=
  Nat.find_spec (exists_expTower_ge n)

theorem logStar_min_le {n j : ℕ} (h : n ≤ expTower j) : logStar n ≤ j :=
  Nat.find_min' (exists_expTower_ge n) h

theorem logStar_mono {n m : ℕ} (h : n ≤ m) : logStar n ≤ logStar m := by
  apply logStar_min_le
  exact h.trans (le_expTower_logStar m)

@[simp] theorem logStar_one : logStar 1 = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hmin := logStar_min_le (n := 1) (j := 0) (by simp [expTower])
  omega

/-- The least tower height dominating a tower is its own height. -/
@[simp] theorem logStar_expTower (j : ℕ) : logStar (expTower j) = j := by
  apply le_antisymm
  · exact logStar_min_le (n := expTower j) (j := j) le_rfl
  · by_contra hlt
    have hlt' : logStar (expTower j) < j := by omega
    have hstrict := expTower_strictMono hlt'
    have hspec := le_expTower_logStar (expTower j)
    exact (not_lt_of_ge hspec) hstrict



end Erdos1016.Extremal

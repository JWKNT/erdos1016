import Erdos1016.Extremal.Construction.ShortcutChain

set_option autoImplicit false

/-!
# Arithmetic bookkeeping for the §18 upper construction

This module formalizes the rounding and count estimates after the binary
shortcut-chain graph lemma. Graph insertion into a given `n`-cycle is separate.
-/

namespace Erdos1016.Extremal

/-- The total original length used by the first `k` shortcut segments. -/
lemma shortcutSize_eq (k : ℕ) : shortcutSize k = 2 ^ k + k - 1 := by
  induction k with
  | zero => simp [shortcutSize, shortcutBoundary]
  | succ k ih =>
      change shortcutBoundary (k + 1) = 2 ^ (k + 1) + (k + 1) - 1
      rw [shortcutBoundary_succ, ← shortcutSize, ih, pow_succ]
      have hpos : 0 < 2 ^ k + k := by positivity
      omega

/-- The chain fits on an `n`-cycle with at least two unused cycle edges. -/
def shortcutFits (n k : ℕ) : Prop := 2 ^ k + k + 1 ≤ n

/-- Maximality of the chosen segment count gives the sharp upper rounding
bound used to compare the long and intermediate intervals. -/
theorem shortcut_maximal_rounding {n k : ℕ}
    (hmax : ¬ shortcutFits n (k + 1)) : n ≤ 2 ^ (k + 1) + k + 1 := by
  simp only [shortcutFits, Nat.not_le] at hmax
  omega

/-- For every `n≥7`, a maximal feasible segment count exists, starting at
`k=2` and failing feasibility exactly at the next integer. -/
theorem exists_maximal_shortcut_k {n : ℕ} (hn : 7 ≤ n) :
    ∃ k, 2 ≤ k ∧ shortcutFits n k ∧ ¬ shortcutFits n (k + 1) := by
  classical
  have hex : ∃ m, 3 ≤ m ∧ ¬ shortcutFits n m := by
    refine ⟨n + 1, by omega, ?_⟩
    dsimp [shortcutFits]
    have hp : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self (n := n + 1)
    omega
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  have hm3 : 3 ≤ m := by simpa [m] using hm.1
  have hprev : shortcutFits n (m - 1) := by
    by_cases hm_eq : m = 3
    · rw [hm_eq]
      dsimp [shortcutFits]
      omega
    · by_cases hfit : shortcutFits n (m - 1)
      · exact hfit
      · have hprev3 : 3 ≤ m - 1 := by omega
        have hfailPrev : 3 ≤ m - 1 ∧ ¬ shortcutFits n (m - 1) := ⟨hprev3, hfit⟩
        have hmin : Nat.find hex ≤ m - 1 := Nat.find_min' hex hfailPrev
        simp only [m] at hmin
        omega
  refine ⟨m - 1, ?_, hprev, ?_⟩
  · omega
  · simpa [m, Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using hm.2





/-- A level of the paper's shortcut tower (starting at `T₀=2`). -/
def shortcutTower (d : ℕ) : ℕ := expTower (d + 1)

theorem exists_shortcutTower_ge (k : ℕ) : ∃ d, k ≤ shortcutTower d := by
  refine ⟨logStar k, ?_⟩
  have h := le_expTower_logStar k
  exact h.trans (expTower_strictMono.monotone (by omega))

/-- Minimum number of reductions `t ↦ ceil(log₂ t)` needed to reach at most
one. Its tower characterization is simpler to use in Lean than logarithms. -/
noncomputable def shortcutIterationCount (k : ℕ) : ℕ :=
  Nat.find (exists_shortcutTower_ge k)

@[simp] theorem le_shortcutTower_iterationCount (k : ℕ) :
    k ≤ shortcutTower (shortcutIterationCount k) :=
  Nat.find_spec (exists_shortcutTower_ge k)

theorem shortcutIterationCount_min_le {k d : ℕ}
    (h : k ≤ shortcutTower d) : shortcutIterationCount k ≤ d :=
  Nat.find_min' (exists_shortcutTower_ge k) h

/-- For `k≥2`, the reduction count is exactly `logStar k - 1`, as in §18. -/
theorem shortcutIterationCount_eq_logStar_sub_one {k : ℕ} (hk : 2 ≤ k) :
    shortcutIterationCount k + 1 = logStar k := by
  have hs : 1 ≤ logStar k := by
    by_contra hpos
    have hz : logStar k = 0 := Nat.eq_zero_of_not_pos hpos
    have hspec := le_expTower_logStar k
    rw [hz] at hspec
    simp [expTower] at hspec
    omega
  have hsub : (logStar k - 1) + 1 = logStar k := Nat.sub_add_cancel hs
  have hupper : shortcutIterationCount k ≤ logStar k - 1 := by
    apply shortcutIterationCount_min_le
    rw [shortcutTower, hsub]
    exact le_expTower_logStar k
  have hlower : logStar k ≤ shortcutIterationCount k + 1 := by
    apply logStar_min_le
    simpa [shortcutTower] using le_shortcutTower_iterationCount k
  omega

/-- A feasible `k` is at most the integer floor of `log₂ n`. -/
theorem shortcut_k_le_log2 {n k : ℕ} (hn : 0 < n)
    (hfit : shortcutFits n k) : k ≤ n.log2 := by
  by_contra h
  have hk : n.log2 + 1 ≤ k := by omega
  have hpow : n < 2 ^ (n.log2 + 1) := (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  have hmono : 2 ^ (n.log2 + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hnk : 2 ^ k ≤ n := by dsimp [shortcutFits] at hfit; omega
  omega

/-- The resulting added-edge budget `k+2+d(k)` is bounded by the desired
`log₂ n + logStar n + 1` (with integer `log₂`). -/
theorem shortcut_added_edges_bound {n k : ℕ} (hn : 0 < n)
    (hk : 2 ≤ k) (hfit : shortcutFits n k) :
    k + 2 + shortcutIterationCount k ≤ n.log2 + logStar n + 1 := by
  have hcount := shortcutIterationCount_eq_logStar_sub_one hk
  have hlog : k ≤ n.log2 := shortcut_k_le_log2 hn hfit
  have hstar : logStar k ≤ logStar n := logStar_mono (hlog.trans (Nat.log2_le_self n))
  omega

end Erdos1016.Extremal

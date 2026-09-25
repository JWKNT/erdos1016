import Erdos1016.Extremal.Construction.ShortcutBounds

set_option autoImplicit false

/-!
# Recursive closure levels for the §18 short-cycle construction

The closure chord at level `m` supplies cycles in `[m+1, 2^m+m]`. Repeated
ceiling binary logarithms produce a list of additional levels whose intervals
cover everything below the main level `k`. -/

namespace Erdos1016.Extremal

theorem clog_two_lt_self {k : ℕ} (hk : 2 < k) : Nat.clog 2 k < k := by
  have hpow : k ≤ 2 ^ (k - 1) := by
    have h := succ_le_two_pow (k - 1)
    omega
  have hclog : Nat.clog 2 k ≤ k - 1 :=
    (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp hpow
  omega

/-- Levels reached by repeatedly applying the ceiling base-two logarithm,
stopping at two. -/
def recursiveClosureLevels : ℕ → List ℕ
  | k => if k ≤ 2 then [] else
      recursiveClosureLevels (Nat.clog 2 k) ++ [Nat.clog 2 k]
termination_by k => k
decreasing_by
  exact clog_two_lt_self (by omega)

theorem two_le_clog_two {k : ℕ} (hk : 2 < k) : 2 ≤ Nat.clog 2 k := by
  have hp : 2 ^ 1 < k := by norm_num; omega
  have h := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hp
  omega

theorem clog_two_covers {k : ℕ} : k ≤ 2 ^ Nat.clog 2 k :=
  Nat.le_pow_clog (by decide : 1 < 2) k

/-- The exact log-star recurrence for the ceiling logarithm used by the
recursive chord construction. -/
theorem logStar_clog_two_succ {k : ℕ} (hk : 2 < k) :
    logStar (Nat.clog 2 k) + 1 = logStar k := by
  let d := logStar k
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    have hs : k ≤ expTower d := by simpa [d] using le_expTower_logStar k
    rw [hd0] at hs
    simp [expTower] at hs
    omega
  have hsub : (d - 1) + 1 = d := Nat.sub_add_cancel (by omega)
  have hclogBound : Nat.clog 2 k ≤ expTower (d - 1) := by
    apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hs : k ≤ expTower d := by simpa [d] using le_expTower_logStar k
    rw [← hsub, expTower] at hs
    exact hs
  have hupper : logStar (Nat.clog 2 k) ≤ d - 1 := by
    calc
      logStar (Nat.clog 2 k) ≤ logStar (expTower (d - 1)) := logStar_mono hclogBound
      _ = d - 1 := logStar_expTower _
  have hlower : d ≤ logStar (Nat.clog 2 k) + 1 := by
    apply logStar_min_le
    calc
      k ≤ 2 ^ Nat.clog 2 k := clog_two_covers
      _ ≤ 2 ^ expTower (logStar (Nat.clog 2 k)) := Nat.pow_le_pow_right
        (by norm_num : 0 < 2) (le_expTower_logStar _)
      _ = expTower (logStar (Nat.clog 2 k) + 1) := by simp [expTower]
  omega

/-- The number of recursively added closure chords is exactly the paper's
`shortcutIterationCount`. -/
theorem recursiveClosureLevels_length (k : ℕ) :
    (recursiveClosureLevels k).length = shortcutIterationCount k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk : k ≤ 2
      · have hcount : shortcutIterationCount k = 0 := by
          have hle : shortcutIterationCount k ≤ 0 := by
            apply shortcutIterationCount_min_le
            simp [shortcutTower, expTower]
            omega
          omega
        rw [recursiveClosureLevels.eq_1, if_pos hk]
        simp [hcount]
      · have hk' : 2 < k := by omega
        let m := Nat.clog 2 k
        have hm : m < k := by dsimp [m]; exact clog_two_lt_self hk'
        have hm2 : 2 ≤ m := by dsimp [m]; exact two_le_clog_two hk'
        have him := ih m hm
        rw [recursiveClosureLevels.eq_1, if_neg (by omega)]
        simp only [List.length_append, List.length_singleton]
        rw [him]
        have hcountk := shortcutIterationCount_eq_logStar_sub_one (by omega : 2 ≤ k)
        have hcountm := shortcutIterationCount_eq_logStar_sub_one hm2
        have hlog := logStar_clog_two_succ hk'
        dsimp [m] at *
        omega

/-- Every recursive closure index stays between two and the original level. -/
theorem recursiveClosureLevels_mem_bounds {k m : ℕ}
    (hk : 2 ≤ k) (hm : m ∈ recursiveClosureLevels k) : 2 ≤ m ∧ m < k := by
  induction k using Nat.strong_induction_on generalizing m with
  | h k ih =>
      by_cases hsmall : k ≤ 2
      · rw [recursiveClosureLevels.eq_1, if_pos hsmall] at hm
        simp at hm
      · have hbig : 2 < k := by omega
        rw [recursiveClosureLevels.eq_1, if_neg hsmall, List.mem_append,
          List.mem_singleton] at hm
        rcases hm with hm | hm
        · have hclogBound : Nat.clog 2 k < k := clog_two_lt_self hbig
          have hclogLower : 2 ≤ Nat.clog 2 k := two_le_clog_two hbig
          have hrec := ih (Nat.clog 2 k) hclogBound hclogLower hm
          omega
        · subst m
          exact ⟨two_le_clog_two hbig, clog_two_lt_self hbig⟩

/-- The main level and its recursive closure levels cover every cycle length
from three through the top of the main binary-shortcut interval. -/
theorem recursiveClosureIntervals_cover (k ℓ : ℕ) (hk : 2 ≤ k)
    (hlo : 3 ≤ ℓ) (hhi : ℓ ≤ 2 ^ k + k) :
    ∃ m ∈ k :: recursiveClosureLevels k,
      m + 1 ≤ ℓ ∧ ℓ ≤ 2 ^ m + m := by
  induction k using Nat.strong_induction_on generalizing ℓ with
  | h k ih =>
      by_cases hmain : k + 1 ≤ ℓ
      · exact ⟨k, by simp, hmain, hhi⟩
      · have hbig : 2 < k := by omega
        let m := Nat.clog 2 k
        have hmLt : m < k := by dsimp [m]; exact clog_two_lt_self hbig
        have hmTwo : 2 ≤ m := by dsimp [m]; exact two_le_clog_two hbig
        have hkPower : k ≤ 2 ^ m := by dsimp [m]; exact clog_two_covers
        have hhi' : ℓ ≤ 2 ^ m + m := by omega
        obtain ⟨r, hrmem, hrlo, hrhi⟩ := ih m hmLt ℓ hmTwo hlo hhi'
        refine ⟨r, ?_, hrlo, hrhi⟩
        rw [recursiveClosureLevels.eq_1, if_neg (by omega)]
        rcases List.mem_cons.mp hrmem with hr | hr
        · subst r
          apply List.mem_cons.mpr
          right
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        · apply List.mem_cons.mpr
          right
          exact List.mem_append.mpr (Or.inl hr)

end Erdos1016.Extremal

import Erdos1016.Cleanup.Protection.ParallelPairProtection

set_option autoImplicit false

namespace Erdos1016.Proof.DeletionBudgetBounds

open Erdos1016
open CleanupSpecification

private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => norm_num
          | succ n =>
              have hprev := ih (n + 1) (by omega)
              rw [pow_succ]
              have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
              nlinarith

private theorem r_add_four_le_two_pow {R : ℕ} (hR : 5 ≤ R) :
    R + 4 ≤ 2 ^ R := by
  have hbase : 5 + 4 ≤ 2 ^ 5 := by norm_num
  induction R, hR using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      omega

/-- With the fixed constants of the paper, the attachment count is at most
`2^(5R)` once `R` is at least `4` and at least the explicit coefficient
`2 B₃ + 6 m₂`.  This is the paper's “sufficiently large R” estimate in a
fully explicit form. -/
theorem corrected_attachment_bound
    (B₃ m₂ R m M₂ : ℕ)
    (hR5 : 5 ≤ R)
    (hRconst : 2 * B₃ + 6 * m₂ ≤ R)
    (hm : m < 2 ^ (4 * R))
    (hM₂ : M₂ ≤ m₂ * R ^ 2) :
    (R + 1) * (m + B₃ * R) + 2 * m + 6 * M₂ ≤ 2 ^ (5 * R) := by
  have hRpow : R ≤ 2 ^ R := self_le_two_pow R
  have hRadd : R + 3 ≤ 2 ^ R - 1 := by
    have := r_add_four_le_two_pow hR5
    omega
  have hRpos : 1 ≤ R := by omega
  have hR2 : R ^ 2 ≤ 2 ^ (2 * R) := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ 2 ^ R * 2 ^ R := Nat.mul_le_mul hRpow hRpow
      _ = 2 ^ (2 * R) := by rw [← pow_add]; congr 1 <;> omega
  have hpolyCoeff : 2 * B₃ + 6 * m₂ ≤ 2 ^ (2 * R) := by
    calc
      2 * B₃ + 6 * m₂ ≤ R := hRconst
      _ ≤ 2 ^ R := hRpow
      _ ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpoly : B₃ * R * (R + 1) + 6 * (m₂ * R ^ 2) ≤ 2 ^ (4 * R) := by
    have hcoef : B₃ * R * (R + 1) + 6 * (m₂ * R ^ 2) ≤
        (2 * B₃ + 6 * m₂) * R ^ 2 := by
      have hRa : R + 1 ≤ 2 * R := by omega
      have hmult := Nat.mul_le_mul_left (B₃ * R) hRa
      nlinarith [hmult]
    calc
      _ ≤ (2 * B₃ + 6 * m₂) * R ^ 2 := hcoef
      _ ≤ 2 ^ (2 * R) * 2 ^ (2 * R) := Nat.mul_le_mul hpolyCoeff hR2
      _ = 2 ^ (4 * R) := by rw [← pow_add]; congr 1 <;> omega
  have hm' : m ≤ 2 ^ (4 * R) - 1 := by omega
  have hfirst : (R + 3) * m ≤ (2 ^ R - 1) * 2 ^ (4 * R) := by
    have hmle : m ≤ 2 ^ (4 * R) := by omega
    exact Nat.mul_le_mul hRadd hmle
  have hrest : (R + 1) * (B₃ * R) + 6 * M₂ ≤ 2 ^ (4 * R) := by
    calc
      (R + 1) * (B₃ * R) + 6 * M₂
          ≤ B₃ * R * (R + 1) + 6 * (m₂ * R ^ 2) := by
            have hmul : 6 * M₂ ≤ 6 * (m₂ * R ^ 2) := Nat.mul_le_mul_left _ hM₂
            have hfirst : (R + 1) * (B₃ * R) = B₃ * R * (R + 1) := by ring
            rw [hfirst]
            exact Nat.add_le_add_left hmul _
      _ ≤ 2 ^ (4 * R) := hpoly
  calc
    (R + 1) * (m + B₃ * R) + 2 * m + 6 * M₂
        = (R + 3) * m + ((R + 1) * (B₃ * R) + 6 * M₂) := by ring
    _ ≤ (2 ^ R - 1) * 2 ^ (4 * R) + 2 ^ (4 * R) := Nat.add_le_add hfirst hrest
    _ = 2 ^ (5 * R) := by
      have hexp : 2 ^ R * 2 ^ (4 * R) = 2 ^ (5 * R) := by
        rw [← pow_add]
        congr 1 <;> omega
      calc
        (2 ^ R - 1) * 2 ^ (4 * R) + 2 ^ (4 * R) =
            ((2 ^ R - 1) + 1) * 2 ^ (4 * R) := by rw [Nat.add_mul]; simp
        _ = 2 ^ R * 2 ^ (4 * R) := by
          rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))]
        _ = 2 ^ (5 * R) := hexp

/-- The concrete corrected deletion budget for the constructed protection. -/
def deletionBudget (R m : ℕ) :=
  (R + 1) * (m + 520 * R) + 2 * m + 6 * 481 * R ^ 2

theorem deletionBudget_le (R m : ℕ) (hR : 3926 ≤ R) (hm : m < 2 ^ (4 * R)) :
    deletionBudget R m ≤ 2 ^ (5 * R) := by
  have h := corrected_attachment_bound 520 481 R m (481 * R ^ 2)
    (by omega) (by omega) hm (by rfl)
  dsimp [deletionBudget]
  nlinarith [h]

/-- The original rank scale absorbs the actual deletion budget, even after
retaining the witness incidences missed by a pointwise degree estimate. -/
theorem scaled_deletionBudget_le (R m : ℕ) (hR : 3926 ≤ R)
    (hm : m < 2 ^ (4 * R)) :
    10 * R * deletionBudget R m ≤ 2 ^ (8 * R) := by
  have hRpow : R ≤ 2 ^ R := self_le_two_pow R
  have hten : 10 ≤ 2 ^ (2 * R) := by
    have hbase : 10 ≤ 2 ^ 4 := by norm_num
    exact hbase.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hscale : 10 * R ≤ 2 ^ (3 * R) := by
    calc
      10 * R ≤ 2 ^ (2 * R) * 2 ^ R := Nat.mul_le_mul hten hRpow
      _ = 2 ^ (3 * R) := by rw [← pow_add]; congr 1 <;> omega
  calc
    10 * R * deletionBudget R m ≤ 2 ^ (3 * R) * 2 ^ (5 * R) :=
      Nat.mul_le_mul hscale (deletionBudget_le R m hR hm)
    _ = 2 ^ (8 * R) := by rw [← pow_add]; congr 1 <;> omega

end Erdos1016.Proof.DeletionBudgetBounds

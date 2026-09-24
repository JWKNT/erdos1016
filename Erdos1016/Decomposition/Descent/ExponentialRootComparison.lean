import Erdos1016.Decomposition.Descent.AdditiveRootEstimate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.ExponentialRootComparison

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
              have hpos : 0 < 2 ^ (n + 1) := by positivity
              nlinarith

private theorem exponent_margin (R C A0 K : ℕ) (hR : 12 ≤ R)
    (hmarg : 7 * C ≥ 7 * A0 * K ^ 2 + 9) :
    (7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + R ^ 4 + 1 <
      (7 / 8 : ℝ) * ((C * R ^ 4 - 8 * R : ℕ) : ℝ) := by
  have hmargR : (7 * A0 * K ^ 2 + 9 : ℝ) ≤ 7 * C := by exact_mod_cast hmarg
  have hBigNat : 56 * R + 8 < R ^ 4 := by
    have hcube : 12 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hmul := Nat.mul_le_mul_left R hcube
    nlinarith [hmul, hR]
  have hBig : 56 * (R : ℝ) + 8 < (R : ℝ) ^ 4 := by exact_mod_cast hBigNat
  have hmul := mul_le_mul_of_nonneg_right hmargR (show 0 ≤ (R : ℝ) ^ 4 by positivity)
  have hC : 1 ≤ C := by omega
  have hnat : 8 * R ≤ C * R ^ 4 := by nlinarith [hBigNat, hC]
  push_cast [Nat.cast_sub hnat]
  nlinarith [hmul, hBig]

/-- Extremal §10 scale comparison, stated independently of the graph cleanup
construction. Here `hrootBound` is the §9 additive root estimate after
substituting `B₀ = 1/16` and the paper's exponent `p=7/8`. -/
theorem contradict_additive_root_bound
    (R C A0 Cext mD r n b c M : ℕ) (T0 : ℕ → ℕ)
    (hR : 12 ≤ R)
    (hpoly : Cext + 2 * mD ≤ R)
    (hmargin : 7 * C > 7 * A0 * (Cext + mD) ^ 2 + 8)
    (hr : 2 ^ (C * R ^ 4) ≤ r)
    (hn : r ≤ n * 2 ^ (8 * R))
    (hb : b ≤ 2 ^ (5 * R))
    (hc : c ≤ Cext * R ^ 2)
    (hM : M ≤ mD * R ^ 2)
    (hT0 : ∀ k, T0 k ≤ 2 ^ (A0 * k ^ 2))
    (hrootBound : (n : ℝ) ^ (7 / 8 : ℝ) ≤
      16 * b + (c + 2 * M : ℕ) * (T0 (c + M) : ℝ) ^ (7 / 8 : ℝ)) :
    False := by
  let K : ℕ := Cext + mD
  let D : ℕ := Cext + 2 * mD
  let k : ℕ := c + M
  have hK : c + M ≤ K * R ^ 2 := by
    dsimp [K]
    nlinarith [hc, hM]
  have hcoef : c + 2 * M ≤ D * R ^ 2 := by
    dsimp [D]
    nlinarith [hc, hM]
  have hcoefR : c + 2 * M ≤ R ^ 3 := by
    calc
      c + 2 * M ≤ D * R ^ 2 := hcoef
      _ ≤ R * R ^ 2 := Nat.mul_le_mul_right (R ^ 2) hpoly
      _ = R ^ 3 := by ring
  have hKsq : k ^ 2 ≤ K ^ 2 * R ^ 4 := by
    have hsq := Nat.pow_le_pow_left hK 2
    dsimp [k] at hsq ⊢
    nlinarith [hsq]
  have hTnat : T0 k ≤ 2 ^ (A0 * K ^ 2 * R ^ 4) := by
    calc
      T0 k ≤ 2 ^ (A0 * k ^ 2) := hT0 k
      _ ≤ 2 ^ (A0 * K ^ 2 * R ^ 4) := by
        apply Nat.pow_le_pow_right (by omega)
        nlinarith [hKsq]
  have hRpow : R ≤ 2 ^ R := self_le_two_pow R
  have hR3 : R ^ 3 ≤ 2 ^ (3 * R) := by
    calc
      R ^ 3 = R * R * R := by ring
      _ ≤ 2 ^ R * 2 ^ R * 2 ^ R := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hRpow hRpow) hRpow
      _ = 2 ^ (3 * R) := by rw [← pow_add, ← pow_add]; congr 1 <;> omega
  have h3R : 3 * R ≤ R ^ 4 := by nlinarith [hR]
  have h5R4 : 5 * R + 4 ≤ R ^ 4 := by nlinarith [hR]
  have hRpow3 : (R : ℝ) ^ 3 ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) := by
    have hcast : (R : ℝ) ^ 3 ≤ (2 : ℝ) ^ (3 * R : ℕ) := by exact_mod_cast hR3
    have hmon : (2 : ℝ) ^ (3 * R : ℕ) ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega) h3R)
    exact hcast.trans hmon
  have hbR : 16 * (b : ℝ) ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) := by
    have hb' : (b : ℝ) ≤ (2 : ℝ) ^ (5 * R : ℕ) := by exact_mod_cast hb
    have hpow : (2 : ℝ) ^ (5 * R + 4 : ℕ) ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega) h5R4)
    have hmul : 16 * (2 : ℝ) ^ (5 * R : ℕ) = (2 : ℝ) ^ (5 * R + 4 : ℕ) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1 <;> omega
    calc
      16 * (b : ℝ) ≤ 16 * (2 : ℝ) ^ (5 * R : ℕ) := by nlinarith
      _ = (2 : ℝ) ^ (5 * R + 4 : ℕ) := hmul
      _ ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) := hpow
  have hqcast :
      (T0 k : ℝ) ≤ (2 : ℝ) ^ (A0 * K ^ 2 * R ^ 4 : ℕ) := by exact_mod_cast hTnat
  have hTpow : (T0 k : ℝ) ^ (7 / 8 : ℝ) ≤
      (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ)) := by
    have h : Real.rpow (T0 k : ℝ) (7 / 8 : ℝ) ≤
        Real.rpow ((2 : ℝ) ^ (A0 * K ^ 2 * R ^ 4 : ℕ)) (7 / 8 : ℝ) := by
      exact Real.rpow_le_rpow (x := (T0 k : ℝ))
        (y := (2 : ℝ) ^ (A0 * K ^ 2 * R ^ 4 : ℕ)) (z := (7 / 8 : ℝ))
        (by positivity) hqcast (by norm_num)
    have hmul : (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ)) =
        ((2 : ℝ) ^ (A0 * K ^ 2 * R ^ 4 : ℕ)) ^ (7 / 8 : ℝ) := by
      rw [mul_comm]
      rw [← Real.rpow_natCast (2 : ℝ) (A0 * K ^ 2 * R ^ 4)]
      rw [← Real.rpow_mul (x := (2 : ℝ)) (y := ((A0 * K ^ 2 * R ^ 4 : ℕ) : ℝ))
        (z := (7 / 8 : ℝ)) (by norm_num)]
    rw [hmul]
    exact h
  have hpolycast : ((c + 2 * M : ℕ) : ℝ) ≤ (R : ℝ) ^ 3 := by exact_mod_cast hcoefR
  have hsecond :
      (c + 2 * M : ℕ) * (T0 k : ℝ) ^ (7 / 8 : ℝ) ≤
        (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + R ^ 4) := by
    calc
      (c + 2 * M : ℕ) * (T0 k : ℝ) ^ (7 / 8 : ℝ)
          ≤ (R : ℝ) ^ 3 * (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ)) := by
            exact mul_le_mul hpolycast hTpow (by positivity) (by positivity)
      _ ≤ (2 : ℝ) ^ (R ^ 4 : ℕ) *
            (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ)) :=
              mul_le_mul_of_nonneg_right hRpow3 (by positivity)
      _ = (2 : ℝ) ^ ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + R ^ 4) := by
            rw [Real.rpow_add (by norm_num)]
            rw [← Real.rpow_natCast (2 : ℝ) (R ^ 4)]
            rw [mul_comm]
            congr 1
            norm_cast
  let E : ℝ := (7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + R ^ 4
  have hfirst : 16 * (b : ℝ) ≤ (2 : ℝ) ^ E := by
    dsimp [E]
    have hbase : ((R ^ 4 : ℕ) : ℝ) ≤
        (7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + ((R ^ 4 : ℕ) : ℝ) := by
      nlinarith [show 0 ≤ (7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) by positivity]
    have hbR' : 16 * (b : ℝ) ≤ Real.rpow (2 : ℝ) ((R ^ 4 : ℕ) : ℝ) := by
      have heq : Real.rpow (2 : ℝ) ((R ^ 4 : ℕ) : ℝ) =
          (2 : ℝ) ^ (R ^ 4 : ℕ) := Real.rpow_natCast _ _
      rw [heq]
      exact hbR
    have hmono : Real.rpow (2 : ℝ) ((R ^ 4 : ℕ) : ℝ) ≤
        Real.rpow (2 : ℝ) ((7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + ((R ^ 4 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (y := ((R ^ 4 : ℕ) : ℝ))
        (z := (7 / 8 : ℝ) * (A0 * K ^ 2 * R ^ 4 : ℕ) + ((R ^ 4 : ℕ) : ℝ))
        (by norm_num : (1 : ℝ) ≤ 2) hbase
    have hcast : ((R ^ 4 : ℕ) : ℝ) = (R : ℝ) ^ 4 := by norm_cast
    simpa [hcast] using hbR'.trans hmono
  have hupper :
      16 * (b : ℝ) + (c + 2 * M : ℕ) * (T0 k : ℝ) ^ (7 / 8 : ℝ) ≤
        (2 : ℝ) ^ (E + 1) := by
    calc
      _ ≤ (2 : ℝ) ^ E + (2 : ℝ) ^ E := add_le_add hfirst (by simpa [E] using hsecond)
      _ = 2 * (2 : ℝ) ^ E := by ring
      _ = Real.rpow (2 : ℝ) 1 * Real.rpow (2 : ℝ) E := by norm_num
      _ = Real.rpow (2 : ℝ) (1 + E) := by
        exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 E).symm
      _ = Real.rpow (2 : ℝ) (E + 1) := by
        congr 1
        ring
  have hnatExponent : 8 * R ≤ C * R ^ 4 := by
    have hC : 2 ≤ C := by omega
    nlinarith [hR]
  have hscalePow : 2 ^ (C * R ^ 4 - 8 * R) ≤ n := by
    have hm : 2 ^ (C * R ^ 4 - 8 * R) * 2 ^ (8 * R) ≤ n * 2 ^ (8 * R) := by
      calc
      2 ^ (C * R ^ 4 - 8 * R) * 2 ^ (8 * R)
          = 2 ^ (C * R ^ 4) := by rw [← pow_add, Nat.sub_add_cancel hnatExponent]
      _ ≤ n * 2 ^ (8 * R) := hr.trans hn
    exact Nat.le_of_mul_le_mul_right hm (Nat.pow_pos (by norm_num))
  have hrootLower :
      (2 : ℝ) ^ ((7 / 8 : ℝ) * ((C * R ^ 4 - 8 * R : ℕ) : ℝ)) ≤
        (n : ℝ) ^ (7 / 8 : ℝ) := by
    have hbase : (2 : ℝ) ^ (C * R ^ 4 - 8 * R : ℕ) ≤ (n : ℝ) := by exact_mod_cast hscalePow
    have h : Real.rpow (Real.rpow (2 : ℝ) ((C * R ^ 4 - 8 * R : ℕ) : ℝ)) (7 / 8 : ℝ) ≤
        Real.rpow (n : ℝ) (7 / 8 : ℝ) := by
      apply Real.rpow_le_rpow (x := Real.rpow (2 : ℝ) ((C * R ^ 4 - 8 * R : ℕ) : ℝ))
        (y := (n : ℝ)) (z := (7 / 8 : ℝ))
      · exact le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      · simpa [Real.rpow_natCast] using hbase
      · norm_num
    have hmul : (2 : ℝ) ^ ((7 / 8 : ℝ) * ((C * R ^ 4 - 8 * R : ℕ) : ℝ)) =
        Real.rpow (Real.rpow (2 : ℝ) ((C * R ^ 4 - 8 * R : ℕ) : ℝ)) (7 / 8 : ℝ) := by
      rw [mul_comm]
      exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
        ((C * R ^ 4 - 8 * R : ℕ) : ℝ) (7 / 8 : ℝ)
    rw [hmul]
    exact h
  have hExponent :
      E + 1 < (7 / 8 : ℝ) * ((C * R ^ 4 - 8 * R : ℕ) : ℝ) := by
    dsimp [E, K]
    apply exponent_margin R C A0 (Cext + mD) hR
    omega
  have hstrict : (2 : ℝ) ^ (E + 1) <
      (2 : ℝ) ^ ((7 / 8 : ℝ) * ((C * R ^ 4 - 8 * R : ℕ) : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hExponent
  have : (n : ℝ) ^ (7 / 8 : ℝ) ≤ (2 : ℝ) ^ (E + 1) :=
    hrootBound.trans (by simpa [E, k] using hupper)
  exact (not_lt_of_ge (hrootLower.trans this)) hstrict

end Erdos1016.Proof.ExponentialRootComparison

import Erdos1016.ExactMaximum.SmallCutCase
import Erdos1016.ExactMaximum.CutCaps

set_option autoImplicit false

/-!
# Proposition 6.3 with caps

`SmallCutCase.lean` proves Proposition 6.3 of the paper "The maximum number of cycles in a graph
of large rank" from two statements about poles: Theorem 5.4 for `ε = 1/1000`, and the bound
`c(T) ≤ (9/16) 2^b` for a pole `T` of large rank `b`. The second statement treats the case in
which the larger side of the cut has no pair of ports with many paths.

This file proves the proposition without the bound `(9/16) 2^b`. In its place it uses the caps of
`CutCaps.lean`: for the larger side `T` of the cut, the cycles of `T` and its paths between the
ends of the cut edges are together at most a little more than `2^(d-2) 2^b`, where `d` is the
size of the cut. This is the proof of the text.

* `two_cut_cap_arith`, `three_cut_cap_arith`: the arithmetic;
* `numCycles_le_of_two_cut_cap`, `numCycles_le_of_three_cut_cap`: the cases `d = 2` and `d = 3`;
* `numCycles_le_of_small_cut_cap`: Proposition 6.3 for networks;
* `threeCutStatement_of_caps`: `FewCyclesStatement` and `CapStatement` imply
  `ThreeCutStatement`.

The proofs of the cases follow `TwoCut.lean` and `ThreeCut.lean` line by line; only the
hypothesis on the cycles of the larger side is different.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance smallCutCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Arithmetic for a cut of size two -/

/-- The count for a cut of size two, when the first side has the smaller rank. The cap of the
second side replaces the bound `(9/16) 2^b`. -/
theorem two_cut_cap_arith_aux {K B c₁ c₂ P₁ P₂ b₁ b₂ : ℕ} (hK : 1 ≤ K) (hb₁ : 1 ≤ b₁)
    (hle : b₁ ≤ b₂) (hc₁ : c₁ < 2 ^ b₁) (hP₁ : P₁ ≤ 2 ^ b₁) (hP₂ : P₂ ≤ 2 ^ b₂)
    (hF₁ : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂ : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hCap₂ : B ≤ b₂ → 4096 * (c₂ + P₂) ≤ 4097 * 2 ^ b₂)
    (hlarge : 2 * max B (16 * K) + 8 ≤ b₁ + b₂) :
    c₁ + c₂ + P₁ * P₂ ≤ 2 ^ (b₁ + b₂) + 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) := by
  have hmax : max B (16 * K) + 4 ≤ b₂ := by omega
  have hB : B ≤ b₂ := by
    have := le_max_left B (16 * K)
    omega
  have h16K : 16 * K ≤ b₂ := by
    have := le_max_right B (16 * K)
    omega
  have hA2 : 2 ≤ 2 ^ b₁ := Nat.le_self_pow (by omega) 2
  have h16D : 16 ≤ 2 ^ b₂ := by
    have h : 2 ^ 4 ≤ 2 ^ b₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h
    exact h
  have h16KD : 16 * K ≤ 2 ^ b₂ := le_trans h16K (le_of_lt Nat.lt_two_pow_self)
  have hAD : 2 ^ (b₁ + b₂) = 2 ^ b₁ * 2 ^ b₂ := pow_add 2 b₁ b₂
  have m1 : K * 2 ^ ((b₁ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 2) / 2) :=
    Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
  have m2 : K * 2 ^ ((b₂ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 2) / 2) :=
    Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e2 : 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) = 2 * (K * 2 ^ ((b₁ + b₂ + 2) / 2)) := by ring
  have k1' : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ≤ K * 2 ^ ((b₁ + 1) / 2) :=
    fun h => le_of_sq_le (hF₁ h)
  have k2' : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ≤ K * 2 ^ ((b₂ + 1) / 2) :=
    fun h => le_of_sq_le (hF₂ h)
  have hcap := hCap₂ hB
  rw [hAD, e2]
  -- abbreviations for the powers
  generalize 2 ^ b₁ = A at *
  generalize 2 ^ b₂ = D at *
  generalize K * 2 ^ ((b₁ + b₂ + 2) / 2) = M at *
  have t3 : 16 * A ≤ A * D := by
    calc 16 * A = A * 16 := by ring
      _ ≤ A * D := Nat.mul_le_mul_left A h16D
  have t4 : 2 * D ≤ A * D := Nat.mul_le_mul_right D hA2
  by_cases hcase₂ : 501 * D ≤ 1000 * P₂
  · have hc₂ := hF₂ hcase₂
    by_cases hcase₁ : 501 * A ≤ 1000 * P₁
    · -- both sides have many paths
      have k1 := k1' hcase₁
      have k2 := k2' hcase₂
      have m3 : P₁ * P₂ ≤ A * D := Nat.mul_le_mul hP₁ hP₂
      omega
    · -- the second side has many paths, the first side does not
      have k2 : 4 * c₂ ≤ D := four_mul_le hc₂ h16KD
      have t1 : P₁ * P₂ ≤ P₁ * D := Nat.mul_le_mul_left P₁ hP₂
      have t2 : 1000 * (P₁ * D) ≤ 501 * (A * D) := by
        calc 1000 * (P₁ * D) = (1000 * P₁) * D := by ring
          _ ≤ (501 * A) * D := Nat.mul_le_mul_right D (le_of_lt (not_le.1 hcase₁))
          _ = 501 * (A * D) := by ring
      generalize P₁ * P₂ = Z at *
      generalize P₁ * D = Y at *
      generalize A * D = X at *
      omega
  · -- the second side has few paths: its cap
    obtain ⟨Q, hQ⟩ : ∃ Q, D = P₂ + Q := Nat.exists_eq_add_of_le hP₂
    have hQ4 : 4 ≤ Q := by omega
    have w1 : 4 * A ≤ A * Q := by
      calc 4 * A = A * 4 := by ring
        _ ≤ A * Q := Nat.mul_le_mul_left A hQ4
    have w2 : 2 * Q ≤ A * Q := Nat.mul_le_mul_right Q hA2
    have t1 : P₁ * P₂ ≤ A * P₂ := Nat.mul_le_mul_right P₂ hP₁
    have e : A * D = A * P₂ + A * Q := by rw [hQ, Nat.mul_add]
    generalize P₁ * P₂ = Z at *
    generalize A * P₂ = Y at *
    generalize A * Q = W at *
    generalize A * D = X at *
    omega

/-- The count for a cut of size two, with the caps of the two sides. -/
theorem two_cut_cap_arith {K B c₁ c₂ P₁ P₂ b₁ b₂ : ℕ} (hK : 1 ≤ K) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hc₁ : c₁ < 2 ^ b₁) (hc₂ : c₂ < 2 ^ b₂) (hP₁ : P₁ ≤ 2 ^ b₁) (hP₂ : P₂ ≤ 2 ^ b₂)
    (hF₁ : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂ : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hCap₁ : B ≤ b₁ → 4096 * (c₁ + P₁) ≤ 4097 * 2 ^ b₁)
    (hCap₂ : B ≤ b₂ → 4096 * (c₂ + P₂) ≤ 4097 * 2 ^ b₂)
    (hlarge : 2 * max B (16 * K) + 8 ≤ b₁ + b₂) :
    c₁ + c₂ + P₁ * P₂ ≤ 2 ^ (b₁ + b₂) + 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) := by
  rcases le_total b₁ b₂ with h | h
  · exact two_cut_cap_arith_aux hK hb₁ h hc₁ hP₁ hP₂ hF₁ hF₂ hCap₂ hlarge
  · have h1 := two_cut_cap_arith_aux hK hb₂ h hc₂ hP₂ hP₁ hF₂ hF₁ hCap₁
      (by omega : 2 * max B (16 * K) + 8 ≤ b₂ + b₁)
    rw [add_comm b₂ b₁, Nat.mul_comm P₂ P₁] at h1
    omega

/-! ### Arithmetic for a cut of size three -/

/-- The count for a cut of size three, when the second side has two pairs of ports with many
paths: the pairs `2` and `3`. This is `three_cut_arith_ii` without the bound `(9/16) 2^b`: the
bound `c₂ < 2^(b₂)` is sufficient here. -/
theorem three_cut_cap_arith_ii {K c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁)
    (h16 : 16 ≤ 2 ^ b₂) (h2M : 2000000 * K ≤ 2 ^ b₂) (hc₁ : c₁ < 2 ^ b₁) (hc₂ : c₂ < 2 ^ b₂)
    (hX₁ : X₁ ≤ 2 ^ b₁) (hX₂ : X₂ ≤ 2 ^ b₁) (hX₃ : X₃ ≤ 2 ^ b₁)
    (hY₂ : Y₂ ≤ 2 ^ b₂) (hY₃ : Y₃ ≤ 2 ^ b₂) (hYsmall : Y₁ ^ 2 ≤ 2 * K * 2 ^ b₂)
    (hYbig : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₃))
    (hF₁₂ : 501 * 2 ^ b₁ ≤ 1000 * X₂ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₁₃ : 501 * 2 ^ b₁ ≤ 1000 * X₃ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂₂ : 501 * 2 ^ b₂ ≤ 1000 * Y₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hF₂₃ : 501 * 2 ^ b₂ ≤ 1000 * Y₃ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hT₁ : 1002 * 2 ^ b₁ ≤ 1000 * (X₂ + X₃) → X₁ ^ 2 ≤ 2 * K * 2 ^ b₁) :
    c₁ + c₂ + X₁ * Y₁ + X₂ * Y₂ + X₃ * Y₃ ≤
      2 * 2 ^ (b₁ + b₂) + 4 * K * 2 ^ ((b₁ + b₂ + 3) / 2) := by
  have hY1 : 1000 * Y₁ ≤ 2 ^ b₂ := thousand_mul_le hYsmall h2M
  have hA2 : 2 ≤ 2 ^ b₁ := Nat.le_self_pow (by omega) 2
  have hAD : 2 ^ (b₁ + b₂) = 2 ^ b₁ * 2 ^ b₂ := pow_add 2 b₁ b₂
  have e4 : 4 * K * 2 ^ ((b₁ + b₂ + 3) / 2) = 4 * (K * 2 ^ ((b₁ + b₂ + 3) / 2)) := by ring
  rw [hAD, e4]
  by_cases hXbig : 1002 * 2 ^ b₁ ≤ 1000 * (X₂ + X₃)
  · -- both sides have two pairs with many paths
    have hXs := hT₁ hXbig
    have hc₁' : c₁ ≤ K * 2 ^ ((b₁ + 1) / 2) := by
      rcases le_or_lt (501 * 2 ^ b₁) (1000 * X₂) with k | k
      · exact le_of_sq_le (hF₁₂ k)
      · exact le_of_sq_le (hF₁₃ (by omega))
    have hc₂' : c₂ ≤ K * 2 ^ ((b₂ + 1) / 2) := by
      rcases le_or_lt (501 * 2 ^ b₂) (1000 * Y₂) with k | k
      · exact le_of_sq_le (hF₂₂ k)
      · exact le_of_sq_le (hF₂₃ (by omega))
    have hprod := mul_le_of_sq_le hXs hYsmall
    have m1 : K * 2 ^ ((b₁ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 3) / 2) :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
    have m2 : K * 2 ^ ((b₂ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 3) / 2) :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
    have m3 : K * 2 ^ ((b₁ + b₂ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 3) / 2) :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
    have e2 : 2 * K * 2 ^ ((b₁ + b₂ + 1) / 2) = 2 * (K * 2 ^ ((b₁ + b₂ + 1) / 2)) := by ring
    rw [e2] at hprod
    have p2 : X₂ * Y₂ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul hX₂ hY₂
    have p3 : X₃ * Y₃ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul hX₃ hY₃
    omega
  · -- the first side does not have these two pairs with many paths
    have q1 : X₁ * Y₁ ≤ 2 ^ b₁ * Y₁ := Nat.mul_le_mul_right Y₁ hX₁
    have q1' : 1000 * (2 ^ b₁ * Y₁) ≤ 2 ^ b₁ * 2 ^ b₂ := by
      calc 1000 * (2 ^ b₁ * Y₁) = 2 ^ b₁ * (1000 * Y₁) := by ring
        _ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul_left _ hY1
    have q2 : X₂ * Y₂ ≤ X₂ * 2 ^ b₂ := Nat.mul_le_mul_left X₂ hY₂
    have q3 : X₃ * Y₃ ≤ X₃ * 2 ^ b₂ := Nat.mul_le_mul_left X₃ hY₃
    have q4 : 1000 * (X₂ * 2 ^ b₂ + X₃ * 2 ^ b₂) ≤ 1002 * (2 ^ b₁ * 2 ^ b₂) := by
      calc 1000 * (X₂ * 2 ^ b₂ + X₃ * 2 ^ b₂) = (1000 * (X₂ + X₃)) * 2 ^ b₂ := by ring
        _ ≤ (1002 * 2 ^ b₁) * 2 ^ b₂ := Nat.mul_le_mul_right _ (le_of_lt (not_le.1 hXbig))
        _ = 1002 * (2 ^ b₁ * 2 ^ b₂) := by ring
    have t3 : 16 * 2 ^ b₁ ≤ 2 ^ b₁ * 2 ^ b₂ := by
      calc 16 * 2 ^ b₁ = 2 ^ b₁ * 16 := by ring
        _ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul_left _ h16
    have t4 : 2 * 2 ^ b₂ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul_right _ hA2
    generalize X₁ * Y₁ = Z₁ at *
    generalize X₂ * Y₂ = Z₂ at *
    generalize X₃ * Y₃ = Z₃ at *
    generalize 2 ^ b₁ * Y₁ = U₁ at *
    generalize X₂ * 2 ^ b₂ = U₂ at *
    generalize X₃ * 2 ^ b₂ = U₃ at *
    generalize 2 ^ b₁ * 2 ^ b₂ = P at *
    generalize K * 2 ^ ((b₁ + b₂ + 3) / 2) = M at *
    omega

/-- The count for a cut of size three, when the first side has the smaller rank. The cap of the
second side replaces the bound `(9/16) 2^b`. -/
theorem three_cut_cap_arith_aux {K B c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁)
    (hle : b₁ ≤ b₂) (hlarge : 2 * max B (2000000 * K) + 8 ≤ b₁ + b₂) (hc₁ : c₁ < 2 ^ b₁)
    (hc₂ : c₂ < 2 ^ b₂)
    (hCap₂ : B ≤ b₂ → 2048 * (c₂ + (Y₁ + Y₂ + Y₃)) ≤ 4097 * 2 ^ b₂)
    (hX₁ : X₁ ≤ 2 ^ b₁) (hX₂ : X₂ ≤ 2 ^ b₁)
    (hX₃ : X₃ ≤ 2 ^ b₁) (hY₁ : Y₁ ≤ 2 ^ b₂) (hY₂ : Y₂ ≤ 2 ^ b₂) (hY₃ : Y₃ ≤ 2 ^ b₂)
    (hF₁₁ : 501 * 2 ^ b₁ ≤ 1000 * X₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₁₂ : 501 * 2 ^ b₁ ≤ 1000 * X₂ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₁₃ : 501 * 2 ^ b₁ ≤ 1000 * X₃ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂₁ : 501 * 2 ^ b₂ ≤ 1000 * Y₁ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hF₂₂ : 501 * 2 ^ b₂ ≤ 1000 * Y₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hF₂₃ : 501 * 2 ^ b₂ ≤ 1000 * Y₃ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hT₁₁ : 1002 * 2 ^ b₁ ≤ 1000 * (X₂ + X₃) → X₁ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₁₂ : 1002 * 2 ^ b₁ ≤ 1000 * (X₁ + X₃) → X₂ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₁₃ : 1002 * 2 ^ b₁ ≤ 1000 * (X₁ + X₂) → X₃ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₂₁ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₃) → Y₁ ^ 2 ≤ 2 * K * 2 ^ b₂)
    (hT₂₂ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₃) → Y₂ ^ 2 ≤ 2 * K * 2 ^ b₂)
    (hT₂₃ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₂) → Y₃ ^ 2 ≤ 2 * K * 2 ^ b₂) :
    c₁ + c₂ + X₁ * Y₁ + X₂ * Y₂ + X₃ * Y₃ ≤
      2 * 2 ^ (b₁ + b₂) + 4 * K * 2 ^ ((b₁ + b₂ + 3) / 2) := by
  have hB : B ≤ b₂ := by
    have := le_max_left B (2000000 * K)
    omega
  have h2K : 2000000 * K ≤ b₂ := by
    have := le_max_right B (2000000 * K)
    omega
  have h16 : 16 ≤ 2 ^ b₂ := by
    have k : 2 ^ 4 ≤ 2 ^ b₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at k
    exact k
  have h2M : 2000000 * K ≤ 2 ^ b₂ := le_trans h2K (le_of_lt Nat.lt_two_pow_self)
  have hcap := hCap₂ hB
  by_cases k1 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₃)
  · exact three_cut_cap_arith_ii hb₁ h16 h2M hc₁ hc₂ hX₁ hX₂ hX₃ hY₂ hY₃ (hT₂₁ k1) k1 hF₁₂ hF₁₃
      hF₂₂ hF₂₃ hT₁₁
  by_cases k2 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₃)
  · have k := three_cut_cap_arith_ii hb₁ h16 h2M hc₁ hc₂ hX₂ hX₁ hX₃ hY₁ hY₃ (hT₂₂ k2) k2 hF₁₁
      hF₁₃ hF₂₁ hF₂₃ hT₁₂
    omega
  by_cases k3 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₂)
  · have k := three_cut_cap_arith_ii hb₁ h16 h2M hc₁ hc₂ hX₃ hX₂ hX₁ hY₂ hY₁ (hT₂₃ k3)
      (by omega : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₁)) hF₁₂ hF₁₁ hF₂₂ hF₂₁
      (fun k' => hT₁₃ (by omega))
    omega
  -- no two pairs of the second side have many paths: the cap of the second side
  have hA2 : 2 ≤ 2 ^ b₁ := Nat.le_self_pow (by omega) 2
  have hAD : 2 ^ (b₁ + b₂) = 2 ^ b₁ * 2 ^ b₂ := pow_add 2 b₁ b₂
  rw [hAD]
  have q1 : X₁ * Y₁ ≤ 2 ^ b₁ * Y₁ := Nat.mul_le_mul_right Y₁ hX₁
  have q2 : X₂ * Y₂ ≤ 2 ^ b₁ * Y₂ := Nat.mul_le_mul_right Y₂ hX₂
  have q3 : X₃ * Y₃ ≤ 2 ^ b₁ * Y₃ := Nat.mul_le_mul_right Y₃ hX₃
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, 3006 * 2 ^ b₂ = 2000 * (Y₁ + Y₂ + Y₃) + Δ :=
    Nat.exists_eq_add_of_le (by omega)
  have e : 3006 * (2 ^ b₁ * 2 ^ b₂) =
      2000 * (2 ^ b₁ * Y₁ + 2 ^ b₁ * Y₂ + 2 ^ b₁ * Y₃) + 2 ^ b₁ * Δ := by
    calc 3006 * (2 ^ b₁ * 2 ^ b₂) = 2 ^ b₁ * (3006 * 2 ^ b₂) := by ring
      _ = 2 ^ b₁ * (2000 * (Y₁ + Y₂ + Y₃) + Δ) := by rw [hΔ]
      _ = 2000 * (2 ^ b₁ * Y₁ + 2 ^ b₁ * Y₂ + 2 ^ b₁ * Y₃) + 2 ^ b₁ * Δ := by ring
  have w : Δ ≤ 2 ^ b₁ * Δ := Nat.le_mul_of_pos_left Δ (by omega)
  have t3 : 16 * 2 ^ b₁ ≤ 2 ^ b₁ * 2 ^ b₂ := by
    calc 16 * 2 ^ b₁ = 2 ^ b₁ * 16 := by ring
      _ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul_left _ h16
  have t4 : 2 * 2 ^ b₂ ≤ 2 ^ b₁ * 2 ^ b₂ := Nat.mul_le_mul_right _ hA2
  generalize X₁ * Y₁ = Z₁ at *
  generalize X₂ * Y₂ = Z₂ at *
  generalize X₃ * Y₃ = Z₃ at *
  generalize 2 ^ b₁ * Y₁ = U₁ at *
  generalize 2 ^ b₁ * Y₂ = U₂ at *
  generalize 2 ^ b₁ * Y₃ = U₃ at *
  generalize 2 ^ b₁ * Δ = W at *
  generalize 2 ^ b₁ * 2 ^ b₂ = P at *
  omega

/-- The count for a cut of size three, with the caps of the two sides. The products are in the
order of the count `numCycles_of_three_crossing`. -/
theorem three_cut_cap_arith {K B c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁)
    (hb₂ : 1 ≤ b₂) (hlarge : 2 * max B (2000000 * K) + 8 ≤ b₁ + b₂) (hc₁ : c₁ < 2 ^ b₁)
    (hc₂ : c₂ < 2 ^ b₂)
    (hCap₁ : B ≤ b₁ → 2048 * (c₁ + (X₁ + X₂ + X₃)) ≤ 4097 * 2 ^ b₁)
    (hCap₂ : B ≤ b₂ → 2048 * (c₂ + (Y₁ + Y₂ + Y₃)) ≤ 4097 * 2 ^ b₂)
    (hX₁ : X₁ ≤ 2 ^ b₁) (hX₂ : X₂ ≤ 2 ^ b₁) (hX₃ : X₃ ≤ 2 ^ b₁) (hY₁ : Y₁ ≤ 2 ^ b₂)
    (hY₂ : Y₂ ≤ 2 ^ b₂) (hY₃ : Y₃ ≤ 2 ^ b₂)
    (hF₁₁ : 501 * 2 ^ b₁ ≤ 1000 * X₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₁₂ : 501 * 2 ^ b₁ ≤ 1000 * X₂ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₁₃ : 501 * 2 ^ b₁ ≤ 1000 * X₃ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂₁ : 501 * 2 ^ b₂ ≤ 1000 * Y₁ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hF₂₂ : 501 * 2 ^ b₂ ≤ 1000 * Y₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hF₂₃ : 501 * 2 ^ b₂ ≤ 1000 * Y₃ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hT₁₁ : 1002 * 2 ^ b₁ ≤ 1000 * (X₂ + X₃) → X₁ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₁₂ : 1002 * 2 ^ b₁ ≤ 1000 * (X₁ + X₃) → X₂ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₁₃ : 1002 * 2 ^ b₁ ≤ 1000 * (X₁ + X₂) → X₃ ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hT₂₁ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₃) → Y₁ ^ 2 ≤ 2 * K * 2 ^ b₂)
    (hT₂₂ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₃) → Y₂ ^ 2 ≤ 2 * K * 2 ^ b₂)
    (hT₂₃ : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₂) → Y₃ ^ 2 ≤ 2 * K * 2 ^ b₂) :
    c₁ + c₂ + X₃ * Y₃ + X₂ * Y₂ + X₁ * Y₁ ≤
      2 ^ (b₁ + b₂ + 1) + 4 * K * 2 ^ ((b₁ + b₂ + 3) / 2) := by
  have e : 2 ^ (b₁ + b₂ + 1) = 2 * 2 ^ (b₁ + b₂) := by rw [pow_succ, Nat.mul_comm]
  rw [e]
  rcases le_total b₁ b₂ with h | h
  · have k := three_cut_cap_arith_aux hb₁ h hlarge hc₁ hc₂ hCap₂ hX₁ hX₂ hX₃ hY₁ hY₂ hY₃ hF₁₁
      hF₁₂ hF₁₃ hF₂₁ hF₂₂ hF₂₃ hT₁₁ hT₁₂ hT₁₃ hT₂₁ hT₂₂ hT₂₃
    omega
  · have k := three_cut_cap_arith_aux hb₂ h (by omega : 2 * max B (2000000 * K) + 8 ≤ b₂ + b₁)
      hc₂ hc₁ hCap₁ hY₁ hY₂ hY₃ hX₁ hX₂ hX₃ hF₂₁ hF₂₂ hF₂₃ hF₁₁ hF₁₂ hF₁₃ hT₂₁ hT₂₂ hT₂₃ hT₁₁
      hT₁₂ hT₁₃
    rw [add_comm b₂ b₁, Nat.mul_comm Y₁ X₁, Nat.mul_comm Y₂ X₂, Nat.mul_comm Y₃ X₃] at k
    omega

/-! ### The cases of the proposition -/

/-- **Proposition 6.3 of the paper, the case of a cut of size two, with caps.** Let `N` be a
connected cubic network of rank `r`, without a cyclic cut of size one, and let `S` be a cyclic
cut of size two. If `r` is large, then `N` has at most `2^(r-1) + 2 K 2^⌈r/2⌉` cycles. -/
theorem numCycles_le_of_two_cut_cap {K B : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K)
    (hC : CapTwoWith B) {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 2 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 2) (hcyc : N.IsCyclicCut S)
    (hR : 2 * max B (16 * K) + 9 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 2 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- the two crossing edges
  have hcard : (Finset.univ.filter fun g : E => N.crosses S g).card = 2 := by
    rw [← natCard_subtype_eq_card_filter]
    exact hS
  obtain ⟨e, f, hef, hCef⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ g, N.crosses S g ↔ g = e ∨ g = f := by
    intro g
    have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S g) ↔ N.crosses S g :=
      ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
    rw [← h1, hCef, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨s₁, t₁, he, hs₁, ht₁⟩ := exists_joins_of_crosses N ((hmem e).2 (Or.inl rfl))
  obtain ⟨s₂, t₂, hf, hs₂, ht₂⟩ := exists_joins_of_crosses N ((hmem f).2 (Or.inr rfl))
  -- the complement of `S` is a cut of the same kind
  have hS' : N.cutSize (fun v => ¬ S v) = 2 := by
    rw [N.cutSize_not S]
    exact hS
  have hcyc' : 0 < (N.sub (N.inside fun v => ¬ S v)).numCycles := hcyc.2
  have hnn : ∀ v, S v → ¬ ¬ S v := fun v h h' => h' h
  -- the ends of the two edges are different
  have hs : s₁ ≠ s₂ := by
    intro h
    rw [← h] at hf
    exact N.false_of_two_crossing_at hcubic (by norm_num) hmin S hS hcyc.1 hef he hf hs₁ ht₁ ht₂
  have ht : t₁ ≠ t₂ := by
    intro h
    rw [← h] at hf
    exact N.false_of_two_crossing_at hcubic (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' hef
      he.symm hf.symm ht₁ (hnn s₁ hs₁) (hnn s₂ hs₂)
  -- both sides are connected
  have hin := N.reachable_inside_of_minimal hcubic (by norm_num) (by norm_num) hmin S hS hs₁ ht₁
  have hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t₁ u :=
    N.reachable_inside_of_minimal hcubic (by norm_num) (by norm_num) hmin (fun v => ¬ S v) hS'
      ht₁ (hnn s₁ hs₁)
  -- the rank and the count
  have hrank := N.networkRank_add_one_of_cut S hs₁ ht₁ hN hin hout
  have hS2 : Nat.card {g : E // N.crosses S g} = 2 := hS
  rw [hS2] at hrank
  have hcount := N.numCycles_of_two_crossing S (fun g hg => (hmem g).1 hg) he hs₁ ht₁ hf hs₂ ht₂
    hs ht
  -- the two sides are poles, and the ends of the edges are ports
  have hpole₁ : (N.sub (N.inside S)).IsWeakPole :=
    N.isWeakPole_inside hcubic (by norm_num) (by norm_num) hmin S hS hcyc.1 hs₁ ht₁
  have hpole₂ : (N.sub (N.outside S)).IsWeakPole :=
    N.isWeakPole_inside hcubic (by norm_num) (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' ht₁
      (hnn s₁ hs₁)
  have hport₁ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.inside S)).IsPort s := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (by norm_num) hmin S hS hcyc.1 hg hs' ht'
  have hport₂ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.outside S)).IsPort t := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' hg.symm ht'
      (hnn s hs')
  -- the hypotheses of the arithmetic
  have hb₁ := networkRank_pos_of_numCycles_pos _ hcyc.1
  have hb₂ := networkRank_pos_of_numCycles_pos _ hcyc.2
  have hc₁ := (N.sub (N.inside S)).numCycles_lt_two_pow
  have hc₂ := (N.sub (N.outside S)).numCycles_lt_two_pow
  have hP₁ := (N.sub (N.inside S)).numPaths_le_two_pow s₁ s₂
  have hP₂ := (N.sub (N.outside S)).numPaths_le_two_pow t₁ t₂
  have hF₁ := hF V {g : E // N.inside S g} (N.sub (N.inside S)) hpole₁ s₁ s₂
    (hport₁ e s₁ t₁ he hs₁ ht₁) (hport₁ f s₂ t₂ hf hs₂ ht₂) hs
  have hF₂ := hF V {g : E // N.outside S g} (N.sub (N.outside S)) hpole₂ t₁ t₂
    (hport₂ e s₁ t₁ he hs₁ ht₁) (hport₂ f s₂ t₂ hf hs₂ ht₂) ht
  -- the caps of the two sides
  have hCap₁ : B ≤ networkRank (N.sub (N.inside S)) →
      4096 * ((N.sub (N.inside S)).numCycles + (N.sub (N.inside S)).numPaths s₁ s₂) ≤
        4097 * 2 ^ networkRank (N.sub (N.inside S)) :=
    fun h => hC V {g : E // N.inside S g} (N.sub (N.inside S)) h s₁ s₂
  have hCap₂ : B ≤ networkRank (N.sub (N.outside S)) →
      4096 * ((N.sub (N.outside S)).numCycles + (N.sub (N.outside S)).numPaths t₁ t₂) ≤
        4097 * 2 ^ networkRank (N.sub (N.outside S)) :=
    fun h => hC V {g : E // N.outside S g} (N.sub (N.outside S)) h t₁ t₂
  have harith := two_cut_cap_arith hK hb₁ hb₂ hc₁ hc₂ hP₁ hP₂ hF₁ hF₂ hCap₁ hCap₂ (by omega)
  have e1 : networkRank N - 1 =
      networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) := by omega
  have e2 : (networkRank N + 1) / 2 =
      (networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) + 2) / 2 := by
    omega
  rw [e1, e2, hcount]
  exact harith

/-- **Proposition 6.3 of the paper, the case of a cut of size three, with caps.** Let `N` be a
connected cubic network of rank `r`, without a cyclic cut of size one or two, and let `S` be a
cyclic cut of size three. If `r` is large, then `N` has at most `2^(r-1) + 4 K 2^⌈r/2⌉`
cycles. -/
theorem numCycles_le_of_three_cut_cap {K B : ℕ} (hF : FewCyclesWith K) (hC : CapThreeWith B)
    {V E : Type} [Fintype V] [Fintype E] (N : Network V E) (hN : N.graph.Connected)
    (hcubic : N.IsCubic) (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 3 ≤ N.cutSize S)
    (S : V → Prop) (hS : N.cutSize S = 3) (hcyc : N.IsCyclicCut S)
    (hR : 2 * max B (2000000 * K) + 10 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 4 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- the three crossing edges
  have hcard : (Finset.univ.filter fun g : E => N.crosses S g).card = 3 := by
    rw [← natCard_subtype_eq_card_filter]
    exact hS
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, hC3⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ g, N.crosses S g ↔ g = e₁ ∨ g = e₂ ∨ g = e₃ := by
    intro g
    have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S g) ↔ N.crosses S g :=
      ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
    rw [← h1, hC3, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨s₁, t₁, he₁, hs₁, ht₁⟩ := exists_joins_of_crosses N ((hmem e₁).2 (Or.inl rfl))
  obtain ⟨s₂, t₂, he₂, hs₂, ht₂⟩ :=
    exists_joins_of_crosses N ((hmem e₂).2 (Or.inr (Or.inl rfl)))
  obtain ⟨s₃, t₃, he₃, hs₃, ht₃⟩ :=
    exists_joins_of_crosses N ((hmem e₃).2 (Or.inr (Or.inr rfl)))
  -- the complement of `S` is a cut of the same kind
  have hS' : N.cutSize (fun v => ¬ S v) = 3 := by
    rw [N.cutSize_not S]
    exact hS
  have hcyc' : 0 < (N.sub (N.inside fun v => ¬ S v)).numCycles := hcyc.2
  have hnn : ∀ v, S v → ¬ ¬ S v := fun v h h' => h' h
  -- the ends of the three edges are different
  have hsne : ∀ (e f : E) (s s' t t' : V), e ≠ f → N.Joins e s t → N.Joins f s' t' → S s →
      ¬ S t → ¬ S t' → s ≠ s' := by
    intro e f s s' t t' hef he hf hs ht ht' h
    subst h
    exact N.false_of_two_crossing_at hcubic (le_refl 3) hmin S hS hcyc.1 hef he hf hs ht ht'
  have htne : ∀ (e f : E) (s s' t t' : V), e ≠ f → N.Joins e s t → N.Joins f s' t' → S s →
      S s' → ¬ S t → t ≠ t' := by
    intro e f s s' t t' hef he hf hs hs' ht h
    subst h
    exact N.false_of_two_crossing_at hcubic (le_refl 3) hmin (fun v => ¬ S v) hS' hcyc' hef
      he.symm hf.symm ht (hnn s hs) (hnn s' hs')
  have hs12 := hsne e₁ e₂ s₁ s₂ t₁ t₂ h12 he₁ he₂ hs₁ ht₁ ht₂
  have hs13 := hsne e₁ e₃ s₁ s₃ t₁ t₃ h13 he₁ he₃ hs₁ ht₁ ht₃
  have hs23 := hsne e₂ e₃ s₂ s₃ t₂ t₃ h23 he₂ he₃ hs₂ ht₂ ht₃
  have ht12 := htne e₁ e₂ s₁ s₂ t₁ t₂ h12 he₁ he₂ hs₁ hs₂ ht₁
  have ht13 := htne e₁ e₃ s₁ s₃ t₁ t₃ h13 he₁ he₃ hs₁ hs₃ ht₁
  have ht23 := htne e₂ e₃ s₂ s₃ t₂ t₃ h23 he₂ he₃ hs₂ hs₃ ht₂
  -- both sides are connected
  have hin := N.reachable_inside_of_minimal hcubic (le_refl 3) (by norm_num) hmin S hS hs₁ ht₁
  have hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t₁ u :=
    N.reachable_inside_of_minimal hcubic (le_refl 3) (by norm_num) hmin (fun v => ¬ S v) hS'
      ht₁ (hnn s₁ hs₁)
  have hin2 : ∀ u v, S u → S v → (N.sub (N.inside S)).graph.Reachable u v :=
    fun u v hu hv => (hin u hu).symm.trans (hin v hv)
  have hout2 : ∀ u v, ¬ S u → ¬ S v → (N.sub (N.outside S)).graph.Reachable u v :=
    fun u v hu hv => (hout u hu).symm.trans (hout v hv)
  -- the rank and the count
  have hrank := N.networkRank_add_one_of_cut S hs₁ ht₁ hN hin hout
  have hS3 : Nat.card {g : E // N.crosses S g} = 3 := hS
  rw [hS3] at hrank
  have hcount := N.numCycles_of_three_crossing S (fun g hg => (hmem g).1 hg) he₁ he₂ he₃ hs₁ hs₂
    hs₃ ht₁ ht₂ ht₃ hs12 hs13 hs23 ht12 ht13 ht23
  -- the two sides are poles, and the ends of the edges are ports
  have hpole₁ : (N.sub (N.inside S)).IsWeakPole :=
    N.isWeakPole_inside hcubic (le_refl 3) (by norm_num) hmin S hS hcyc.1 hs₁ ht₁
  have hpole₂ : (N.sub (N.inside fun v => ¬ S v)).IsWeakPole :=
    N.isWeakPole_inside hcubic (le_refl 3) (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' ht₁
      (hnn s₁ hs₁)
  have hport₁ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.inside S)).IsPort s := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (le_refl 3) hmin S hS hcyc.1 hg hs' ht'
  have hport₂ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.inside fun v => ¬ S v)).IsPort t := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (le_refl 3) hmin (fun v => ¬ S v) hS' hcyc' hg.symm ht' (hnn s hs')
  have hp₁ := hport₁ e₁ s₁ t₁ he₁ hs₁ ht₁
  have hp₂ := hport₁ e₂ s₂ t₂ he₂ hs₂ ht₂
  have hp₃ := hport₁ e₃ s₃ t₃ he₃ hs₃ ht₃
  have hq₁ := hport₂ e₁ s₁ t₁ he₁ hs₁ ht₁
  have hq₂ := hport₂ e₂ s₂ t₂ he₂ hs₂ ht₂
  have hq₃ := hport₂ e₃ s₃ t₃ he₃ hs₃ ht₃
  -- a path of each side between the ends of each two crossing edges
  obtain ⟨Q₁₂, hQ₁₂, hw₁₂⟩ :=
    N.exists_isPathWord_of_reachable (N.outside S) ht12 (hout2 t₁ t₂ ht₁ ht₂)
  obtain ⟨Q₁₃, hQ₁₃, hw₁₃⟩ :=
    N.exists_isPathWord_of_reachable (N.outside S) ht13 (hout2 t₁ t₃ ht₁ ht₃)
  obtain ⟨Q₂₃, hQ₂₃, hw₂₃⟩ :=
    N.exists_isPathWord_of_reachable (N.outside S) ht23 (hout2 t₂ t₃ ht₂ ht₃)
  obtain ⟨R₁₂, hR₁₂, hv₁₂⟩ :=
    N.exists_isPathWord_of_reachable (N.inside S) hs12 (hin2 s₁ s₂ hs₁ hs₂)
  obtain ⟨R₁₃, hR₁₃, hv₁₃⟩ :=
    N.exists_isPathWord_of_reachable (N.inside S) hs13 (hin2 s₁ s₃ hs₁ hs₃)
  obtain ⟨R₂₃, hR₂₃, hv₂₃⟩ :=
    N.exists_isPathWord_of_reachable (N.inside S) hs23 (hin2 s₂ s₃ hs₂ hs₃)
  have k₁₂ : Hook N S e₁ e₂ s₁ s₂ t₁ t₂ Q₁₂ :=
    ⟨he₁, he₂, hs₁, hs₂, ht₁, ht₂, hs12, ht12, hQ₁₂, hw₁₂⟩
  have k₁₃ : Hook N S e₁ e₃ s₁ s₃ t₁ t₃ Q₁₃ :=
    ⟨he₁, he₃, hs₁, hs₃, ht₁, ht₃, hs13, ht13, hQ₁₃, hw₁₃⟩
  have k₂₃ : Hook N S e₂ e₃ s₂ s₃ t₂ t₃ Q₂₃ :=
    ⟨he₂, he₃, hs₂, hs₃, ht₂, ht₃, hs23, ht23, hQ₂₃, hw₂₃⟩
  have l₁₂ : Hook N (fun v => ¬ S v) e₁ e₂ t₁ t₂ s₁ s₂ R₁₂ :=
    ⟨he₁.symm, he₂.symm, ht₁, ht₂, hnn s₁ hs₁, hnn s₂ hs₂, ht12, hs12, hR₁₂,
      within_outside_not hv₁₂⟩
  have l₁₃ : Hook N (fun v => ¬ S v) e₁ e₃ t₁ t₃ s₁ s₃ R₁₃ :=
    ⟨he₁.symm, he₃.symm, ht₁, ht₃, hnn s₁ hs₁, hnn s₃ hs₃, ht13, hs13, hR₁₃,
      within_outside_not hv₁₃⟩
  have l₂₃ : Hook N (fun v => ¬ S v) e₂ e₃ t₂ t₃ s₂ s₃ R₂₃ :=
    ⟨he₂.symm, he₃.symm, ht₂, ht₃, hnn s₂ hs₂, hnn s₃ hs₃, ht23, hs23, hR₂₃,
      within_outside_not hv₂₃⟩
  -- Lemma 5.7 (b) for the two sides
  obtain ⟨hT₁₁, hT₁₂, hT₁₃⟩ := third_pairs hF k₁₂ k₁₃ k₂₃ hpole₁ hp₁ hp₂ hp₃ hin2
  obtain ⟨hT₂₁, hT₂₂, hT₂₃⟩ := third_pairs hF l₁₂ l₁₃ l₂₃ hpole₂ hq₁ hq₂ hq₃ hout2
  -- the hypotheses of the arithmetic
  have hb₁ := networkRank_pos_of_numCycles_pos _ hcyc.1
  have hb₂ := networkRank_pos_of_numCycles_pos _ hcyc.2
  have hc₁ := (N.sub (N.inside S)).numCycles_lt_two_pow
  have hc₂ := (N.sub (N.outside S)).numCycles_lt_two_pow
  have hX : ∀ s s' : V, (N.sub (N.inside S)).numPaths s s' ≤
      2 ^ networkRank (N.sub (N.inside S)) := (N.sub (N.inside S)).numPaths_le_two_pow
  have hY : ∀ t t' : V, (N.sub (N.outside S)).numPaths t t' ≤
      2 ^ networkRank (N.sub (N.outside S)) := (N.sub (N.outside S)).numPaths_le_two_pow
  have hF₁ : ∀ s s' : V, (N.sub (N.inside S)).IsPort s → (N.sub (N.inside S)).IsPort s' →
      s ≠ s' → 501 * 2 ^ networkRank (N.sub (N.inside S)) ≤
        1000 * (N.sub (N.inside S)).numPaths s s' →
      (N.sub (N.inside S)).numCycles ^ 2 ≤ K * 2 ^ networkRank (N.sub (N.inside S)) :=
    hF V {g : E // N.inside S g} (N.sub (N.inside S)) hpole₁
  have hF₂ : ∀ t t' : V, (N.sub (N.outside S)).IsPort t → (N.sub (N.outside S)).IsPort t' →
      t ≠ t' → 501 * 2 ^ networkRank (N.sub (N.outside S)) ≤
        1000 * (N.sub (N.outside S)).numPaths t t' →
      (N.sub (N.outside S)).numCycles ^ 2 ≤ K * 2 ^ networkRank (N.sub (N.outside S)) :=
    hF V {g : E // N.outside S g} (N.sub (N.outside S)) hpole₂
  -- the caps of the two sides
  have hCap₁ : B ≤ networkRank (N.sub (N.inside S)) →
      2048 * ((N.sub (N.inside S)).numCycles + ((N.sub (N.inside S)).numPaths s₂ s₃ +
        (N.sub (N.inside S)).numPaths s₁ s₃ + (N.sub (N.inside S)).numPaths s₁ s₂)) ≤
        4097 * 2 ^ networkRank (N.sub (N.inside S)) := by
    intro h
    have k := hC V {g : E // N.inside S g} (N.sub (N.inside S)) h s₁ s₂ s₃
    omega
  have hCap₂ : B ≤ networkRank (N.sub (N.outside S)) →
      2048 * ((N.sub (N.outside S)).numCycles + ((N.sub (N.outside S)).numPaths t₂ t₃ +
        (N.sub (N.outside S)).numPaths t₁ t₃ + (N.sub (N.outside S)).numPaths t₁ t₂)) ≤
        4097 * 2 ^ networkRank (N.sub (N.outside S)) := by
    intro h
    have k := hC V {g : E // N.outside S g} (N.sub (N.outside S)) h t₁ t₂ t₃
    omega
  have harith := three_cut_cap_arith (K := K) (B := B) hb₁ hb₂ (by omega) hc₁ hc₂ hCap₁ hCap₂
    (hX s₂ s₃) (hX s₁ s₃) (hX s₁ s₂) (hY t₂ t₃) (hY t₁ t₃) (hY t₁ t₂)
    (hF₁ s₂ s₃ hp₂ hp₃ hs23) (hF₁ s₁ s₃ hp₁ hp₃ hs13) (hF₁ s₁ s₂ hp₁ hp₂ hs12)
    (hF₂ t₂ t₃ hq₂ hq₃ ht23) (hF₂ t₁ t₃ hq₁ hq₃ ht13) (hF₂ t₁ t₂ hq₁ hq₂ ht12)
    hT₁₁ hT₁₂ hT₁₃ hT₂₁ hT₂₂ hT₂₃
  have e1 : networkRank N - 1 =
      networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) + 1 := by omega
  have e2 : (networkRank N + 1) / 2 =
      (networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) + 3) / 2 := by
    omega
  rw [e1, e2, hcount]
  exact harith

/-! ### The proposition -/

/-- **Proposition 6.3 of the paper for networks, with caps.** Let `N` be a connected cubic
network of rank `r` with a cyclic cut of size at most three. If `r` is large, then `N` has at
most `2^(r-1) + 4 K 2^⌈r/2⌉` cycles. The constant `K` is that of Theorem 5.4, and `B` is the
rank from which the caps hold. -/
theorem numCycles_le_of_small_cut_cap {K B : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K)
    (hC₂ : CapTwoWith B) (hC₃ : CapThreeWith B) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.graph.Connected) (hcubic : N.IsCubic) (S : V → Prop)
    (hcyc : N.IsCyclicCut S) (hS : N.cutSize S ≤ 3)
    (hR : 2 * max B (2000000 * K) + 10 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 4 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- a cyclic cut with the smallest number of crossing edges
  have hex : ∃ d, ∃ S' : V → Prop, N.IsCyclicCut S' ∧ N.cutSize S' = d := ⟨_, S, hcyc, rfl⟩
  obtain ⟨S₀, hcyc₀, hS₀⟩ := Nat.find_spec hex
  have hmin : ∀ S' : V → Prop, N.IsCyclicCut S' → Nat.find hex ≤ N.cutSize S' :=
    fun S' h' => Nat.find_min' hex ⟨S', h', rfl⟩
  have hd3 : Nat.find hex ≤ 3 := le_trans (hmin S hcyc) hS
  generalize Nat.find hex = d at hS₀ hmin hd3
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · -- no crossing edge: the network is not connected
    exfalso
    haveI : Nonempty V := hN.nonempty
    have hcyc' : 0 < (N.sub (N.inside fun v => ¬ S₀ v)).numCycles := hcyc₀.2
    obtain ⟨s₀, hs₀, -⟩ := N.exists_ne_of_numCycles_pos S₀ hcyc₀.1 (Classical.arbitrary V)
    obtain ⟨t₀, ht₀, -⟩ :=
      N.exists_ne_of_numCycles_pos (fun v => ¬ S₀ v) hcyc' (Classical.arbitrary V)
    have hclosed : ∀ e, S₀ (N.src e) ↔ S₀ (N.dst e) := by
      intro e
      refine Classical.not_not.1 fun hc => ?_
      haveI : Nonempty {g : E // N.crosses S₀ g} := ⟨⟨e, hc⟩⟩
      have hpos : 0 < Nat.card {g : E // N.crosses S₀ g} := Nat.card_pos
      have h0 : Nat.card {g : E // N.crosses S₀ g} = 0 := hS₀
      omega
    exact ht₀ (N.mem_of_reachable_of_closed S₀ hclosed (hN s₀ t₀) hs₀)
  · -- one crossing edge
    have hcard : (Finset.univ.filter fun g : E => N.crosses S₀ g).card = 1 := by
      rw [← natCard_subtype_eq_card_filter]
      exact hS₀
    obtain ⟨e, hCe⟩ := Finset.card_eq_one.1 hcard
    have hmem : ∀ g, N.crosses S₀ g ↔ g = e := by
      intro g
      have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S₀ g) ↔ N.crosses S₀ g :=
        ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
      rw [← h1, hCe, Finset.mem_singleton]
    obtain ⟨s, t, he, hs, ht⟩ := exists_joins_of_crosses N ((hmem e).2 rfl)
    have h := N.numCycles_le_of_bridge S₀ hN he hs ht (fun g hg => (hmem g).1 hg) hcyc₀.1
      hcyc₀.2
    exact le_trans h (Nat.le_add_right _ _)
  · -- two crossing edges
    have hmax : max B (16 * K) ≤ max B (2000000 * K) := max_le_max (le_refl B) (by omega)
    have h := numCycles_le_of_two_cut_cap hK hF hC₂ N hN hcubic hmin S₀ hS₀ hcyc₀ (by omega)
    have hle : 2 * K * 2 ^ ((networkRank N + 1) / 2) ≤
        4 * K * 2 ^ ((networkRank N + 1) / 2) := Nat.mul_le_mul_right _ (by omega)
    exact le_trans h (Nat.add_le_add_left hle _)
  · -- three crossing edges
    exact numCycles_le_of_three_cut_cap hF hC₃ N hN hcubic hmin S₀ hS₀ hcyc₀ hR

/-- **Proposition 6.3 of the paper**, from Theorem 5.4 for `ε = 1/1000` and the caps. A
connected cubic multigraph of large rank `r`, without a loop and with a cyclic cut of size at
most three, has at most `2^(r-1) + K 2^⌈r/2⌉` cycles. -/
theorem threeCutStatement_of_caps (hF : FewCyclesStatement) (hC : CapStatement) :
    ThreeCutStatement := by
  obtain ⟨K, hK, hF⟩ := hF
  obtain ⟨B, hC₂, hC₃⟩ := hC
  refine ⟨4 * K, 2 * max B (2000000 * K) + 10, ?_⟩
  rintro M hconn hcubic hloop hR ⟨U, hU, hcard⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  -- the two sides contain a cycle
  have hcyc : M.looplessNetwork.IsCyclicCut (fun v => v ∈ U) := by
    constructor
    · obtain ⟨y, hy, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl U).1 hU.1
      exact numCycles_sub_pos _ _ hy hw
    · obtain ⟨y, hy, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl Uᶜ).1 hU.2
      exact numCycles_sub_pos _ _ hy
        (fun e he => ⟨Finset.mem_compl.1 (hw e he).1, Finset.mem_compl.1 (hw e he).2⟩)
  -- the crossing edges are cut edges
  have hsize : M.looplessNetwork.cutSize (fun v => v ∈ U) ≤ 3 := by
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ U) e} →
        {e : M.Edge // e ∈ M.cutEdges U}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses U e.1).2 e.2⟩, fun _ => rfl⟩
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
      exact Subtype.ext (Subtype.ext h1)
    have h1 := Nat.card_le_card_of_injective f hinj
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges U} = (M.cutEdges U).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ U) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ U) e} := rfl
    omega
  have h := numCycles_le_of_small_cut_cap hK hF hC₂ hC₃ M.looplessNetwork hN hcub
    (fun v => v ∈ U) hcyc hsize (by rw [← M.cycleRank_eq_networkRank hl]; exact hR)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h

end Erdos1016.ExactMaximum

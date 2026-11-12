import Erdos1016.ExactMaximum.ThirdPair

set_option autoImplicit false

/-!
# A cyclic cut of size three

This file proves the case `d = 3` of Proposition 6.3 of the paper "The maximum number of cycles
in a graph of large rank": a connected cubic network of large rank `r` whose smallest cyclic cut
has three edges has at most `2^(r-1) + 4 K 2^(r/2)` cycles (`numCycles_le_of_three_cut`). Like
`numCycles_le_of_two_cut`, the theorem has the two statements about poles as hypotheses.

The first part of the file is arithmetic. For each side, the three pairs of ports are numbered by
the port that is not in the pair: `X₁, X₂, X₃` are the numbers of paths of the first side, and
`Y₁, Y₂, Y₃` those of the second side. The number of cycles is
`c₁ + c₂ + X₁ Y₁ + X₂ Y₂ + X₃ Y₃`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance threeCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Arithmetic -/

/-- From `c² ≤ M² 2^b`: `c ≤ M 2^⌈b/2⌉`. -/
theorem le_of_sq_le_sq {c M b : ℕ} (h : c ^ 2 ≤ M ^ 2 * 2 ^ b) : c ≤ M * 2 ^ ((b + 1) / 2) := by
  have h1 : M ^ 2 * 2 ^ b ≤ (M * 2 ^ ((b + 1) / 2)) ^ 2 := by
    have e1 : (M * 2 ^ ((b + 1) / 2)) ^ 2 = M ^ 2 * 2 ^ (2 * ((b + 1) / 2)) := by ring
    rw [e1]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (le_trans h h1)

/-- The product of two small numbers of paths. -/
theorem mul_le_of_sq_le {X Y K b₁ b₂ : ℕ} (hX : X ^ 2 ≤ 2 * K * 2 ^ b₁)
    (hY : Y ^ 2 ≤ 2 * K * 2 ^ b₂) : X * Y ≤ 2 * K * 2 ^ ((b₁ + b₂ + 1) / 2) := by
  apply le_of_sq_le_sq
  calc (X * Y) ^ 2 = X ^ 2 * Y ^ 2 := by ring
    _ ≤ (2 * K * 2 ^ b₁) * (2 * K * 2 ^ b₂) := Nat.mul_le_mul hX hY
    _ = (2 * K) ^ 2 * 2 ^ (b₁ + b₂) := by ring

/-- From `Y² ≤ 2 K D` and `2000000 K ≤ D`: `1000 Y ≤ D`. -/
theorem thousand_mul_le {Y K D : ℕ} (h : Y ^ 2 ≤ 2 * K * D) (hD : 2000000 * K ≤ D) :
    1000 * Y ≤ D := by
  have h1 : (1000 * Y) * (1000 * Y) ≤ D * D := by
    calc (1000 * Y) * (1000 * Y) = 1000000 * Y ^ 2 := by ring
      _ ≤ 1000000 * (2 * K * D) := Nat.mul_le_mul_left _ h
      _ = (2000000 * K) * D := by ring
      _ ≤ D * D := Nat.mul_le_mul_right D hD
  exact Nat.mul_self_le_mul_self_iff.1 h1

/-- The count for a cut of size three, when the second side has two pairs of ports with many
paths: the pairs `2` and `3`. Then the pair `1` of the second side has few paths. -/
theorem three_cut_arith_ii {K c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁)
    (h16 : 16 ≤ 2 ^ b₂) (h2M : 2000000 * K ≤ 2 ^ b₂) (hc₁ : c₁ < 2 ^ b₁)
    (hG₂ : 16 * c₂ ≤ 9 * 2 ^ b₂) (hX₁ : X₁ ≤ 2 ^ b₁) (hX₂ : X₂ ≤ 2 ^ b₁) (hX₃ : X₃ ≤ 2 ^ b₁)
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

/-- The count for a cut of size three, when the first side has the smaller rank. -/
theorem three_cut_arith_aux {K B c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁)
    (hle : b₁ ≤ b₂) (hlarge : 2 * max B (2000000 * K) + 8 ≤ b₁ + b₂) (hc₁ : c₁ < 2 ^ b₁)
    (hG₂ : B ≤ b₂ → 16 * c₂ ≤ 9 * 2 ^ b₂) (hX₁ : X₁ ≤ 2 ^ b₁) (hX₂ : X₂ ≤ 2 ^ b₁)
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
  have hG := hG₂ hB
  by_cases k1 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₃)
  · exact three_cut_arith_ii hb₁ h16 h2M hc₁ hG hX₁ hX₂ hX₃ hY₂ hY₃ (hT₂₁ k1) k1 hF₁₂ hF₁₃
      hF₂₂ hF₂₃ hT₁₁
  by_cases k2 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₃)
  · have k := three_cut_arith_ii hb₁ h16 h2M hc₁ hG hX₂ hX₁ hX₃ hY₁ hY₃ (hT₂₂ k2) k2 hF₁₁
      hF₁₃ hF₂₁ hF₂₃ hT₁₂
    omega
  by_cases k3 : 1002 * 2 ^ b₂ ≤ 1000 * (Y₁ + Y₂)
  · have k := three_cut_arith_ii hb₁ h16 h2M hc₁ hG hX₃ hX₂ hX₁ hY₂ hY₁ (hT₂₃ k3)
      (by omega : 1002 * 2 ^ b₂ ≤ 1000 * (Y₂ + Y₁)) hF₁₂ hF₁₁ hF₂₂ hF₂₁
      (fun k' => hT₁₃ (by omega))
    omega
  -- no two pairs of the second side have many paths
  have hA2 : 2 ≤ 2 ^ b₁ := Nat.le_self_pow (by omega) 2
  have hAD : 2 ^ (b₁ + b₂) = 2 ^ b₁ * 2 ^ b₂ := pow_add 2 b₁ b₂
  rw [hAD]
  have q1 : X₁ * Y₁ ≤ 2 ^ b₁ * Y₁ := Nat.mul_le_mul_right Y₁ hX₁
  have q2 : X₂ * Y₂ ≤ 2 ^ b₁ * Y₂ := Nat.mul_le_mul_right Y₂ hX₂
  have q3 : X₃ * Y₃ ≤ 2 ^ b₁ * Y₃ := Nat.mul_le_mul_right Y₃ hX₃
  have q4 : 2000 * (2 ^ b₁ * Y₁ + 2 ^ b₁ * Y₂ + 2 ^ b₁ * Y₃) ≤ 3006 * (2 ^ b₁ * 2 ^ b₂) := by
    calc 2000 * (2 ^ b₁ * Y₁ + 2 ^ b₁ * Y₂ + 2 ^ b₁ * Y₃)
        = 2 ^ b₁ * (2000 * (Y₁ + Y₂ + Y₃)) := by ring
      _ ≤ 2 ^ b₁ * (3006 * 2 ^ b₂) := Nat.mul_le_mul_left _ (by omega)
      _ = 3006 * (2 ^ b₁ * 2 ^ b₂) := by ring
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
  generalize 2 ^ b₁ * 2 ^ b₂ = P at *
  omega

/-- The count for a cut of size three. The products are in the order of the count
`numCycles_of_three_crossing`. -/
theorem three_cut_arith {K B c₁ c₂ b₁ b₂ X₁ X₂ X₃ Y₁ Y₂ Y₃ : ℕ} (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hlarge : 2 * max B (2000000 * K) + 8 ≤ b₁ + b₂) (hc₁ : c₁ < 2 ^ b₁) (hc₂ : c₂ < 2 ^ b₂)
    (hG₁ : B ≤ b₁ → 16 * c₁ ≤ 9 * 2 ^ b₁) (hG₂ : B ≤ b₂ → 16 * c₂ ≤ 9 * 2 ^ b₂)
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
  · have k := three_cut_arith_aux hb₁ h hlarge hc₁ hG₂ hX₁ hX₂ hX₃ hY₁ hY₂ hY₃ hF₁₁ hF₁₂ hF₁₃
      hF₂₁ hF₂₂ hF₂₃ hT₁₁ hT₁₂ hT₁₃ hT₂₁ hT₂₂ hT₂₃
    omega
  · have k := three_cut_arith_aux hb₂ h (by omega : 2 * max B (2000000 * K) + 8 ≤ b₂ + b₁) hc₂
      hG₁ hY₁ hY₂ hY₃ hX₁ hX₂ hX₃ hF₂₁ hF₂₂ hF₂₃ hF₁₁ hF₁₂ hF₁₃ hT₂₁ hT₂₂ hT₂₃ hT₁₁ hT₁₂ hT₁₃
    rw [add_comm b₂ b₁, Nat.mul_comm Y₁ X₁, Nat.mul_comm Y₂ X₂, Nat.mul_comm Y₃ X₃] at k
    omega

/-! ### The three pairs of ports of a side -/

/-- The number of paths between two vertices does not depend on their order. -/
theorem numPaths_symm {V E : Type*} [Fintype E] (N : Network V E) (s t : V) :
    N.numPaths s t = N.numPaths t s :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x : N.Word =>
    ⟨fun h : N.IsPathWord s t x => h.symm, fun h : N.IsPathWord t s x => h.symm⟩)

/-- A word within the first side of a cut is within the second side of the cut of the
complement. -/
theorem within_outside_not {V E : Type*} {N : Network V E} {S : V → Prop} {x : E → Bit}
    (hx : Within x (N.inside S)) : Within x (N.outside fun v => ¬ S v) :=
  fun e he => ⟨fun h => h (hx e he).1, fun h => h (hx e he).2⟩

/-- **Lemma 5.7 (b) of the paper for the three ports of a side.** Let the first side of a cut
with three crossing edges be a pole, and let the second side contain a path between the ends of
each two crossing edges. If two of the three pairs of ports of the first side have together at
least `1.002 · 2^b` paths, then the third pair has at most `(2 K 2^b)^(1/2)` paths. -/
theorem third_pairs {K : ℕ} (hF : FewCyclesWith K) {V E : Type} [Fintype V] [Fintype E]
    {N : Network V E} {S : V → Prop} {e₁ e₂ e₃ : E} {s₁ s₂ s₃ t₁ t₂ t₃ : V}
    {Q₁₂ Q₁₃ Q₂₃ : N.Word} (h₁₂ : Hook N S e₁ e₂ s₁ s₂ t₁ t₂ Q₁₂)
    (h₁₃ : Hook N S e₁ e₃ s₁ s₃ t₁ t₃ Q₁₃) (h₂₃ : Hook N S e₂ e₃ s₂ s₃ t₂ t₃ Q₂₃)
    (hT : (N.sub (N.inside S)).IsWeakPole) (hp₁ : (N.sub (N.inside S)).IsPort s₁)
    (hp₂ : (N.sub (N.inside S)).IsPort s₂) (hp₃ : (N.sub (N.inside S)).IsPort s₃)
    (hin : ∀ u v, S u → S v → (N.sub (N.inside S)).graph.Reachable u v) :
    (1002 * 2 ^ networkRank (N.sub (N.inside S)) ≤
        1000 * ((N.sub (N.inside S)).numPaths s₁ s₃ + (N.sub (N.inside S)).numPaths s₁ s₂) →
      (N.sub (N.inside S)).numPaths s₂ s₃ ^ 2 ≤ 2 * K * 2 ^ networkRank (N.sub (N.inside S))) ∧
    (1002 * 2 ^ networkRank (N.sub (N.inside S)) ≤
        1000 * ((N.sub (N.inside S)).numPaths s₂ s₃ + (N.sub (N.inside S)).numPaths s₁ s₂) →
      (N.sub (N.inside S)).numPaths s₁ s₃ ^ 2 ≤ 2 * K * 2 ^ networkRank (N.sub (N.inside S))) ∧
    (1002 * 2 ^ networkRank (N.sub (N.inside S)) ≤
        1000 * ((N.sub (N.inside S)).numPaths s₂ s₃ + (N.sub (N.inside S)).numPaths s₁ s₃) →
      (N.sub (N.inside S)).numPaths s₁ s₂ ^ 2 ≤ 2 * K * 2 ^ networkRank (N.sub (N.inside S))) := by
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · -- the pair of `s₂` and `s₃`; the third port is `s₁`
    refine third_pair hF h₂₃ hT hp₂ hp₃ hp₁ h₁₂.hs₁ h₁₂.hs.symm h₁₃.hs.symm
      (fun u hu => hin s₂ u h₂₃.hs₁ hu) ?_
    rw [numPaths_symm _ s₂ s₁, numPaths_symm _ s₃ s₁]
    omega
  · -- the pair of `s₁` and `s₃`; the third port is `s₂`
    refine third_pair hF h₁₃ hT hp₁ hp₃ hp₂ h₁₂.hs₂ h₁₂.hs h₂₃.hs.symm
      (fun u hu => hin s₁ u h₁₃.hs₁ hu) ?_
    rw [numPaths_symm _ s₃ s₂]
    omega
  · -- the pair of `s₁` and `s₂`; the third port is `s₃`
    refine third_pair hF h₁₂ hT hp₁ hp₂ hp₃ h₁₃.hs₂ h₁₃.hs h₂₃.hs
      (fun u hu => hin s₁ u h₁₂.hs₁ hu) ?_
    omega

/-! ### The theorem -/

/-- **Proposition 6.3 of the paper, the case of a cut of size three.** Let `N` be a connected
cubic network of rank `r`, without a cyclic cut of size one or two, and let `S` be a cyclic cut
of size three. If `r` is large, then `N` has at most `2^(r-1) + 4 K 2^⌈r/2⌉` cycles. The
constants `K` and `B` are those of the two statements about poles. -/
theorem numCycles_le_of_three_cut {K B : ℕ} (hF : FewCyclesWith K) (hG : PoleCycleBoundWith B)
    {V E : Type} [Fintype V] [Fintype E] (N : Network V E) (hN : N.graph.Connected)
    (hcubic : N.IsCubic) (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 3 ≤ N.cutSize S)
    (S : V → Prop) (hS : N.cutSize S = 3) (hcyc : N.IsCyclicCut S)
    (hR : 2 * max B (2000000 * K) + 10 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 4 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- the three crossing edges
  have hcard : (Finset.univ.filter fun g : E => N.crosses S g).card = 3 := by
    rw [← natCard_subtype_eq_card_filter]
    exact hS
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, hC⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ g, N.crosses S g ↔ g = e₁ ∨ g = e₂ ∨ g = e₃ := by
    intro g
    have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S g) ↔ N.crosses S g :=
      ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
    rw [← h1, hC, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
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
  have hG₁ := hG V {g : E // N.inside S g} (N.sub (N.inside S)) hpole₁
  have hG₂ : B ≤ networkRank (N.sub (N.outside S)) →
      16 * (N.sub (N.outside S)).numCycles ≤ 9 * 2 ^ networkRank (N.sub (N.outside S)) :=
    hG V {g : E // N.outside S g} (N.sub (N.outside S)) hpole₂
  have harith := three_cut_arith (K := K) (B := B) hb₁ hb₂ (by omega) hc₁ hc₂ hG₁ hG₂
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

end Erdos1016.ExactMaximum

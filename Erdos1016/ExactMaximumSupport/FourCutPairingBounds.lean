import Erdos1016.ExactMaximum.FourCutArithmetic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Bilinear bounds for the three cut pairings

These are scalar inequalities on the exact pairingSum from the four-cut interface.
No graph premise is included.
-/
namespace Erdos1016.ExactMaximumSupport.FourCutPairingBounds
open ExactMaximum

/-- Pairing products are nonnegative. -/
theorem pairingSum_nonneg (p u : Fin 3 → ℝ)
    (hp : ∀ i,0≤p i) (hu : ∀ i,0≤u i) : 0≤pairingSum p u := by
  unfold pairingSum
  exact add_nonneg
    (add_nonneg (mul_nonneg (hp 0) (add_nonneg (hu 1) (hu 2)))
      (mul_nonneg (hp 1) (add_nonneg (hu 0) (hu 2))))
    (mul_nonneg (hp 2) (add_nonneg (hu 0) (hu 1)))

/-- A vector of total mass at most one cannot exceed the other vector's total mass. -/
theorem pairingSum_le_sum (p u : Fin 3 → ℝ)
    (hp : ∀ i,0≤p i) (hu : ∀ i,0≤u i) (hs : p 0+p 1+p 2≤1) :
    pairingSum p u ≤ u 0+u 1+u 2 := by
  have h0 := mul_nonneg (hp 0) (hu 0)
  have h1 := mul_nonneg (hp 1) (hu 1)
  have h2 := mul_nonneg (hp 2) (hu 2)
  have hsum := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (add_nonneg (hu 0) (hu 1)) (hu 2))
  unfold pairingSum
  nlinarith

private theorem three_term_half (p₀ p₁ p₂ u₀ u₁ u₂ : ℝ)
    (hu₁ : 0≤u₁) (hu₂ : 0≤u₂) (hs : p₀+p₁+p₂≤1)
    (hp₁ : p₁≤1/2) (hp₂ : p₂≤1/2) (h₁ : u₁≤u₀) (h₂ : u₂≤u₀) :
    p₀*(u₁+u₂)+p₁*(u₀+u₂)+p₂*(u₀+u₁) ≤ (u₀+u₁+u₂+u₀)/2 := by
  have hA := mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hu₁ hu₂)
  have hB := mul_nonneg (sub_nonneg.mpr hp₁) (sub_nonneg.mpr h₁)
  have hC := mul_nonneg (sub_nonneg.mpr hp₂) (sub_nonneg.mpr h₂)
  nlinarith

/-- Half-bounded coordinates give the paper's bound using a largest opposite coordinate. -/
theorem pairingSum_le_half_sum_add (p u : Fin 3 → ℝ) (γ : Fin 3)
    (hu : ∀ i,0≤u i) (hp : ∀ i,p i≤1/2) (hs : p 0+p 1+p 2≤1)
    (hmax : ∀ i,u i≤u γ) :
    pairingSum p u ≤ (u 0+u 1+u 2+u γ)/2 := by
  fin_cases γ
  · exact three_term_half _ _ _ _ _ _ (hu 1) (hu 2) hs (hp 1) (hp 2) (hmax 1) (hmax 2)
  · change pairingSum p u ≤ (u 0+u 1+u 2+u 1)/2
    have hh := three_term_half (p 1) (p 0) (p 2) (u 1) (u 0) (u 2)
      (hu 0) (hu 2) (by linarith) (hp 0) (hp 2) (hmax 0) (hmax 2)
    unfold pairingSum
    nlinarith
  · change pairingSum p u ≤ (u 0+u 1+u 2+u 2)/2
    have hh := three_term_half (p 2) (p 0) (p 1) (u 2) (u 0) (u 1)
      (hu 0) (hu 1) (by linarith) (hp 0) (hp 1) (hmax 0) (hmax 1)
    unfold pairingSum
    nlinarith

/-- Two half-bounded vectors of mass at most one contribute at most three quarters. -/
theorem pairingSum_le_three_quarters (p u : Fin 3 → ℝ)
    (hu : ∀ i,0≤u i) (hp : ∀ i,p i≤1/2) (huHalf : ∀ i,u i≤1/2)
    (hs : p 0+p 1+p 2≤1) (ht : u 0+u 1+u 2≤1) :
    pairingSum p u ≤ 3/4 := by
  have hm : ∃ γ : Fin 3,∀ i,u i≤u γ := by
    obtain ⟨γ,_,hγ⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
    exact ⟨γ,fun i => hγ i (Finset.mem_univ i)⟩
  obtain ⟨γ,hγ⟩ := hm
  have hh := pairingSum_le_half_sum_add p u γ hu hp hs hγ
  have hhγ := huHalf γ
  linarith

end Erdos1016.ExactMaximumSupport.FourCutPairingBounds

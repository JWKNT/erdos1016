import Erdos1016.ExactMaximumSupport.Shortening.MarginFewCycles

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Uniform normalized decay from the actual square-root cycle bound. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.MarginDecay
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- An elementary, uniform rank threshold; no asymptotic axiom is used. -/
theorem exists_scale (K : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃R:ℕ,∀r:ℕ,R≤r → (K:ℝ)≤δ^2*(2:ℝ)^r := by
  obtain ⟨R,hR⟩ := exists_nat_gt ((K:ℝ)/δ^2)
  refine ⟨R,?_⟩
  intro r hr
  have hrR : (R:ℝ)≤r := by exact_mod_cast hr
  have hrpow : (r:ℝ)≤(2:ℝ)^r := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=r)))
  have hK := (div_le_iff₀ (by positivity : 0<δ^2)).mp hR.le
  nlinarith [mul_le_mul_of_nonneg_right (hrR.trans hrpow) (sq_nonneg δ)]

/-- A square bound becomes a normalized first-order bound. -/
theorem normalized_le {c K r : ℕ} {δ : ℝ} (hδ : 0≤δ)
    (hc : c^2≤K*2^r) (hK : (K:ℝ)≤δ^2*(2:ℝ)^r) :
    (c:ℝ)/(2:ℝ)^r≤δ := by
  have hD : 0<(2:ℝ)^r := by positivity
  have hcR : (c:ℝ)^2≤(K:ℝ)*(2:ℝ)^r := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_right hK hD.le
  rw [div_le_iff₀ hD]
  nlinarith [mul_nonneg hδ hD.le]

/-- Rich weak poles have uniformly vanishing normalized cycle counts. -/
theorem exists_bound (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ) :
    ∃R:ℕ,∀(V E:Type) [Fintype V] [Fintype E] (N:Network V E),
      N.IsWeakPole → ∀s t,N.IsPort s → N.IsPort t → s≠t →
      (1/2+ε)*(2:ℝ)^networkRank N≤N.numPaths s t → R≤networkRank N →
      (N.numCycles:ℝ)/(2:ℝ)^networkRank N≤δ := by
  obtain ⟨K,hK⟩ := MarginFewCycles.exists_bound ε hε
  obtain ⟨R,hR⟩ := exists_scale K δ hδ
  refine ⟨R,?_⟩
  intro V E _ _ N hN s t hs ht hst hrich hr
  exact normalized_le hδ.le (hK V E N hN s t hs ht hst hrich) (hR _ hr)

end Erdos1016.ExactMaximumSupport.Shortening.MarginDecay

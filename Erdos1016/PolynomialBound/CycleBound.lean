import Erdos1016.PolynomialBound.ForestStatement
import Erdos1016.CycleCount.Bound

set_option autoImplicit false

/-!
# From the polynomial forest estimate to the number of cycles

A forest estimate with error `r ^ (-κ)` gives a cycle-count bound with a
polynomial error. The proof is the chord argument of
`Erdos1016.CycleCount.connected_bound`, with about `(log₂ r) / 100` triangles.
The triangles form a witness with at most `(log₂ r) / 100` components, which
the forest estimate permits. The cycles that avoid all selected edges number at
most `2 ^ (r - t)`, and `2 ^ (-t) ≤ 2 * r ^ (-1/100)`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Erdos1016.PolynomialBound
open PhysicalGraph ShortProof CycleCount

/-- The cycle-count bound with a polynomial error, for physical graphs. -/
def PolynomialCycleCountBound : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ r₁ : ℕ, ∀ G : PhysicalGraph, r₁ ≤ G.cycleRank →
    (cycleCount G : ℝ) ≤ (1 / 2 + (G.cycleRank : ℝ) ^ (-κ)) * 2 ^ G.cycleRank

set_option exponentiation.threshold 2048 in
/-- The number of triangles used at rank `r`, with the inequalities it needs. -/
theorem triangle_parameters {r : ℕ} (hr : 2 ^ 2048 ≤ r) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ r ∧ (3 * t) ^ 2 ≤ r ∧
      (100 : ℝ) * (t : ℝ) ≤ Real.logb 2 r ∧
      (2 : ℝ) ^ (r - t) ≤ 2 * (r : ℝ) ^ (-(1 / 100 : ℝ)) * 2 ^ r := by
  have hr0 : r ≠ 0 := by
    have h : 0 < 2 ^ 2048 := by positivity
    omega
  have hs_le : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 hr0
  have hs_lt : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
  have hs2048 : 2048 ≤ Nat.log 2 r := (Nat.pow_le_iff_le_log Nat.one_lt_two hr0).1 hr
  generalize Nat.log 2 r = s at hs_le hs_lt hs2048
  have hss : s < 2 ^ s := Nat.lt_two_pow_self
  have hdiv1 : 100 * (s / 100) ≤ s := Nat.mul_div_le s 100
  have hdiv2 : s < 100 * (s / 100 + 1) := by
    have := Nat.lt_mul_div_succ s (by norm_num : 0 < 100)
    omega
  generalize s / 100 = t at hdiv1 hdiv2
  have hrR : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := Nat.pos_of_ne_zero hr0
    exact_mod_cast this
  refine ⟨t, by omega, by omega, ?_, ?_, ?_⟩
  · have h1 : 3 * t ≤ s := by omega
    have h2 : (3 * t) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : s ^ 2 ≤ 2 ^ s := sq_le_two_pow s (by omega)
    omega
  · have hlog : (s : ℝ) ≤ Real.logb 2 r := natCast_le_logb (by exact_mod_cast hs_le)
    have h100 : ((100 * t : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hdiv1
    push_cast at h100
    linarith
  · have htr : t ≤ r := by omega
    have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (t + 1) := by positivity
    have h1 : (r : ℝ) ≤ ((2 : ℝ) ^ (t + 1)) ^ (100 : ℕ) := by
      rw [← pow_mul]
      have hnat : r ≤ 2 ^ ((t + 1) * 100) :=
        hs_lt.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact_mod_cast hnat
    have h2 : (r : ℝ) ^ ((1 : ℝ) / 100) ≤
        (((2 : ℝ) ^ (t + 1)) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow hrR.le h1 (by norm_num)
    have h3 : (((2 : ℝ) ^ (t + 1)) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) = (2 : ℝ) ^ (t + 1) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (t + 1)) 100, ← Real.rpow_mul hpow2.le]
      norm_num
    have h4 : (r : ℝ) ^ ((1 : ℝ) / 100) ≤ (2 : ℝ) ^ (t + 1) := h3 ▸ h2
    have hpos : (0 : ℝ) < (r : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos hrR _
    have h5 : ((2 : ℝ) ^ (t + 1))⁻¹ ≤ (r : ℝ) ^ (-((1 : ℝ) / 100)) := by
      rw [Real.rpow_neg hrR.le]
      exact inv_anti₀ hpos h4
    have h6 : ((2 : ℝ) ^ t)⁻¹ ≤ 2 * (r : ℝ) ^ (-((1 : ℝ) / 100)) := by
      have e : ((2 : ℝ) ^ t)⁻¹ = 2 * ((2 : ℝ) ^ (t + 1))⁻¹ := by
        rw [pow_succ]
        field_simp
      rw [e]
      linarith
    have h7 : (2 : ℝ) ^ (r - t) = 2 ^ r * ((2 : ℝ) ^ t)⁻¹ := by
      rw [pow_sub₀ (2 : ℝ) (by norm_num) htr]
    rw [h7]
    have h8 : (2 : ℝ) ^ r * ((2 : ℝ) ^ t)⁻¹ ≤
        2 ^ r * (2 * (r : ℝ) ^ (-((1 : ℝ) / 100))) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    linarith

/-- The bound for a connected graph, from the forest estimate above `rmin`. -/
theorem connected_bound (κ : ℝ) (hκ : 0 < κ) (rmin : ℕ)
    (hmin : ∀ (G : PhysicalGraph), G.IsConnected → rmin ≤ G.cycleRank →
      ∀ F : Finset G.CycleWord, F.Nonempty →
        (witnessSupportEdges G F).card ^ 2 ≤ G.cycleRank →
        100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
          Real.logb 2 (G.cycleRank : ℝ) →
        outsideForestProbability G (witnessSupportEdges G F) ≤
          (1 / 2 : ℝ) + (G.cycleRank : ℝ) ^ (-κ))
    (G : PhysicalGraph) (hG : G.IsConnected) (hr1 : rmin ≤ G.cycleRank)
    (hr2 : 2 ^ 2048 ≤ G.cycleRank) :
    (cycleCount G : ℝ) ≤
      (1 / 2 + (G.cycleRank : ℝ) ^ (-κ) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ))) *
        2 ^ G.cycleRank := by
  obtain ⟨t, ht1, htr, ht9, ht100, htl⟩ := triangle_parameters hr2
  have hr0 : (0 : ℝ) < (G.cycleRank : ℝ) := by
    have h : 0 < G.cycleRank := lt_of_lt_of_le (by positivity) hr2
    exact_mod_cast h
  have hB : ∀ (H : PhysicalGraph) (F : Finset H.CycleWord), H.IsConnected →
      G.cycleRank ≤ H.cycleRank → F.Nonempty → F.card ≤ t →
      (∀ T ∈ F, H.wordLength T.1 = 3) →
      outsideForestProbability H (witnessSupportEdges H F) ≤
        1 / 2 + (G.cycleRank : ℝ) ^ (-κ) := by
    intro H F hH hrank hne hcard h3
    have hrankR : (G.cycleRank : ℝ) ≤ (H.cycleRank : ℝ) := by exact_mod_cast hrank
    have hW : (witnessSupportEdges H F).card ≤ 3 * F.card := by
      unfold witnessSupportEdges
      refine (Finset.card_biUnion_le).trans ?_
      have hsum : ∑ T ∈ F, (H.edgeSupport T.1).card = ∑ _T ∈ F, 3 :=
        Finset.sum_congr rfl (fun T hT => h3 T hT)
      rw [hsum]
      simp [mul_comm]
    have hW2 : (witnessSupportEdges H F).card ^ 2 ≤ H.cycleRank := by
      have h : (witnessSupportEdges H F).card ≤ 3 * t := hW.trans (by omega)
      exact ((Nat.pow_le_pow_left h 2).trans ht9).trans hrank
    have hcomp : 100 * (Nat.card (cycleUnionGraph H F).ConnectedComponent : ℝ) ≤
        Real.logb 2 (H.cycleRank : ℝ) := by
      have hc := cycleUnion_component_count_le H F
      have hc' : (Nat.card (cycleUnionGraph H F).ConnectedComponent : ℝ) ≤ t := by
        exact_mod_cast hc.trans hcard
      have hlog : Real.logb 2 (G.cycleRank : ℝ) ≤ Real.logb 2 (H.cycleRank : ℝ) :=
        Real.logb_le_logb_of_le one_lt_two hr0 hrankR
      linarith
    have hest := hmin H hH (hr1.trans hrank) F hne hW2 hcomp
    have hmono : (H.cycleRank : ℝ) ^ (-κ) ≤ (G.cycleRank : ℝ) ^ (-κ) :=
      Real.rpow_le_rpow_of_exponent_nonpos hr0 hrankR (by linarith)
    linarith
  have hmain := card_cycleWord_le G hG t htr ht1 _ hB
  unfold cycleCount
  calc (Fintype.card G.CycleWord : ℝ)
      ≤ (1 / 2 + (G.cycleRank : ℝ) ^ (-κ)) * 2 ^ G.cycleRank +
          2 ^ (G.cycleRank - t) := hmain
    _ ≤ (1 / 2 + (G.cycleRank : ℝ) ^ (-κ)) * 2 ^ G.cycleRank +
          2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ)) * 2 ^ G.cycleRank := by linarith
    _ = (1 / 2 + (G.cycleRank : ℝ) ^ (-κ) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ))) *
          2 ^ G.cycleRank := by ring

/-- The polynomial forest estimate implies the polynomial cycle-count bound. -/
theorem polynomialCycleCountBound_of_forestEstimate (hforest : PolynomialForestEstimate) :
    PolynomialCycleCountBound := by
  obtain ⟨κ₀, hκ₀, rmin, hmin⟩ := hforest
  have hκ : 0 < min κ₀ (1 / 100) / 2 := by
    have : 0 < min κ₀ ((1 : ℝ) / 100) := lt_min hκ₀ (by norm_num)
    linarith
  set κ : ℝ := min κ₀ (1 / 100) / 2 with hκdef
  have hκ1 : 2 * κ ≤ κ₀ := by
    have := min_le_left κ₀ ((1 : ℝ) / 100)
    rw [hκdef]
    linarith
  have hκ2 : 2 * κ ≤ 1 / 100 := by
    have := min_le_right κ₀ ((1 : ℝ) / 100)
    rw [hκdef]
    linarith
  have hlim : Tendsto (fun r : ℕ => (r : ℝ) ^ κ) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop 3)
  refine ⟨κ, hκ, max (max rmin (2 ^ 2048)) N, ?_⟩
  intro G hr
  have hrk : (connectByHub G).cycleRank = G.cycleRank := cycleRank_connectByHub G
  have hra : rmin ≤ G.cycleRank :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hr
  have hrb : 2 ^ 2048 ≤ G.cycleRank :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hr
  have hrc : N ≤ G.cycleRank := (le_max_right _ _).trans hr
  have hb := connected_bound κ₀ hκ₀ rmin hmin (connectByHub G) (connectByHub_connected G)
    (by rw [hrk]; exact hra) (by rw [hrk]; exact hrb)
  rw [hrk] at hb
  have hle : (cycleCount G : ℝ) ≤ (cycleCount (connectByHub G) : ℝ) := by
    exact_mod_cast cycleCount_le_connectByHub G
  have hr1 : (1 : ℝ) ≤ (G.cycleRank : ℝ) := by
    have h : 1 ≤ G.cycleRank := le_trans (Nat.one_le_two_pow) hrb
    exact_mod_cast h
  have hr0 : (0 : ℝ) < (G.cycleRank : ℝ) := by linarith
  have h3 : (3 : ℝ) ≤ (G.cycleRank : ℝ) ^ κ := hN _ hrc
  -- the three error terms
  have e1 : (G.cycleRank : ℝ) ^ (-κ₀) ≤ (G.cycleRank : ℝ) ^ (-(2 * κ)) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have e2 : (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ)) ≤ (G.cycleRank : ℝ) ^ (-(2 * κ)) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have e3 : (G.cycleRank : ℝ) ^ (-(2 * κ)) =
      (G.cycleRank : ℝ) ^ (-κ) * (G.cycleRank : ℝ) ^ (-κ) := by
    rw [← Real.rpow_add hr0]
    congr 1
    ring
  have hpos : (0 : ℝ) < (G.cycleRank : ℝ) ^ (-κ) := Real.rpow_pos_of_pos hr0 _
  have e4 : (G.cycleRank : ℝ) ^ (-κ) ≤ 1 / 3 := by
    rw [Real.rpow_neg hr0.le, one_div]
    exact inv_anti₀ (by norm_num) h3
  have herr : (G.cycleRank : ℝ) ^ (-κ₀) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ)) ≤
      (G.cycleRank : ℝ) ^ (-κ) := by
    have h : (G.cycleRank : ℝ) ^ (-κ₀) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ)) ≤
        3 * ((G.cycleRank : ℝ) ^ (-κ) * (G.cycleRank : ℝ) ^ (-κ)) := by
      rw [← e3]
      linarith only [e1, e2]
    have h3p : 3 * (G.cycleRank : ℝ) ^ (-κ) ≤ 1 := by linarith only [e4]
    calc (G.cycleRank : ℝ) ^ (-κ₀) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ))
        ≤ 3 * ((G.cycleRank : ℝ) ^ (-κ) * (G.cycleRank : ℝ) ^ (-κ)) := h
      _ = (3 * (G.cycleRank : ℝ) ^ (-κ)) * (G.cycleRank : ℝ) ^ (-κ) := by ring
      _ ≤ 1 * (G.cycleRank : ℝ) ^ (-κ) := mul_le_mul_of_nonneg_right h3p hpos.le
      _ = (G.cycleRank : ℝ) ^ (-κ) := one_mul _
  have hpow : (0 : ℝ) < (2 : ℝ) ^ G.cycleRank := by positivity
  calc (cycleCount G : ℝ)
      ≤ (cycleCount (connectByHub G) : ℝ) := hle
    _ ≤ (1 / 2 + (G.cycleRank : ℝ) ^ (-κ₀) + 2 * (G.cycleRank : ℝ) ^ (-(1 / 100 : ℝ))) *
          2 ^ G.cycleRank := hb
    _ ≤ (1 / 2 + (G.cycleRank : ℝ) ^ (-κ)) * 2 ^ G.cycleRank := by
      apply mul_le_mul_of_nonneg_right _ hpow.le
      linarith only [herr]

end Erdos1016.PolynomialBound

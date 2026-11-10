import Erdos1016.CycleCount.ConnectedBound
import Erdos1016.Graph.ConnectedCoverage
import Erdos1016.Extremal.Recurrence.WitnessReduction

set_option autoImplicit false

/-!
# The cycle-count bound

A finite simple graph of large cycle rank `r` has at most
`(1/2 + 21 / log₂ log₂ log₂ r) * 2^r` cycles. The proof applies the forest
estimate to a chord extension with about `log₂ log₂ r` triangles. The result
is first proved for connected graphs. The hub extension then removes the
connectivity assumption.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.CycleCount
open PhysicalGraph ShortProof

/-- The number of cycles of a finite simple graph. -/
def cycleCount (G : PhysicalGraph) : ℕ := Fintype.card G.CycleWord

/-- Connecting the components by a hub does not lose a cycle. -/
theorem cycleCount_le_connectByHub (G : PhysicalGraph) :
    cycleCount G ≤ cycleCount (connectByHub G) := by
  apply Fintype.card_le_of_injective (liftHubCycleWord G)
  intro c c' h
  apply Subtype.ext
  funext e
  have h' := congrArg
    (fun z : (connectByHub G).CycleWord => z.1 (hubOldEdgeEmbedding G e)) h
  simpa using h'

/-! ### Numerical lemmas -/

theorem hundred_mul_le_two_pow : ∀ k : ℕ, 11 ≤ k → 100 * (k + 1) ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

theorem sq_le_two_pow : ∀ s : ℕ, 4 ≤ s → s ^ 2 ≤ 2 ^ s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have h2 : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    nlinarith

theorem logb_lt_natCast {x : ℝ} {n : ℕ} (hx : 0 < x) (hxn : x < n) :
    Real.logb 2 x < n := by
  rw [Real.logb_lt_iff_lt_rpow one_lt_two hx, Real.rpow_natCast]
  have h : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  exact hxn.trans_le h

theorem natCast_le_logb {x : ℝ} {k : ℕ} (hk : (2 : ℝ) ^ k ≤ x) :
    (k : ℝ) ≤ Real.logb 2 x := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) hk
  rw [Real.le_logb_iff_rpow_le one_lt_two hx, Real.rpow_natCast]
  exact hk

/-- Lower bounds for the three iterated logarithms of a large number. -/
theorem iterated_log_lower {ρ : ℝ} (hρ : (2 : ℝ) ^ 2048 ≤ ρ) :
    (2048 : ℝ) ≤ Real.logb 2 ρ ∧ (11 : ℝ) ≤ Real.logb 2 (Real.logb 2 ρ) ∧
      (3 : ℝ) ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 ρ)) := by
  have h1 : ((2048 : ℕ) : ℝ) ≤ Real.logb 2 ρ := natCast_le_logb hρ
  have h1' : (2048 : ℝ) ≤ Real.logb 2 ρ := by exact_mod_cast h1
  have e11 : (2 : ℝ) ^ 11 = 2048 := by norm_num
  have h2 : ((11 : ℕ) : ℝ) ≤ Real.logb 2 (Real.logb 2 ρ) :=
    natCast_le_logb (by rw [e11]; exact h1')
  have h2' : (11 : ℝ) ≤ Real.logb 2 (Real.logb 2 ρ) := by exact_mod_cast h2
  have e3 : (2 : ℝ) ^ 3 = 8 := by norm_num
  have h3 : ((3 : ℕ) : ℝ) ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 ρ)) :=
    natCast_le_logb (by rw [e3]; linarith)
  exact ⟨h1', h2', by exact_mod_cast h3⟩

/-- The triple logarithm is positive and monotone on large ranks. -/
theorem tripleLog_mono {r R : ℕ} (hr : 2 ^ 2048 ≤ r) (hrR : r ≤ R) :
    0 < tripleLog r ∧ tripleLog r ≤ tripleLog R := by
  have hrρ : (2 : ℝ) ^ 2048 ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨a1, a2, a3⟩ := iterated_log_lower hrρ
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrρ
  have hrR' : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have m1 : Real.logb 2 r ≤ Real.logb 2 R :=
    Real.logb_le_logb_of_le one_lt_two hr0 hrR'
  have m2 : Real.logb 2 (Real.logb 2 r) ≤ Real.logb 2 (Real.logb 2 R) :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) m1
  have m3 : Real.logb 2 (Real.logb 2 (Real.logb 2 r)) ≤
      Real.logb 2 (Real.logb 2 (Real.logb 2 R)) :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) m2
  constructor
  · unfold tripleLog
    linarith
  · unfold tripleLog
    exact m3

set_option exponentiation.threshold 2048 in
/-- The number of triangles used at rank `r`, with the inequalities it needs. -/
theorem witness_parameters {r : ℕ} (hr : 2 ^ 2048 ≤ r) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ r ∧ (3 * t) ^ 2 ≤ r ∧
      (100 : ℝ) * (t : ℝ) ≤ Real.logb 2 r ∧ tripleLog r ≤ (2 : ℝ) ^ t := by
  have hr0 : r ≠ 0 := by
    have h : 0 < 2 ^ 2048 := by positivity
    omega
  have hs_le : 2 ^ Nat.log 2 r ≤ r := Nat.pow_log_le_self 2 hr0
  have hs_lt : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
  have hs2048 : 2048 ≤ Nat.log 2 r := (Nat.pow_le_iff_le_log Nat.one_lt_two hr0).1 hr
  generalize Nat.log 2 r = s at hs_le hs_lt hs2048
  have hs0 : s ≠ 0 := by omega
  have hk_le : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 hs0
  have hk_lt : s < 2 ^ (Nat.log 2 s + 1) := Nat.lt_pow_succ_log_self (by norm_num) s
  have hk11 : 11 ≤ Nat.log 2 s :=
    (Nat.pow_le_iff_le_log (by norm_num) hs0).1 (by norm_num; omega)
  generalize Nat.log 2 s = k at hk_le hk_lt hk11
  have h100 : 100 * (k + 1) ≤ s := (hundred_mul_le_two_pow k hk11).trans hk_le
  have hss : s < 2 ^ s := Nat.lt_two_pow_self
  refine ⟨k + 1, by omega, by omega, ?_, ?_, ?_⟩
  · have h1 : 3 * (k + 1) ≤ s := by omega
    have h2 : (3 * (k + 1)) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : s ^ 2 ≤ 2 ^ s := sq_le_two_pow s (by omega)
    omega
  · have hlog : (s : ℝ) ≤ Real.logb 2 r := natCast_le_logb (by exact_mod_cast hs_le)
    have h100' : ((100 * (k + 1) : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast h100
    push_cast at h100' ⊢
    linarith
  · have hrρ : (2 : ℝ) ^ 2048 ≤ (r : ℝ) := by exact_mod_cast hr
    obtain ⟨a1, a2, a3⟩ := iterated_log_lower hrρ
    have hr0' : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrρ
    have b1 : Real.logb 2 r < ((s + 1 : ℕ) : ℝ) := by
      rw [Real.logb_lt_iff_lt_rpow one_lt_two hr0', Real.rpow_natCast]
      exact_mod_cast hs_lt
    have b2 : Real.logb 2 (Real.logb 2 r) < ((s + 1 : ℕ) : ℝ) :=
      logb_lt_natCast (by linarith) b1
    have b3 : Real.logb 2 (Real.logb 2 (Real.logb 2 r)) < ((s + 1 : ℕ) : ℝ) :=
      logb_lt_natCast (by linarith) b2
    have b4 : ((s + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast (show s + 1 ≤ 2 ^ (k + 1) by omega)
    unfold tripleLog
    linarith

/-! ### The bound -/

/-- The cycle-count bound for all finite simple graphs of large cycle rank. -/
def CycleCountBound : Prop :=
  ∃ r₁ : ℕ, ∀ G : PhysicalGraph, r₁ ≤ G.cycleRank →
    (cycleCount G : ℝ) ≤ (1 / 2 + 21 / tripleLog G.cycleRank) * 2 ^ G.cycleRank

/-- The bound for a connected graph, from the forest estimate above `rmin`. -/
theorem connected_bound (rmin : ℕ)
    (hmin : ∀ (G : PhysicalGraph), G.IsConnected → rmin ≤ G.cycleRank →
      ∀ F : Finset G.CycleWord, F.Nonempty →
        (witnessSupportEdges G F).card ^ 2 ≤ G.cycleRank →
        100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
          Real.logb 2 (G.cycleRank : ℝ) →
        outsideForestProbability G (witnessSupportEdges G F) ≤
          (1 / 2 : ℝ) + 20 / tripleLog G.cycleRank)
    (G : PhysicalGraph) (hG : G.IsConnected) (hr1 : rmin ≤ G.cycleRank)
    (hr2 : 2 ^ 2048 ≤ G.cycleRank) :
    (cycleCount G : ℝ) ≤ (1 / 2 + 21 / tripleLog G.cycleRank) * 2 ^ G.cycleRank := by
  obtain ⟨t, ht1, htr, ht9, ht100, htl⟩ := witness_parameters hr2
  obtain ⟨hpos, -⟩ := tripleLog_mono hr2 le_rfl
  have hr0 : (0 : ℝ) < (G.cycleRank : ℝ) := by
    have h : 0 < G.cycleRank := lt_of_lt_of_le (by positivity) hr2
    exact_mod_cast h
  have hB : ∀ (H : PhysicalGraph) (F : Finset H.CycleWord), H.IsConnected →
      G.cycleRank ≤ H.cycleRank → F.Nonempty → F.card ≤ t →
      (∀ T ∈ F, H.wordLength T.1 = 3) →
      outsideForestProbability H (witnessSupportEdges H F) ≤
        1 / 2 + 20 / tripleLog G.cycleRank := by
    intro H F hH hrank hne hcard h3
    obtain ⟨-, hmono⟩ := tripleLog_mono hr2 hrank
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
        Real.logb_le_logb_of_le one_lt_two hr0 (by exact_mod_cast hrank)
      linarith
    have hest := hmin H hH (hr1.trans hrank) F hne hW2 hcomp
    have hdiv : 20 / tripleLog H.cycleRank ≤ 20 / tripleLog G.cycleRank :=
      div_le_div_of_nonneg_left (by norm_num) hpos hmono
    linarith
  have hmain := card_cycleWord_le G hG t htr ht1 _ hB
  have hpow : (2 : ℝ) ^ (G.cycleRank - t) ≤
      2 ^ G.cycleRank / tripleLog G.cycleRank := by
    rw [pow_sub₀ (2 : ℝ) (by norm_num) htr, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos htl) (by positivity)
  unfold cycleCount
  calc (Fintype.card G.CycleWord : ℝ)
      ≤ (1 / 2 + 20 / tripleLog G.cycleRank) * 2 ^ G.cycleRank +
          2 ^ (G.cycleRank - t) := hmain
    _ ≤ (1 / 2 + 20 / tripleLog G.cycleRank) * 2 ^ G.cycleRank +
          2 ^ G.cycleRank / tripleLog G.cycleRank := by linarith
    _ = (1 / 2 + 21 / tripleLog G.cycleRank) * 2 ^ G.cycleRank := by
      field_simp
      ring

/-- The forest estimate implies the cycle-count bound. -/
theorem cycleCountBound_of_forestEstimate (hforest : FewComponentForestEstimate) :
    CycleCountBound := by
  obtain ⟨rmin, hmin⟩ := hforest
  refine ⟨max rmin (2 ^ 2048), ?_⟩
  intro G hr
  have hrk : (connectByHub G).cycleRank = G.cycleRank := cycleRank_connectByHub G
  have hb := connected_bound rmin hmin (connectByHub G) (connectByHub_connected G)
    (by rw [hrk]; exact (le_max_left _ _).trans hr)
    (by rw [hrk]; exact (le_max_right _ _).trans hr)
  rw [hrk] at hb
  have hle : (cycleCount G : ℝ) ≤ (cycleCount (connectByHub G) : ℝ) := by
    exact_mod_cast cycleCount_le_connectByHub G
  exact hle.trans hb

end Erdos1016.CycleCount

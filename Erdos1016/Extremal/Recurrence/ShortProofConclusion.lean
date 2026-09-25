import Erdos1016.Extremal.Capacity.ActualRankTail
import Erdos1016.Extremal.Recurrence.LinearExponentialDecay
import Erdos1016.Extremal.InfimumLowerBound
import Erdos1016.Extremal.PancyclicGraphTransfer
import Erdos1016.Extremal.UpperBound

set_option autoImplicit false

/-!
# The shorter recurrence implies the pancyclic excess bounds

This final numerical deduction uses the supremum over actual graph ranks and
iterates the scale `R ↦ 2^(256*R)`. The graph estimate establishing the recurrence
is an explicit hypothesis. The upper bound is supplied independently by the
recursive shortcut construction.
-/

noncomputable section
namespace Erdos1016.ShortProof
open Erdos1016.Extremal

/-- Log-star decay of the actual-rank supremum controls each covered prefix. -/
theorem coverage_le_of_actual_rank_tail_decay (K : ℝ)
    (hdecay : ∀ r, actualRankTail r ≤ K / (2 : ℝ) ^ logStar r)
    (G : PhysicalGraph) {L : ℕ} (hL : G.InitialCoverage L) :
    (L : ℝ) ≤ 2 + K * ((2 : ℝ) ^ G.cycleRank /
      (2 : ℝ) ^ logStar G.cycleRank) := by
  have hpowR : 0 < (2 : ℝ) ^ G.cycleRank := by positivity
  have hpowS : 0 < (2 : ℝ) ^ logStar G.cycleRank := by positivity
  have hcap := (coverageDensity_le_actualRankTail G le_rfl hL).trans
    (hdecay G.cycleRank)
  have hmul := (div_le_div_iff₀ hpowR hpowS).1 hcap
  have hnumAux : (L : ℝ) - 2 ≤
      (K * (2 : ℝ) ^ G.cycleRank) / (2 : ℝ) ^ logStar G.cycleRank :=
    (le_div_iff₀ hpowS).2 (by
      simpa [coverageDensity, mul_comm, mul_left_comm, mul_assoc] using hmul)
  simpa [mul_div_assoc] using (show (L : ℝ) ≤
      2 + (K * (2 : ℝ) ^ G.cycleRank) / (2 : ℝ) ^ logStar G.cycleRank by linarith)

private theorem logStar_pow_two_succ_le (r : ℕ) :
    logStar (2 ^ (r + 1)) ≤ logStar r + 2 := by
  let s := logStar r
  have hrs : r ≤ expTower s := le_expTower_logStar r
  have hrplus : r + 1 ≤ 2 ^ r := succ_le_two_pow r
  have hlevels : r + 1 ≤ expTower (s + 1) := by
    calc
      r + 1 ≤ 2 ^ r := hrplus
      _ ≤ 2 ^ expTower s := Nat.pow_le_pow_right (by decide) hrs
      _ = expTower (s + 1) := by simp [expTower]
  have hpow : 2 ^ (r + 1) ≤ expTower (s + 2) := by
    calc
      2 ^ (r + 1) ≤ 2 ^ expTower (s + 1) := Nat.pow_le_pow_right (by decide) hlevels
      _ = expTower (s + 2) := by simp [expTower, Nat.add_assoc]
  calc
    logStar (2 ^ (r + 1)) ≤ s + 2 := logStar_min_le hpow
    _ = logStar r + 2 := rfl

/-- Decay of actual-rank coverage gives the lower bound for a physical graph. -/
theorem pancyclic_excess_lower_of_actual_rank_tail_decay
    (K : ℝ) (hK : 0 < K)
    (hdecay : ∀ r, actualRankTail r ≤ K / (2 : ℝ) ^ logStar r)
    (G : PhysicalGraph) (hp : IsPancyclic G) :
    Real.logb 2 (G.vertexCount : ℝ) + (logStar G.vertexCount : ℝ) -
        (Real.logb 2 (K + 2) + 3) ≤ edgeExcess G := by
  let r := G.cycleRank
  let s := logStar r
  have hI := coverage_le_of_actual_rank_tail_decay K hdecay G hp.2.2
  have hsle : s ≤ r := logStar_min_le (le_expTower r)
  have hpowS : 0 < (2 : ℝ) ^ s := by positivity
  have hpowR : 0 < (2 : ℝ) ^ r := by positivity
  have hpowmono : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide) hsle)
  have hratio_one : 1 ≤ (2 : ℝ) ^ r / (2 : ℝ) ^ s :=
    (le_div_iff₀ hpowS).2 (by simpa using hpowmono)
  have hsize : (G.vertexCount : ℝ) ≤
      (K + 2) * ((2 : ℝ) ^ r / (2 : ℝ) ^ s) := by
    calc
      (G.vertexCount : ℝ) ≤ 2 + K * ((2 : ℝ) ^ r / (2 : ℝ) ^ s) := hI
      _ ≤ (K + 2) * ((2 : ℝ) ^ r / (2 : ℝ) ^ s) := by
        nlinarith [mul_le_mul_of_nonneg_left hratio_one (le_of_lt hK)]
  have hnpos : 0 < (G.vertexCount : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hp.2.1)
  have hCpos : 0 < K + 2 := by linarith
  have hratio_pos : 0 < (2 : ℝ) ^ r / (2 : ℝ) ^ s := div_pos hpowR hpowS
  have hlogN := Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ)) hnpos hsize
  have hlogRatio : Real.logb 2 ((2 : ℝ) ^ r / (2 : ℝ) ^ s) =
      (r : ℝ) - (s : ℝ) := by
    rw [Real.logb_div hpowR.ne' hpowS.ne', Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  have hlogBound : Real.logb 2 (G.vertexCount : ℝ) ≤
      Real.logb 2 (K + 2) + (r : ℝ) - (s : ℝ) := by
    calc
      _ ≤ Real.logb 2 ((K + 2) * ((2 : ℝ) ^ r / (2 : ℝ) ^ s)) := hlogN
      _ = Real.logb 2 (K + 2) +
          Real.logb 2 ((2 : ℝ) ^ r / (2 : ℝ) ^ s) := by
        rw [Real.logb_mul hCpos.ne' hratio_pos.ne']
      _ = _ := by rw [hlogRatio]; ring
  have hcapacityUpper : G.vertexCount ≤ 2 ^ (r + 1) := by
    have hpow : 2 ^ r + 1 ≤ 2 ^ (r + 1) := by
      rw [pow_succ]
      have hbase : 1 ≤ 2 ^ r := Nat.succ_le_of_lt (pow_pos (by decide) r)
      omega
    exact (G.coverage_bound hp.2.2).trans hpow
  have hlogstarN : logStar G.vertexCount ≤ s + 2 := by
    exact (logStar_mono hcapacityUpper).trans (logStar_pow_two_succ_le r)
  have hlogstarN_real : (logStar G.vertexCount : ℝ) ≤ (s : ℝ) + 2 := by
    exact_mod_cast hlogstarN
  have heuler := rank_real_eq_excess_add_one G hp.1
  dsimp [r, s] at hlogBound hlogstarN_real heuler ⊢
  linarith


open Erdos1016.Problem1016

/-- A pancyclic community graph has the lower bound supplied by the physical
capacity estimate, expressed in the community excess convention. -/
private theorem community_excess_lower_of_actual_rank_tail_decay
    (K : ℝ) (hK : 0 < K)
    (hdecay : ∀ r, actualRankTail r ≤ K / (2 : ℝ) ^ logStar r)
    {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPancyclic G) :
    Real.logb 2 (n : ℝ) + (logStar n : ℝ) -
        (Real.logb 2 (K + 2) + 3) ≤ (excess n G : ℝ) := by
  let H := physicalOfSimpleGraph G
  have hp : Extremal.IsPancyclic H := final_isPancyclic_of_isPancyclic G hn hG
  have hlow := pancyclic_excess_lower_of_actual_rank_tail_decay K hK hdecay H hp
  have hconnG : G.Connected := by
    have hconnH : H.IsConnected := hp.1
    change H.toSimpleGraph.Connected at hconnH
    simpa [H, physicalOfSimpleGraph_toSimpleGraph] using hconnH
  have hrank := physicalOfSimpleGraph_rank_eq_excess_add_one G
    hconnG
    hn hG
  have hrankR := congrArg (fun x : ℕ => (x : ℝ)) hrank
  push_cast at hrankR
  have heuler := rank_real_eq_excess_add_one H hp.1
  have hexcess : edgeExcess H = (excess n G : ℝ) := by
    linarith [hrankR, heuler]
  simpa [H, physicalOfSimpleGraph_vertexCount, hexcess] using hlow

/-- Actual-rank log-star decay, together with the independent construction,
gives both bounds in the problem's statement. -/
theorem mainTheorem_of_actual_rank_tail_decay
    (K : ℝ) (hK : 0 < K)
    (hdecay : ∀ r, actualRankTail r ≤ K / (2 : ℝ) ^ logStar r) :
    Problem1016.MainTheorem := by
  refine ⟨Real.logb 2 (K + 2) + 3, 1, ?_⟩
  intro n hn
  constructor
  · apply real_lower_bound_of_candidate_graphs n _ (candidateExcesses_nonempty n)
    intro G hG
    exact community_excess_lower_of_actual_rank_tail_decay K hK hdecay hn G hG
  · exact upper_bound n hn

/-- The exact near-halving recurrence of the shorter proof suffices for the
full statement. Its graph-theoretic derivation remains an explicit premise. -/
theorem mainTheorem_of_linear_exponential_recurrence (Rmin : ℕ)
    (hrec : ∀ R, Rmin ≤ R →
      actualRankTail (2 ^ (256 * R)) ≤
        ((1 / 2 : ℝ) + 20 / LinearExponentialDecay.doubleLog R) * actualRankTail R +
          (2 : ℝ) ^ (2 - (R : ℝ))) :
    Problem1016.MainTheorem := by
  obtain ⟨K, hK, hdecay⟩ := LinearExponentialDecay.recurrence_logStar_bound Rmin
    actualRankTail actualRankTail_bounds actualRankTail_antitone hrec
  exact mainTheorem_of_actual_rank_tail_decay K hK hdecay

end Erdos1016.ShortProof

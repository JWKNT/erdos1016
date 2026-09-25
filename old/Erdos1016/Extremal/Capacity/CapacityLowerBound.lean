import Erdos1016.Extremal.Capacity.Tail

set_option autoImplicit false

/-!
# Turning log-star capacity decay into the graph lower bound

This module isolates the final numerical deduction after the graph recurrence
has been proved. It is conditional only on the actual tail-capacity decay
bound, not on an unrelated extremal realization.
-/

noncomputable section
namespace Erdos1016.Extremal

private lemma initialCapacityExcess_le_tailCapacity (r : ℕ) :
    initialCapacityExcess r ≤ tailCapacity r := by
  unfold tailCapacity
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro x ⟨q, _, rfl⟩
    exact initialCapacityExcess_le_one q
  · exact ⟨r, le_rfl, rfl⟩

theorem initialCapacity_le_of_tail_decay (K : ℝ)
    (hdecay : ∀ r, tailCapacity r ≤ K / (2 : ℝ) ^ logStar r)
    (r : ℕ) :
    (initialCapacity r : ℝ) ≤
      2 + K * ((2 : ℝ) ^ r / (2 : ℝ) ^ logStar r) := by
  have hs : logStar r ≤ r := logStar_min_le (le_expTower r)
  have hpowR : 0 < (2 : ℝ) ^ r := by positivity
  have hpowS : 0 < (2 : ℝ) ^ logStar r := by positivity
  have hcap := (initialCapacityExcess_le_tailCapacity r).trans (hdecay r)
  have hmul := (div_le_div_iff₀ hpowR hpowS).1 hcap
  have hnumAux : ((initialCapacity r : ℝ) - 2) ≤
      (K * (2 : ℝ) ^ r) / (2 : ℝ) ^ logStar r :=
    (le_div_iff₀ hpowS).2 (by
      simpa [initialCapacityExcess, mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hnum : ((initialCapacity r : ℝ) - 2) ≤
      K * ((2 : ℝ) ^ r / (2 : ℝ) ^ logStar r) := by
    simpa [mul_div_assoc] using hnumAux
  have hcast : (2 : ℝ) ≤ (initialCapacity r : ℝ) := by
    exact_mod_cast initialCapacity_two_le r
  linarith

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

/-- A tail log-star estimate gives the desired coefficient-one lower bound
for every connected pancyclic physical graph. The only analytic premise is
the capacity estimate produced by the paper's near-halving recurrence. -/
theorem pancyclic_excess_lower_of_tail_decay
    (K : ℝ) (hK : 0 < K)
    (hdecay : ∀ r, tailCapacity r ≤ K / (2 : ℝ) ^ logStar r)
    (G : PhysicalGraph) (hp : IsPancyclic G) :
    Real.logb 2 (G.vertexCount : ℝ) + (logStar G.vertexCount : ℝ) -
        (Real.logb 2 (K + 2) + 3) ≤ edgeExcess G := by
  let r := G.cycleRank
  let s := logStar r
  have hcover := coverage_le_initialCapacity G (le_rfl) hp.2.2
  have hnI : (G.vertexCount : ℝ) ≤ (initialCapacity r : ℝ) := by
    exact_mod_cast hcover
  have hI := initialCapacity_le_of_tail_decay K hdecay r
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
      (G.vertexCount : ℝ) ≤ (initialCapacity r : ℝ) := hnI
      _ ≤ 2 + K * ((2 : ℝ) ^ r / (2 : ℝ) ^ s) := hI
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
    exact (hcover.trans (initialCapacity_le r)).trans hpow
  have hlogstarN : logStar G.vertexCount ≤ s + 2 := by
    exact (logStar_mono hcapacityUpper).trans (logStar_pow_two_succ_le r)
  have hlogstarN_real : (logStar G.vertexCount : ℝ) ≤ (s : ℝ) + 2 := by
    exact_mod_cast hlogstarN
  have heuler := rank_real_eq_excess_add_one G hp.1
  dsimp [r, s] at hlogBound hlogstarN_real heuler ⊢
  linarith



end Erdos1016.Extremal

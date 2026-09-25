import Erdos1016.Extremal.Witness.WeightedExtraction
import Erdos1016.Extremal.Capacity.ActualRankTail

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.ShortProof
open PhysicalGraph

/-- A least-missing cycle is charged against the actual-rank tail once its
current support has rank at least `R`. -/
def witnessRankCharge (R s : ℕ) : ℝ :=
  if s < R then (2 : ℝ) ^ s + 2
  else actualRankTail R * (2 : ℝ) ^ s + 3

theorem witnessRankCharge_nonneg (R s : ℕ) : 0 ≤ witnessRankCharge R s := by
  have h := (actualRankTail_bounds R).1
  unfold witnessRankCharge
  split_ifs <;> positivity

theorem least_missing_length_le_charge (G : PhysicalGraph) (R : ℕ)
    (E : Finset G.Edge) (C : G.CycleWord)
    (hp : SupportedPrefix G E (G.wordLength C.1 - 1)) :
    (G.wordLength C.1 : ℝ) ≤ witnessRankCharge R (G.restrictedCycleRank E) := by
  have hcov := initialCoverage_of_prefix G E _ hp
  unfold witnessRankCharge
  split_ifs with hs
  · have hb := (G.restrictPhysical E).coverage_bound hcov
    rw [G.restrictPhysical_cycleRank] at hb
    have hb' : G.wordLength C.1 ≤ 2 ^ G.restrictedCycleRank E + 2 := by omega
    exact_mod_cast hb'
  · have hs' : R ≤ (G.restrictPhysical E).cycleRank := by
      rw [G.restrictPhysical_cycleRank]
      omega
    have hb := coverage_le_actualRankTail_mul (G.restrictPhysical E) hs' hcov
    rw [G.restrictPhysical_cycleRank] at hb
    have hlen : (G.wordLength C.1 : ℝ) ≤ ((G.wordLength C.1 - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show G.wordLength C.1 ≤ G.wordLength C.1 - 1 + 1 by omega)
    linarith

private theorem real_two_pow_sum_range (n : ℕ) :
    (∑ s ∈ Finset.range n, (2 : ℝ) ^ s) = (2 : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem witnessRankCharge_sum (R : ℕ) :
    (∑ s ∈ Finset.range (2 * R), witnessRankCharge R s) =
      actualRankTail R * ((2 : ℝ) ^ (2 * R) - (2 : ℝ) ^ R) +
        (2 : ℝ) ^ R - 1 + 5 * R := by
  have hRR : R ≤ 2 * R := by omega
  have hlow : (∑ s ∈ Finset.range R, witnessRankCharge R s) =
      (2 : ℝ) ^ R - 1 + 2 * R := by
    have he : ∀ s ∈ Finset.range R, witnessRankCharge R s = (2 : ℝ) ^ s + 2 := by
      intro s hs
      simp [witnessRankCharge, Finset.mem_range.mp hs]
    rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, real_two_pow_sum_range]
    simp
    ring
  have hhigh : (∑ s ∈ Finset.Ico R (2 * R), witnessRankCharge R s) =
      actualRankTail R * ((2 : ℝ) ^ (2 * R) - (2 : ℝ) ^ R) + 3 * R := by
    have he : ∀ s ∈ Finset.Ico R (2 * R), witnessRankCharge R s =
        actualRankTail R * (2 : ℝ) ^ s + 3 := by
      intro s hs
      simp [witnessRankCharge, not_lt.mpr (Finset.mem_Ico.mp hs).1]
    rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_Ico_eq_sub (fun s : ℕ => (2 : ℝ) ^ s) hRR,
      real_two_pow_sum_range, real_two_pow_sum_range]
    simp [Nat.cast_sub hRR]
    ring
  rw [← Finset.sum_range_add_sum_Ico (witnessRankCharge R) hRR, hlow, hhigh]
  ring

theorem sum_initial_cost_add_one_le (K : ℕ) :
    (∑ s ∈ Finset.range K, (initialCapacity s + 1)) + 1 ≤ 2 ^ K + 2 * K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Nat.pow_succ]
    have h := initialCapacity_le K
    omega

private theorem four_mul_le_two_pow_double (R : ℕ) (hR : 1 ≤ R) :
    4 * R ≤ 2 ^ (2 * R) := by
  induction R, hR using Nat.le_induction with
  | base => norm_num
  | @succ R hR ih =>
    have he : 2 * (R + 1) = 2 * R + 2 := by omega
    rw [he, pow_add]
    norm_num
    omega

private theorem six_mul_le_two_pow (R : ℕ) (hR : 5 ≤ R) : 6 * R ≤ 2 ^ R := by
  induction R, hR using Nat.le_induction with
  | base => norm_num
  | @succ R hR ih => rw [Nat.pow_succ]; omega

/-- The witness is an actual union of at most `2R` cycles, stopped at the first
rank crossing. The two edge estimates hold for this same union. -/
theorem exists_budgeted_witness (G : PhysicalGraph) (R : ℕ) (hR : 5 ≤ R)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    ∃ F : Finset G.CycleWord,
      F.Nonempty ∧ 2 * R ≤ G.restrictedCycleRank (witnessSupportEdges G F) ∧
      F.card ≤ 2 * R ∧ Nat.card (cycleUnionGraph G F).ConnectedComponent ≤ 2 * R ∧
      (witnessSupportEdges G F).card ≤ 2 ^ (3 * R) ∧
      ((witnessSupportEdges G F).card : ℝ) + 1 ≤
        actualRankTail R * (2 : ℝ) ^ (2 * R) + (2 : ℝ) ^ R + 5 * R ∧
      (((witnessSupportEdges G F).card : ℝ) + 1) /
        (2 : ℝ) ^ G.restrictedCycleRank (witnessSupportEdges G F) ≤
        actualRankTail R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
  obtain ⟨F, hr, hc, hcomp, hm, hmR⟩ := exists_weighted_few_cycle_witness G (2 * R)
    hcov (witnessRankCharge R) (witnessRankCharge_nonneg R)
    (fun E _ C hp => least_missing_length_le_charge G R E C hp)
  have hne : F.Nonempty := by
    by_contra h
    have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst F
    simp only [witnessSupportEdges, Finset.biUnion_empty, empty_restricted_rank] at hr
    omega
  have hcoarse : (witnessSupportEdges G F).card ≤ 2 ^ (3 * R) := by
    have hs := sum_initial_cost_add_one_le (2 * R)
    have h4 := four_mul_le_two_pow_double R (by omega)
    have hpow : 2 ^ (2 * R + 1) ≤ (2 : ℕ) ^ (3 * R) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_succ] at hpow
    omega
  have hfine : ((witnessSupportEdges G F).card : ℝ) + 1 ≤
      actualRankTail R * (2 : ℝ) ^ (2 * R) + (2 : ℝ) ^ R + 5 * R := by
    rw [witnessRankCharge_sum] at hmR
    have hprod := mul_nonneg (actualRankTail_bounds R).1 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) R)
    nlinarith
  refine ⟨F, hne, hr, hc, hcomp, hcoarse, hfine, ?_⟩
  have h6 : (6 : ℝ) * R ≤ (2 : ℝ) ^ R := by exact_mod_cast six_mul_le_two_pow R hR
  have hpow : (2 : ℝ) ^ (2 * R) ≤
      (2 : ℝ) ^ G.restrictedCycleRank (witnessSupportEdges G F) :=
    pow_le_pow_right₀ (by norm_num) hr
  have herr : (2 : ℝ) ^ (1 - (R : ℝ)) * (2 : ℝ) ^ (2 * R) =
      (2 : ℝ) ^ R * 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) (2 * R), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have he : (1 - (R : ℝ)) + (2 * R : ℕ) = (R : ℝ) + 1 := by push_cast; ring
    rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_one]
  have hnum : ((witnessSupportEdges G F).card : ℝ) + 1 ≤
      (actualRankTail R + (2 : ℝ) ^ (1 - (R : ℝ))) * (2 : ℝ) ^ (2 * R) := by
    rw [add_mul, herr]
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^
    G.restrictedCycleRank (witnessSupportEdges G F))).2
  exact hnum.trans (mul_le_mul_of_nonneg_left hpow
    (add_nonneg (actualRankTail_bounds R).1 (by positivity)))

end Erdos1016.ShortProof

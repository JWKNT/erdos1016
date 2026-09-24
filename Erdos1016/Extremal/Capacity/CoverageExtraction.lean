import Erdos1016.Extremal.Capacity.CycleWitnessSelection
import Erdos1016.Extremal.Capacity.LocalCapacityBound
import Erdos1016.Extremal.Capacity.WitnessAlpha

set_option autoImplicit false

/-!
# A coarse edge/rank extraction from initial coverage

Selecting one physical cycle at each length gives a literal support edge set.
This module records the resulting edge-count and rank bounds. They are weaker
than the rank-by-rank greedy budget needed for the finite alpha bridge.
-/

namespace Erdos1016.Proof.FiniteAlphaExtraction

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Extremal

private theorem real_two_pow_sum_range (n : ℕ) :
    (∑ s ∈ Finset.range n, (2 : ℝ) ^ s) = (2 : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring



/-- If a proposed greedy process assigns at most the current extremal
cycle-length cost to each rank below its terminal rank, its total edge budget
is bounded by the paper's tail-capacity expression. Skipped ranks are encoded
by assigning cost zero. The construction of this rank-indexed cost sequence
from successive least-missing cycles is a separate combinatorial obligation. -/
theorem rank_indexed_greedy_cost_sum_le
    (R p : ℕ) (φ : ℝ) (hR : 5 ≤ R) (hRp : R ≤ p)
    (hφ : ∀ s : ℕ, R ≤ s → initialCapacityExcess s ≤ φ)
    (cost : ℕ → ℕ)
    (hcost : ∀ s, s < p → cost s ≤ initialCapacity s + 1) :
    (((∑ s ∈ Finset.range p, cost s) + 1 : ℕ) : ℝ) ≤
      φ * (2 : ℝ) ^ p + (2 : ℝ) ^ R + 3 * p := by
  have hφnonneg : 0 ≤ φ := by
    have h := hφ R le_rfl
    have hnonneg := initialCapacityExcess_nonneg R
    linarith
  let b : ℕ → ℝ := fun s =>
    if s < R then (2 : ℝ) ^ s + 2 else φ * (2 : ℝ) ^ s + 3
  have hpoint (s : ℕ) (hs : s < p) : (cost s : ℝ) ≤ b s := by
    by_cases hsR : s < R
    · have hc := hcost s hs
      have hI := initialCapacity_le s
      have hcast : (cost s : ℝ) ≤ (initialCapacity s : ℝ) + 1 := by
        exact_mod_cast hc
      have hIcast : (initialCapacity s : ℝ) ≤ (2 : ℝ) ^ s + 1 := by
        exact_mod_cast hI
      simpa [b, hsR] using hcast.trans (by linarith :
        (initialCapacity s : ℝ) + 1 ≤ (2 : ℝ) ^ s + 2)
    · have hsR' : R ≤ s := by omega
      have hc := hcost s hs
      have hcast : (cost s : ℝ) ≤ (initialCapacity s : ℝ) + 1 := by
        exact_mod_cast hc
      have htail := hφ s hsR'
      have hden : 0 < (2 : ℝ) ^ s := by positivity
      have hnum : (initialCapacity s : ℝ) - 2 ≤ φ * (2 : ℝ) ^ s := by
        have h := (div_le_iff₀ hden).1 htail
        have hI : 2 ≤ initialCapacity s := initialCapacity_two_le s
        have hcastSub : ((initialCapacity s - 2 : ℕ) : ℝ) =
            (initialCapacity s : ℝ) - 2 := by
          rw [Nat.cast_sub hI]
          norm_num
        simpa [initialCapacityExcess, hcastSub] using h
      have hbound : (initialCapacity s : ℝ) + 1 ≤
          φ * (2 : ℝ) ^ s + 3 := by linarith
      simpa [b, hsR] using hcast.trans hbound
  have hsum : (∑ s ∈ Finset.range p, (cost s : ℝ)) ≤
      ∑ s ∈ Finset.range p, b s := by
    apply Finset.sum_le_sum
    intro s hs
    exact hpoint s (Finset.mem_range.mp hs)
  have hlow : (∑ s ∈ Finset.range R, b s) =
      (2 : ℝ) ^ R - 1 + 2 * R := by
    have hif : ∀ s ∈ Finset.range R, b s = (2 : ℝ) ^ s + 2 := by
      intro s hs
      simp [b, Finset.mem_range.mp hs]
    rw [Finset.sum_congr rfl hif, Finset.sum_add_distrib,
      real_two_pow_sum_range]
    simp
    push_cast
    ring
  have hhigh : (∑ s ∈ Finset.Ico R p, b s) =
      φ * ((2 : ℝ) ^ p - (2 : ℝ) ^ R) + 3 * (p - R) := by
    have hpow : (∑ s ∈ Finset.Ico R p, (2 : ℝ) ^ s) =
        (2 : ℝ) ^ p - (2 : ℝ) ^ R := by
      rw [Finset.sum_Ico_eq_sub (fun s : ℕ => (2 : ℝ) ^ s) hRp,
        real_two_pow_sum_range, real_two_pow_sum_range]
      ring
    have hconst : (∑ _s ∈ Finset.Ico R p, (3 : ℝ)) = 3 * (p - R) := by
      simp [Finset.sum_const, Nat.cast_sub hRp, mul_comm]
    have hif : ∀ s ∈ Finset.Ico R p,
        (if s < R then (2 : ℝ) ^ s + 2 else φ * (2 : ℝ) ^ s + 3) =
          φ * (2 : ℝ) ^ s + 3 := by
      intro s hs
      have hsR' := (Finset.mem_Ico.mp hs).1
      simp [not_lt.mpr hsR']
    have hsumB : (∑ s ∈ Finset.Ico R p, b s) =
        ∑ s ∈ Finset.Ico R p, (φ * (2 : ℝ) ^ s + 3) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hif s hs
    rw [hsumB]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hpow, hconst]
  have hallSum : (∑ s ∈ Finset.range p, b s) =
      (∑ s ∈ Finset.range R, b s) +
        (∑ s ∈ Finset.Ico R p, b s) := by
    symm
    exact Finset.sum_range_add_sum_Ico b hRp
  have hcastSum :
      (((∑ s ∈ Finset.range p, cost s : ℕ) : ℝ)) =
        ∑ s ∈ Finset.range p, (cost s : ℝ) := by simp
  rw [hallSum, hlow, hhigh] at hsum
  have hsum' := hsum
  have hpowR : 0 ≤ (2 : ℝ) ^ R := by positivity
  have hpowP : 0 ≤ (2 : ℝ) ^ p := by positivity
  have hmain :
      (((∑ s ∈ Finset.range p, cost s : ℕ) : ℝ) + 1) ≤
        φ * (2 : ℝ) ^ p + (2 : ℝ) ^ R + 3 * p := by
    rw [hcastSum]
    nlinarith [hsum', hφnonneg, hpowR, hpowP]
  simpa using hmain



end Erdos1016.Proof.FiniteAlphaExtraction

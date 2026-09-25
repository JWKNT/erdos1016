import Erdos1016.Extremal.Witness.CapacityBudget
import Erdos1016.Extremal.Capacity.WitnessOutsideBound
import Erdos1016.Extremal.Recurrence.ShortProofConclusion
import Erdos1016.Graph.ConnectedCoverage

set_option autoImplicit false
noncomputable section

namespace Erdos1016.ShortProof
open PhysicalGraph
open Erdos1016.Extremal

/-- The logarithm appearing in the forest estimate. -/
def tripleLog (r : ℕ) : ℝ := Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))

/-- The remaining graph theorem, stated for actual cycle unions and the actual
uniform cycle-space forest event. This is a proposition, not an axiom. -/
def FewComponentForestEstimate : Prop :=
  ∃ rmin : ℕ, ∀ (G : PhysicalGraph), G.IsConnected → rmin ≤ G.cycleRank →
    ∀ F : Finset G.CycleWord, F.Nonempty →
      (witnessSupportEdges G F).card ^ 2 ≤ G.cycleRank →
      100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
        Real.logb 2 (G.cycleRank : ℝ) →
      outsideForestProbability G (witnessSupportEdges G F) ≤
        (1 / 2 : ℝ) + 20 / tripleLog G.cycleRank

private theorem error_product (R : ℕ) :
    (2 : ℝ) ^ (1 - (R : ℝ)) * (2 : ℝ) ^ R = 2 := by
  rw [← Real.rpow_natCast (2 : ℝ) R, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : (1 - (R : ℝ)) + R = 1 := by ring
  rw [he, Real.rpow_one]

private theorem double_error (R : ℕ) :
    2 * (2 : ℝ) ^ (1 - (R : ℝ)) = (2 : ℝ) ^ (2 - (R : ℝ)) := by
  conv_lhs => lhs; rw [← Real.rpow_one (2 : ℝ)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Only elementary numerical errors remain once the outside forest bound is
known for the actual greedy union. The probability is also at most one. -/
theorem coverageDensity_le_of_witness_forest_bound (G : PhysicalGraph)
    (R L : ℕ) (hR : 5 ≤ R) (hr : 4 * R ≤ G.cycleRank)
    (hL : G.InitialCoverage L) (a : ℝ)
    (hforest : ∀ F : Finset G.CycleWord, F.Nonempty →
      2 * R ≤ G.restrictedCycleRank (witnessSupportEdges G F) →
      Nat.card (cycleUnionGraph G F).ConnectedComponent ≤ 2 * R →
      (witnessSupportEdges G F).card ≤ 2 ^ (3 * R) →
      outsideForestProbability G (witnessSupportEdges G F) ≤ a)
    (ha : 0 ≤ a) :
    coverageDensity G L ≤ a * actualRankTail R + (2 : ℝ) ^ (2 - (R : ℝ)) := by
  by_cases hlarge : 2 ^ (2 * R) + 1 ≤ L
  · have hcov : G.InitialCoverage (2 ^ (2 * R) + 1) := by
      intro l hl
      apply hL
      have hl' := Finset.mem_Icc.mp hl
      exact Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.trans hlarge⟩
    obtain ⟨F, hne, ht, _, hc, hm, _, hnorm⟩ := exists_budgeted_witness G R hR hcov
    let E := witnessSupportEdges G F
    have hp := hforest F hne ht hc hm
    have hp01 := outsideForestProbability_bounds G E
    have hcount := coverageDensity_le_outsideForest G E hL
    have htR : R ≤ G.restrictedCycleRank E := by dsimp [E]; omega
    have hpowt : (2 : ℝ) ^ R ≤ (2 : ℝ) ^ G.restrictedCycleRank E :=
      pow_le_pow_right₀ (by norm_num) htR
    have hrest : 1 / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤ (2 : ℝ) ^ (1 - (R : ℝ)) := by
      have hfirst : 1 / (2 : ℝ) ^ G.restrictedCycleRank E ≤ 1 / (2 : ℝ) ^ R :=
        one_div_le_one_div_of_le (by positivity) hpowt
      have hmR : (E.card : ℝ) ≤ (2 : ℝ) ^ (3 * R) := by exact_mod_cast hm
      have hpowr : (2 : ℝ) ^ (4 * R) ≤ (2 : ℝ) ^ G.cycleRank :=
        pow_le_pow_right₀ (by norm_num) hr
      have hid : (2 : ℝ) ^ (3 * R) * (2 : ℝ) ^ R = (2 : ℝ) ^ (4 * R) := by
        rw [← pow_add]
        congr 1
        omega
      have hsecond : (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤ 1 / (2 : ℝ) ^ R := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hh := mul_le_mul_of_nonneg_right hmR
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) R)
        rw [hid] at hh
        simpa using hh.trans hpowr
      have he : 1 / (2 : ℝ) ^ R + 1 / (2 : ℝ) ^ R = (2 : ℝ) ^ (1 - (R : ℝ)) := by
        have hh := error_product R
        field_simp at ⊢
        linarith
      linarith
    have hmain : ((E.card : ℝ) + 1) / (2 : ℝ) ^ G.restrictedCycleRank E *
        outsideForestProbability G E ≤
        a * actualRankTail R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
      calc
        _ ≤ (actualRankTail R + (2 : ℝ) ^ (1 - (R : ℝ))) *
            outsideForestProbability G E := mul_le_mul_of_nonneg_right hnorm hp01.1
        _ = actualRankTail R * outsideForestProbability G E +
            (2 : ℝ) ^ (1 - (R : ℝ)) * outsideForestProbability G E := by ring
        _ ≤ actualRankTail R * a + (2 : ℝ) ^ (1 - (R : ℝ)) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hp (actualRankTail_bounds R).1)
            (mul_le_mul_of_nonneg_left hp01.2 (by positivity))
        _ = _ := by ring
    have hdouble := double_error R
    linarith
  · have hLsmall : L ≤ 2 ^ (2 * R) := by omega
    have hpow : (2 : ℝ) ^ (2 * R) ≤ (2 : ℝ) ^ G.cycleRank :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hr3 : 3 * R ≤ G.cycleRank := by omega
    have hpow3 : (2 : ℝ) ^ (3 * R) ≤ (2 : ℝ) ^ G.cycleRank :=
      pow_le_pow_right₀ (by norm_num) hr3
    have hsmall : coverageDensity G L ≤ 1 / (2 : ℝ) ^ R := by
      unfold coverageDensity
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hLc : (L : ℝ) ≤ (2 : ℝ) ^ (2 * R) := by exact_mod_cast hLsmall
      have hid : (2 : ℝ) ^ (2 * R) * (2 : ℝ) ^ R = (2 : ℝ) ^ (3 * R) := by
        rw [← pow_add]; congr 1; omega
      have hm := mul_le_mul_of_nonneg_right hLc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) R)
      rw [hid] at hm
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) R]
    have herr : 1 / (2 : ℝ) ^ R ≤ (2 : ℝ) ^ (1 - (R : ℝ)) := by
      apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ R)).2
      rw [error_product]
      norm_num
    have hnonneg := mul_nonneg ha (actualRankTail_bounds R).1
    have hdouble := double_error R
    have hpos : 0 ≤ (2 : ℝ) ^ (1 - (R : ℝ)) := by positivity
    linarith

theorem log_rank_ge_linear (R r : ℕ) (hr : 2 ^ (256 * R) ≤ r) :
    256 * (R : ℝ) ≤ Real.logb 2 (r : ℝ) := by
  have hpow : (2 : ℝ) ^ (256 * R) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num : (0 : ℝ) < 2) (256 * R)) hpow
  simpa [Real.logb_pow] using hlog

theorem doubleLog_pos (R : ℕ) (hR : 5 ≤ R) :
    0 < LinearExponentialDecay.doubleLog R := by
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) < R by exact_mod_cast (by omega : 2 < R))
  have h1 : 1 < Real.logb 2 (R : ℝ) := by simpa using hlog
  exact Real.logb_pos (by norm_num) h1

theorem doubleLog_le_tripleLog (R r : ℕ) (hR : 5 ≤ R)
    (hr : 2 ^ (256 * R) ≤ r) :
    LinearExponentialDecay.doubleLog R ≤ tripleLog r := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hlogR : 0 < Real.logb 2 (R : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (by omega : 1 < R))
  have hlog := log_rank_ge_linear R r hr
  have hRlog : (R : ℝ) ≤ Real.logb 2 (r : ℝ) := by linarith
  have hnext := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hRpos hRlog
  exact Real.logb_le_logb_of_le (by norm_num) hlogR hnext

/-- At the linear exponential scale, the extracted union meets both geometric
hypotheses of the forest estimate. -/
theorem budgeted_witness_fits_forest_estimate (G : PhysicalGraph) (R : ℕ)
    (hr : 2 ^ (256 * R) ≤ G.cycleRank) (F : Finset G.CycleWord)
    (hc : Nat.card (cycleUnionGraph G F).ConnectedComponent ≤ 2 * R)
    (hm : (witnessSupportEdges G F).card ≤ 2 ^ (3 * R)) :
    (witnessSupportEdges G F).card ^ 2 ≤ G.cycleRank ∧
      100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
        Real.logb 2 (G.cycleRank : ℝ) := by
  constructor
  · calc
      _ ≤ (2 ^ (3 * R)) ^ 2 := Nat.pow_le_pow_left hm _
      _ = 2 ^ (6 * R) := by rw [← pow_mul]; congr 1; omega
      _ ≤ 2 ^ (256 * R) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := hr
  · have hcR : (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤ 2 * R := by
      exact_mod_cast hc
    have hlog := log_rank_ge_linear R G.cycleRank hr
    have hRn : (0 : ℝ) ≤ R := by positivity
    linarith

/-- The exact recurrence is now reduced to the stated few-component forest
theorem. All witness construction, counting, connectedization and numerical
errors in this deduction are proved in Lean. -/
theorem recurrence_of_few_component_forest_estimate
    (hforest : FewComponentForestEstimate) :
    ∃ Rmin : ℕ, ∀ R, Rmin ≤ R →
      actualRankTail (2 ^ (256 * R)) ≤
        ((1 / 2 : ℝ) + 20 / LinearExponentialDecay.doubleLog R) * actualRankTail R +
          (2 : ℝ) ^ (2 - (R : ℝ)) := by
  obtain ⟨rmin, hforest⟩ := hforest
  refine ⟨max rmin 5, ?_⟩
  intro R hRmin
  have hR : 5 ≤ R := (Nat.le_max_right _ _).trans hRmin
  have hstart : rmin ≤ R := (Nat.le_max_left _ _).trans hRmin
  have hden := doubleLog_pos R hR
  have ha : 0 ≤ (1 / 2 : ℝ) + 20 / LinearExponentialDecay.doubleLog R := by positivity
  apply actualRankTail_le_of_connected (add_nonneg (mul_nonneg ha (actualRankTail_bounds R).1)
    (by positivity))
  intro G L hconn hr hL
  have hlin : 256 * R ≤ G.cycleRank :=
    (Nat.lt_two_pow_self (n := 256 * R)).le.trans hr
  apply coverageDensity_le_of_witness_forest_bound G R L hR (by omega) hL _ ?_ ha
  intro F hne _ hc hm
  have hgeom := budgeted_witness_fits_forest_estimate G R hr F hc hm
  have hb := hforest G hconn (by omega) F hne hgeom.1 hgeom.2
  have hlog := doubleLog_le_tripleLog R G.cycleRank hR hr
  exact hb.trans (add_le_add_left (div_le_div_of_nonneg_left (by norm_num) hden hlog) _)

/-- Conditional endpoint of the shorter route. Its single remaining premise
is the actual graph forest estimate, rather than the desired final theorem. -/
theorem mainTheorem_of_few_component_forest_estimate
    (hforest : FewComponentForestEstimate) : Problem1016.MainTheorem := by
  obtain ⟨Rmin, hrec⟩ := recurrence_of_few_component_forest_estimate hforest
  exact mainTheorem_of_linear_exponential_recurrence Rmin hrec

end Erdos1016.ShortProof

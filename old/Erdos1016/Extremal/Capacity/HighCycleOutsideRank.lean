import Erdos1016.Extremal.Capacity.GreedyExtraction

set_option autoImplicit false

/-!
# Recovering the outside rank in the high-cycle branch

The cycle-count alternative on the quartic scale forces the ambient cycle
rank to be within `R+1` of the scale parameter. The short canonical witness
uses at most `2^(4R)` edges, so the exact edge-partition rank identity then
forces at least `2R` rank outside that witness and in its common boundary.
-/

noncomputable section

namespace Erdos1016.Proof.HighCycleOutsideRank

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.FiniteGreedyStages
open Erdos1016.Proof.Capacity

/-- A triangle supplies a uniform positive lower bound on tail capacity. -/
theorem initialCapacity_ge_three (R : ℕ) (hR : 5 ≤ R) :
    3 ≤ initialCapacity R := by
  let K : SimpleGraph (Fin 3) := completeGraph (Fin 3)
  letI : Fintype K.edgeSet := Fintype.ofFinite _
  let H : PhysicalGraph := Problem1016.physicalOfSimpleGraph K
  have hPan : Problem1016.IsPancyclic K :=
    Problem1016.completeGraph_isPancyclic 3
  have hFinal : Extremal.IsPancyclic H :=
    Problem1016.final_isPancyclic_of_isPancyclic K (by norm_num) hPan
  have hcov : H.InitialCoverage 3 := by
    have h := hFinal.2.2
    simpa [PhysicalGraph.IsPancyclic, H] using h
  have hcard : Fintype.card K.edgeSet ≤ 3 := by
    have hcard' : Fintype.card K.edgeSet ≤ Nat.choose 3 2 := by
      rw [← SimpleGraph.edgeFinset_card]
      simpa [K] using
        (SimpleGraph.card_edgeFinset_le_card_choose_two (G := K))
    norm_num [Nat.choose] at hcard'
    exact hcard'
  have hrank : H.cycleRank ≤ 3 := by
    calc
      H.cycleRank ≤ H.edgeCount :=
        PhysicalGraph.cycleRank_le_edgeCount H
      _ = Fintype.card K.edgeSet := rfl
      _ ≤ 3 := hcard
  exact coverage_le_initialCapacity H (r := R) (by omega) hcov

/-- Every tail supremum at scale `R` is at least `2^-R`. -/
theorem inv_two_pow_le_tailCapacity (R : ℕ) (hR : 5 ≤ R) :
    1 / (2 : ℝ) ^ R ≤ tailCapacity R := by
  have hI := initialCapacity_ge_three R hR
  have hnat : 1 ≤ initialCapacity R - 2 := by omega
  have hnum : 1 ≤ (initialCapacity R : ℝ) - 2 := by
    have hcast : (1 : ℝ) ≤ ((initialCapacity R - 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_sub (by omega : 2 ≤ initialCapacity R)] using hcast
  have hExcess : 1 / (2 : ℝ) ^ R ≤ initialCapacityExcess R := by
    unfold initialCapacityExcess
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hbounded : BddAbove
      {x : ℝ | ∃ n : ℕ, R ≤ n ∧ x = initialCapacityExcess n} := by
    refine ⟨1, ?_⟩
    rintro x ⟨n, _, rfl⟩
    exact initialCapacityExcess_le_one n
  unfold tailCapacity
  exact hExcess.trans (le_csSup hbounded ⟨R, le_rfl, rfl⟩)

private theorem three_mul_le_two_pow (n : ℕ) (hn : 5 ≤ n) :
    3 * n ≤ 2 ^ n := by
  have h : ∀ m : ℕ, 3 * (m + 5) ≤ 2 ^ (m + 5) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        calc
          3 * (m + 6) ≤ 2 * (3 * (m + 5)) := by omega
          _ ≤ 2 * 2 ^ (m + 5) := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (m + 6) := by rw [pow_succ]; ring
  have hn' : n = (n - 5) + 5 := by omega
  rw [hn']
  exact h (n - 5)

/-- The normalized high-cycle witness count forces the realizing graph to
have cycle rank at least `r-(R+1)`. -/
theorem rank_ge_of_high_cycle_count
    (G : PhysicalGraph) (R r : ℕ) (hR : 5 ≤ R)
    (hcount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r) :
    r ≤ G.cycleRank + (R + 1) := by
  have hhalf : 1 / (2 : ℝ) ^ (R + 1) ≤ tailCapacity R / 2 := by
    have htail := inv_two_pow_le_tailCapacity R hR
    have hpow : (2 : ℝ) ^ (R + 1) = (2 : ℝ) ^ R * 2 := by
      rw [pow_succ]
    rw [hpow]
    calc
      1 / ((2 : ℝ) ^ R * 2) = (1 / (2 : ℝ) ^ R) / 2 := by ring
      _ ≤ tailCapacity R / 2 :=
        div_le_div_of_nonneg_right htail (by norm_num)
  have hprob := hhalf.trans hcount
  have hcardLower :
      (1 / (2 : ℝ) ^ (R + 1)) * (2 : ℝ) ^ r ≤
        (G.cycleLengths.card : ℝ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)).mp hprob
  have hpow : (2 : ℝ) ^ r ≤
      (G.cycleLengths.card : ℝ) * (2 : ℝ) ^ (R + 1) := by
    calc
      (2 : ℝ) ^ r =
          ((1 / (2 : ℝ) ^ (R + 1)) * (2 : ℝ) ^ r) *
            (2 : ℝ) ^ (R + 1) := by field_simp
      _ ≤ (G.cycleLengths.card : ℝ) * (2 : ℝ) ^ (R + 1) :=
        mul_le_mul_of_nonneg_right hcardLower (by positivity)
  have hcardNat : G.cycleLengths.card ≤ 2 ^ G.cycleRank := by
    have h := G.cycleLengths_card_le
    exact h.trans (Nat.sub_le _ _)
  have hcardUpper : (G.cycleLengths.card : ℝ) ≤ (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast hcardNat
  have hpow' : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ (G.cycleRank + (R + 1)) := by
    calc
      (2 : ℝ) ^ r ≤
          (G.cycleLengths.card : ℝ) * (2 : ℝ) ^ (R + 1) := hpow
      _ ≤ (2 : ℝ) ^ G.cycleRank * (2 : ℝ) ^ (R + 1) :=
        mul_le_mul_of_nonneg_right hcardUpper (by positivity)
      _ = (2 : ℝ) ^ (G.cycleRank + (R + 1)) := by rw [← pow_add]
  have hpowNat : 2 ^ r ≤ 2 ^ (G.cycleRank + (R + 1)) := by
    exact_mod_cast hpow'
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpowNat

/-- On the quartic scale, subtracting the canonical witness edge budget from
the cycle rank forced by the high-cycle branch leaves at least `2R` outside
rank, including the common boundary contribution. -/
theorem canonicalWitness_outsideRank_ge
    (G : PhysicalGraph) (C R r : ℕ)
    (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hscale : 2 ^ (C * R ^ 4) ≤ r)
    (hcount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
    let E := witnessSupportEdges G F
    2 * R ≤ G.outsideCycleRank E + G.commonBoundaryRank E := by
  let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
  let E := witnessSupportEdges G F
  have hrankNear := rank_ge_of_high_cycle_count G R r hR hcount
  have hRp : R ≤ R ^ 4 := by
    calc
      R = R ^ 1 := by simp
      _ ≤ R ^ 4 := Nat.pow_le_pow_right (by omega : 1 ≤ R) (by omega)
  have h8R : 8 * R ≤ C * R ^ 4 := by
    calc
      8 * R ≤ 8 * R ^ 4 := Nat.mul_le_mul_left 8 hRp
      _ ≤ C * R ^ 4 := Nat.mul_le_mul_right (R ^ 4) hC
  have hexp : 4 * R + 1 ≤ C * R ^ 4 := by omega
  have hscale' : 2 ^ (4 * R + 1) ≤ r := by
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp).trans hscale
  have h3R : 3 * R ≤ 2 ^ (4 * R) := by
    calc
      3 * R ≤ 2 ^ R := three_mul_le_two_pow R hR
      _ ≤ 2 ^ (4 * R) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  have hbudgetLower : 2 ^ (4 * R) + 3 * R ≤ r := by
    apply (show 2 ^ (4 * R) + 3 * R ≤ 2 ^ (4 * R + 1) from ?_).trans hscale'
    calc
      2 ^ (4 * R) + 3 * R ≤ 2 ^ (4 * R) + 2 ^ (4 * R) :=
        Nat.add_le_add_left h3R _
      _ = 2 ^ (4 * R + 1) := by rw [pow_succ]; omega
  have hrankTotal : 2 ^ (4 * R) + 3 * R ≤ G.cycleRank + (R + 1) :=
    hbudgetLower.trans hrankNear
  have hEdgeBudget :
      (witnessSupportGraph G F).edgeCount + 1 ≤ 2 ^ (4 * R) := by
    dsimp [F]
    exact canonicalWitnessSupport_add_one_le_power G R hR hcov
  have hEcard : E.card + 1 ≤ 2 ^ (4 * R) := by
    simpa [E, F, witnessSupportGraph] using hEdgeBudget
  have hrestricted : G.restrictedCycleRank E ≤ 2 ^ (4 * R) - 1 := by
    have hrankE : G.restrictedCycleRank E ≤ E.card := by
      calc
        G.restrictedCycleRank E = (G.restrictPhysical E).cycleRank := by
          rw [G.restrictPhysical_cycleRank]
        _ ≤ (G.restrictPhysical E).edgeCount :=
          PhysicalGraph.cycleRank_le_edgeCount (G.restrictPhysical E)
        _ = E.card := rfl
    omega
  have hpartition := G.cycleRank_edgePartition E
  have hneed : 2 * R + G.restrictedCycleRank E ≤ G.cycleRank := by omega
  rw [hpartition] at hneed
  change 2 * R ≤ G.outsideCycleRank E + G.commonBoundaryRank E
  omega

end Erdos1016.Proof.HighCycleOutsideRank

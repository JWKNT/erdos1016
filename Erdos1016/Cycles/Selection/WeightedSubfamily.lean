import Erdos1016.Cycles.Selection.WeightThreshold
import Erdos1016.Probability.Avoidance.FiniteCycleBounds

set_option autoImplicit false

/-!
# Deterministic cycle-weight threshold selection

After the return filter has supplied a large total cycle weight, the paper
selects a graph-determined subfamily whose weight first reaches a target.
The generic finite selection theorem handles the threshold argument; this
module supplies the cycle-specific cap coming from a minimum length.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open BoundaryDecay

local instance deterministicCycleSelectionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {G : PhysicalGraph}

/-- A cycle longer than `D` has weight at most the reciprocal of `2^(D+1)`. -/
theorem cycleWeight_le_of_length_gt {D : ℕ} (C : G.CycleWord)
    (hD : D < BoundaryDecay.Cycle.length C) :
    cycleWeight C ≤ 1 / (2 : ℝ) ^ (D + 1) := by
  have hpow : (2 : ℝ) ^ (D + 1) ≤
      (2 : ℝ) ^ BoundaryDecay.Cycle.length C := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (Nat.succ_le_of_lt hD))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (D + 1) := by positivity
  have hpos' : (0 : ℝ) < (2 : ℝ) ^ BoundaryDecay.Cycle.length C := by positivity
  unfold cycleWeight
  exact one_div_le_one_div_of_le hpos hpow

/-- From a large deterministic cycle-weight family whose cycles all have
length greater than `D`, select a subfamily with target weight `τ` and the
explicit overshoot bound `2^(-(D+1))`. -/
theorem exists_cycleWeight_subfamily_between_threshold
    (F : Finset G.CycleWord) (D : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hlength : ∀ C ∈ F, D < BoundaryDecay.Cycle.length C)
    (hmass : τ ≤ cycleWeightSum F) :
    ∃ F' ⊆ F, τ ≤ cycleWeightSum F' ∧
      cycleWeightSum F' ≤ τ + 1 / (2 : ℝ) ^ (D + 1) := by
  have hcap : ∀ C ∈ F, 0 ≤ cycleWeight C ∧
      cycleWeight C ≤ 1 / (2 : ℝ) ^ (D + 1) := by
    intro C hC
    constructor
    · unfold cycleWeight
      positivity
    · exact cycleWeight_le_of_length_gt C (hlength C hC)
  exact BoundaryDecay.exists_subset_sum_between_threshold F cycleWeight τ
    (1 / (2 : ℝ) ^ (D + 1)) hτ (by positivity) hcap hmass

end Erdos1016.CycleSupply

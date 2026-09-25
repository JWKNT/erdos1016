import Erdos1016.Probability.Cylinders.AffinePairs

set_option autoImplicit false

/-!
# Pair bounds for feasible affine constraints

For two feasible affine cylinders, compatibility determines their joint
probability exactly through the common constraint space. Incompatible
cylinders are disjoint. This file isolates the two inequalities needed by
the graphical second-moment argument.
-/

noncomputable section

namespace Erdos1016.Proof.SelectedTriplePairBounds

open Erdos1016.Proof.AffineCylinders
open Erdos1016.Proof.AffineCylinderPairs

abbrev F₂ := Erdos1016.Proof.AffineCylinders.F₂

variable {W : Type*} [AddCommGroup W] [Module F₂ W]
  [FiniteDimensional F₂ W] [Fintype W] [Fintype F₂]

/-- Uniform cylinder probability is nonnegative. -/
theorem probability_nonneg (L : Submodule F₂ W) (a : Module.Dual F₂ L) :
    0 ≤ probability (Cylinder L a) := by
  unfold probability
  positivity



/-- If two constraint spaces share at most one independent binary
constraint, the joint probability is at most twice the product of the
marginals. -/
theorem pair_probability_le_twice_product_of_common_finrank_le_one
    (L M : Submodule F₂ W) (a : Module.Dual F₂ L)
    (b : Module.Dual F₂ M)
    (hcommon : Module.finrank F₂ (CommonSubspace L M) ≤ 1) :
    probability (fun x => Cylinder L a x ∧ Cylinder M b x) ≤
      2 * probability (Cylinder L a) * probability (Cylinder M b) := by
  classical
  have hp := probability_nonneg L a
  have hq := probability_nonneg M b
  by_cases hcompat : Compatible L M a b
  · rw [compatible_pair_common_mode L M a b hcompat]
    have hpow : (2 : ℝ) ^ Module.finrank F₂ (CommonSubspace L M) ≤ 2 := by
      have hnat := Nat.pow_le_pow_right (by decide : 0 < 2) hcommon
      exact_mod_cast hnat
    apply mul_le_mul_of_nonneg_right _ hq
    exact mul_le_mul_of_nonneg_right hpow hp
  · rw [incompatible_pair_probability L M a b hcompat]
    positivity

end Erdos1016.Proof.SelectedTriplePairBounds

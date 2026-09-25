import Erdos1016.Probability.Conditional.ComponentProductLaw

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.ConditionalProductProbability





/-- Local density is always in `[0,1]` when the local state space is
nonempty. -/
theorem localDensity_bounds {α : Type*} [Fintype α] [Nonempty α] (Q : α → Prop) :
    0 ≤ Erdos1016.Proof.ActiveComponentProbability.density Q ∧
    Erdos1016.Proof.ActiveComponentProbability.density Q ≤ 1 := by
  classical
  unfold Erdos1016.Proof.ActiveComponentProbability.density
  have hden : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty α›
  have hnum : 0 ≤ (Fintype.card {a : α // Q a} : ℝ) := by positivity
  have hle : Fintype.card {a : α // Q a} ≤ Fintype.card α :=
    Fintype.card_subtype_le Q
  constructor
  · exact div_nonneg hnum (le_of_lt hden)
  · exact (div_le_one hden).2 (by exact_mod_cast hle)







end Erdos1016.Proof.ConditionalProductProbability

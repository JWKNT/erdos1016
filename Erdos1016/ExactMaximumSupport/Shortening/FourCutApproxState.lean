import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofStates

set_option autoImplicit false

/-! Variable-tolerance gadget inequalities for the compactness proof. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
open ExactMaximum FourCutArithmeticProof

structure ApproxState (η : ℝ) (a : Fin 4 → Fin 4 → ℝ) (u : Fin 3 → ℝ) : Prop
    extends FourState a u where
  t1 : ∀ i j k, i≠j → i≠k → j≠k → 1+η≤a i k+a j k → a i j≤η
  t2 : ∀ i j k l, Distinct4 i j k l → 2+η≤a i k+a i l+a j k+a j l →
    u (pairingOf i k)+u (pairingOf i l)≤η
  t3 : ∀ i j k l, Distinct4 i j k l →
    1+η≤a i j+u (pairingOf i k)+u (pairingOf i l) → a k l≤η

/-- The same four tested pairs are exactly full in both shores. -/
def CommonFullCross (x a : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∃ i j k l : Fin 4, Distinct4 i j k l ∧
    x i k=1 ∧ x i l=1 ∧ x j k=1 ∧ x j l=1 ∧
    a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1

end Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness

import Erdos1016.Decomposition.Descent.SplitCredit
import Erdos1016.Decomposition.Descent.BondDecomposition

set_option autoImplicit false

/-!
# Signed exterior credit for the actual finite cut decomposition

This instantiates the marked-leaf credit induction on the regions in
`SafeCore.Decomposition`. A no-contact sibling has strictly negative
potential, so it cannot disappear from the pruned tree of negative leaves.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.Proof.GraphDecompositionCredit

open Erdos1016.SafeCore
open Erdos1016.Proof.SignedCredit

variable (G : PhysicalGraph) (P : CutParameters)





/-- A sibling with no old-exterior contact has strictly negative potential.
The strict cut inequality is retained through the no-contact calculation. -/
theorem no_contact_sibling_potential_neg {U : Finset G.Vertex}
    (hG : G.IsConnected) {s : BondSplit G U} (hcheap : Cheap G P s)
    (hn : touchingComponents G U s.right = ∅) :
    potential G P s.right < 0 := by
  have hsib := safe_sibling G hG s hn
  have hR : 0 < (s.right.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 s.right_connected.1
  have hRU : (s.right.card : ℝ) ≤ U.card := by
    exact_mod_cast s.right_card_lt.le
  have hpow : (U.card : ℝ) ^ (P.p - 1) ≤
      (s.right.card : ℝ) ^ (P.p - 1) :=
    Real.rpow_le_rpow_of_nonpos hR hRU (by linarith [P.p_lt_one])
  have hmin : ((min s.left.card s.right.card : ℕ) : ℝ) ≤
      (s.right.card : ℝ) := by
    exact_mod_cast min_le_right s.left.card s.right.card
  have hmul : (s.right.card : ℝ) * (s.right.card : ℝ) ^ (P.p - 1) =
      (s.right.card : ℝ) ^ P.p := by
    calc
      _ = (s.right.card : ℝ) ^ (1 : ℝ) *
          (s.right.card : ℝ) ^ (P.p - 1) := by rw [Real.rpow_one]
      _ = (s.right.card : ℝ) ^ (1 + (P.p - 1)) :=
        (Real.rpow_add hR _ _).symm
      _ = _ := by congr 1; ring
  unfold potential budget
  rw [hsib.2.2.2, sub_lt_zero]
  calc
    (crossSize G s.left s.right : ℝ) <
        P.epsilon * (min s.left.card s.right.card : ℕ) *
          (U.card : ℝ) ^ (P.p - 1) := hcheap
    _ ≤ P.epsilon * (s.right.card : ℝ) *
          (s.right.card : ℝ) ^ (P.p - 1) := by
      have heps := P.epsilon_pos.le
      gcongr <;> positivity
    _ = P.epsilon * (s.right.card : ℝ) ^ P.p := by rw [mul_assoc, hmul]
    _ ≤ P.B * (s.right.card : ℝ) ^ P.p :=
      mul_le_mul_of_nonneg_right P.epsilon_le_B (Real.rpow_nonneg hR.le _)





end Erdos1016.Proof.GraphDecompositionCredit
end

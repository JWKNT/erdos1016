import Erdos1016.ExactMaximumSupport.Shortening.FourCutApproxState
import Erdos1016.ExactMaximumSupport.Shortening.FourCutLimitRigidity
import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofProducts
import Erdos1016.ExactMaximumSupport.FourCutPairingBounds

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Exact limiting gluing: the star alternative is excluded on both shores.
Only elementary bilinear estimates and the exact limit classifier are used;
the older numerical rigidity theorem is not invoked. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness
open ExactMaximum FourCutArithmeticProof FourCutPairingBounds

/-- A limiting crossing contribution of four forces a common full cross. -/
theorem common_full_cross_of_limit
    {x a : Fin 4 → Fin 4 → ℝ} {p u : Fin 3 → ℝ}
    (hx : FourState x p) (hy : FourState a u) (hl : FourCutLimitRigidity.LimitState a u)
    (hB : 4≤pairSum x a+pairingSum p u) : CommonFullCross x a := by
  have hp := pairSum_le hx hy
  have hf := pairingSum_le_sum p u hx.u_nonneg hy.u_nonneg hx.u_sum
  have ht : 4≤pathSum a+forestSum u := by
    simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
  rcases FourCutLimitRigidity.rigidity hl ht with ⟨hcross,hS,hF⟩ | ⟨hstar,hS,hF⟩
  · obtain ⟨i,j,k,l,hd,ha1,ha2,ha3,ha4⟩ := hcross
    have full (v w : Fin 4) (hvw : v≠w) (havw : a v w=1) : x v w=1 := by
      rcases hx.gap v w hvw with hfull | hgap
      · exact hfull
      · have hh := pairSum_loss hx hy v w hvw havw hgap
        exfalso
        simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
    exact ⟨i,j,k,l,hd,full i k hd.2.1 ha1,full i l hd.2.2.1 ha2,
      full j k hd.2.2.2.1 ha3,full j l hd.2.2.2.2.1 ha4,ha1,ha2,ha3,ha4⟩
  · obtain ⟨i,hstar⟩ := hstar
    by_cases hxs : ∀ j,j≠i → x i j=1
    · have hh := pairingSum_le_three_quarters p u hy.u_nonneg
        (hx.star i hxs) (hy.star i hstar) hx.u_sum hy.u_sum
      exfalso
      simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
    · push_neg at hxs
      obtain ⟨j,hji,hneq⟩ := hxs
      have hh := pairSum_loss hx hy i j (Ne.symm hji) (hstar j hji)
        ((hx.gap i j (Ne.symm hji)).resolve_left hneq)
      exfalso
      simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith

end Erdos1016.ExactMaximumSupport.Shortening.FourCutCompactness

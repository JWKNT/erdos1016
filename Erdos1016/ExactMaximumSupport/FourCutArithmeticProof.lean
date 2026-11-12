import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofProducts
import Erdos1016.ExactMaximumSupport.FourCutPairingBounds

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The four-cut arithmetic endpoint

The paper's four cases are assembled from the actual scalar state estimates.
The conclusion is exactly Fable's `FourCutArithmeticStatement`.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
open ExactMaximum FourCutPairingBounds

/-- The scalar part of the cyclic-four-cut theorem, with no additional premise. -/
theorem fourCutArithmeticStatement : FourCutArithmeticStatement := by
  intro x a p u cX cY dX dY hx ha hdX hdY hpHalf hcX0 hcX1 hcY0 hcY hsmall
  have dXp : 0<dX := by linarith
  have dYp : 0<dY := by linarith
  have hX : cX/dY<1/1000 := by
    apply (div_lt_iff₀ dYp).mpr
    linarith
  have hpair := pairSum_le hx ha.toFourState
  have hforest := pairingSum_le_sum p u hx.u_nonneg ha.u_nonneg hx.u_sum
  by_cases hrich : ∃ i j,i≠j ∧ 501/1000≤a i j
  · have hYsmall := hsmall hrich
    have hY : cY/dX≤1/2000 := by
      apply (div_le_iff₀ dXp).mpr
      simp only [pathSum,forestSum,pairSum,pairingSum] at *
      linarith
    by_cases ht : pathSum a+forestSum u<399/100
    · left
      dsimp [forestSum] at ht
      simp only [pathSum,forestSum,pairSum,pairingSum] at *
      linarith
    · have htotal : 399/100≤pathSum a+forestSum u := le_of_not_gt ht
      rcases rigidity ha htotal with ⟨i,hstar⟩ | ⟨i,j,k,l,hd,hb,hc,hd',he⟩
      · left
        have hs := star_pathSum ha i hstar
        by_cases hxs : ∀ j,j≠i → x i j=1
        · have hp := hx.star i hxs
          have hu := ha.star i hstar
          have hq := pairingSum_le_three_quarters p u ha.u_nonneg hp hu hx.u_sum ha.u_sum
          simp only [pathSum,forestSum,pairSum,pairingSum] at *
          linarith
        · push_neg at hxs
          obtain ⟨j,hji,hneq⟩ := hxs
          have hg := (hx.gap i j (Ne.symm hji)).resolve_left hneq
          have hl := pairSum_loss hx ha.toFourState i j (Ne.symm hji) (hstar j hji) hg
          have hF := ha.u_sum
          simp only [pathSum,forestSum,pairSum,pairingSum] at *
          linarith
      · obtain ⟨hS,hF⟩ := full_cross_bounds ha i j k l hd hb hc hd' he
        rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
        by_cases hxb : x i k=1
        · by_cases hxc : x i l=1
          · by_cases hxd : x j k=1
            · by_cases hxe : x j l=1
              · exact Or.inr ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,hxb,hxc,hxd,hxe,hb,hc,hd',he⟩
              · left
                have hl := pairSum_loss hx ha.toFourState j l hjl he ((hx.gap j l hjl).resolve_left hxe)
                dsimp [forestSum] at hF
                simp only [pathSum,forestSum,pairSum,pairingSum] at *
                linarith
            · left
              have hl := pairSum_loss hx ha.toFourState j k hjk hd' ((hx.gap j k hjk).resolve_left hxd)
              dsimp [forestSum] at hF
              simp only [pathSum,forestSum,pairSum,pairingSum] at *
              linarith
          · left
            have hl := pairSum_loss hx ha.toFourState i l hil hc ((hx.gap i l hil).resolve_left hxc)
            dsimp [forestSum] at hF
            simp only [pathSum,forestSum,pairSum,pairingSum] at *
            linarith
        · left
          have hl := pairSum_loss hx ha.toFourState i k hik hb ((hx.gap i k hik).resolve_left hxb)
          dsimp [forestSum] at hF
          simp only [pathSum,forestSum,pairSum,pairingSum] at *
          linarith
  · have hlow : ∀ i j,i≠j → a i j≤501/1000 := by
      intro i j hij
      by_contra hn
      exact hrich ⟨i,j,hij,(lt_of_not_ge hn).le⟩
    left
    by_cases hd : 4≤dX
    · have hY : cY/dX≤9/64 := by
        apply (div_le_iff₀ dXp).mpr
        simp only [pathSum,forestSum,pairSum,pairingSum] at *
        linarith
      have hs := low_total ha hlow
      dsimp [forestSum] at hs
      simp only [pathSum,forestSum,pairSum,pairingSum] at *
      linarith
    · have hY : cY/dX≤9/32 := by
        apply (div_le_iff₀ dXp).mpr
        simp only [pathSum,forestSum,pairSum,pairingSum] at *
        linarith
      obtain ⟨q,_,hq⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
      have hp := hpHalf (lt_of_not_ge hd)
      have hq' := pairingSum_le_half_sum_add p u q ha.u_nonneg hp hx.u_sum
        (fun i => hq i (Finset.mem_univ i))
      have hs := low_half_total ha hlow q
      dsimp [forestSum] at hs
      simp only [pathSum,forestSum,pairSum,pairingSum] at *
      linarith

end Erdos1016.ExactMaximumSupport.FourCutArithmeticProof

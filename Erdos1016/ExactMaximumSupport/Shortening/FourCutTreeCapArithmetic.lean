import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofProducts
import Erdos1016.ExactMaximumSupport.FourCutPairingBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Finite tree-cap replacement for the low-state branch. This consumes the
existing fixed-margin LargeState; no arbitrary-epsilon FewCycles theorem is
assumed. The new graph input is precisely the three actual tree-cap bounds. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCapArithmetic
open ExactMaximum FourCutArithmeticProof FourCutPairingBounds

variable {x a : Fin 4 → Fin 4 → ℝ} {p u : Fin 3 → ℝ}

/-- Convexity over the three pairing sectors, retaining the smallest coordinate. -/
theorem pairing_le_complement_min (hx : FourState x p) (ha : FourState a u)
    (q : Fin 3) (hq : ∀ i,u q≤u i) : pairingSum p u≤forestSum u-u q := by
  have hp0 := hx.u_nonneg 0; have hp1 := hx.u_nonneg 1; have hp2 := hx.u_nonneg 2
  have hu := coordinate_le_forest ha q
  have h0 := mul_nonneg hp0 (sub_nonneg.mpr (hq 0))
  have h1 := mul_nonneg hp1 (sub_nonneg.mpr (hq 1))
  have h2 := mul_nonneg hp2 (sub_nonneg.mpr (hq 2))
  have ht := mul_nonneg (sub_nonneg.mpr hx.u_sum) (sub_nonneg.mpr hu)
  dsimp [pairingSum,forestSum] at *
  nlinarith

/-- The leading cycle bound on the three tree caps bounds the complete gluing form. -/
theorem tree_cap_bilinear (hx : FourState x p) (ha : FourState a u) (z C : ℝ)
    (hcap : ∀ q : Fin 3,z+pathSum a+forestSum u-u q≤C) :
    z+pairSum x a+pairingSum p u≤C := by
  classical
  obtain ⟨q,_,hq⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  have hp := pairing_le_complement_min hx ha q (fun i => hq i (Finset.mem_univ i))
  have ha' := pairSum_le hx ha
  have hc := hcap q
  linarith

/-- The small shore may have bounded rank: only its rank being at least one matters. -/
theorem tree_cap_near_four (e z q B : ℝ)
    (he : e≤1/1000) (hq : q≤z/2)
    (htotal : 4≤e+q+B) (hcap : z+B≤4001/1000) :
    z≤4/1000 ∧ 3997/1000≤B := by
  constructor <;> linarith

/-- With a gluing value at least 3.997, fixed-margin rigidity leaves only a
common full cross. No rank-one exception or cycle-density bound is used. -/
theorem common_full_cross (hx : FourState x p) (ha : LargeState a u)
    (hB : 3997/1000≤pairSum x a+pairingSum p u) :
    ∃ i j k l : Fin 4,Distinct4 i j k l ∧
      x i k=1 ∧ x i l=1 ∧ x j k=1 ∧ x j l=1 ∧
      a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1 := by
  have hp := pairSum_le hx ha.toFourState
  have hf := pairingSum_le_sum p u hx.u_nonneg ha.u_nonneg hx.u_sum
  have ht : 399/100≤pathSum a+forestSum u := by
    simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
  rcases rigidity ha ht with ⟨i,hstar⟩ | ⟨i,j,k,l,hd,hb,hc,hd',he⟩
  · have hs := star_pathSum ha i hstar
    by_cases hxs : ∀ j,j≠i → x i j=1
    · have hq := pairingSum_le_three_quarters p u ha.u_nonneg
        (hx.star i hxs) (ha.star i hstar) hx.u_sum ha.u_sum
      exfalso
      simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
    · push_neg at hxs
      obtain ⟨j,hji,hneq⟩ := hxs
      have hl := pairSum_loss hx ha.toFourState i j (Ne.symm hji)
        (hstar j hji) ((hx.gap i j (Ne.symm hji)).resolve_left hneq)
      have hF := ha.u_sum
      exfalso
      simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
  · obtain ⟨hS,hF⟩ := full_cross_bounds ha i j k l hd hb hc hd' he
    have full (v w : Fin 4) (hvw : v≠w) (havw : a v w=1) : x v w=1 := by
      rcases hx.gap v w hvw with hfull | hgap
      · exact hfull
      · have hl := pairSum_loss hx ha.toFourState v w hvw havw hgap
        exfalso
        simp only [pathSum,forestSum,pairSum,pairingSum] at *; linarith
    exact ⟨i,j,k,l,hd,full i k hd.2.1 hb,full i l hd.2.2.1 hc,
      full j k hd.2.2.2.1 hd',full j l hd.2.2.2.2.1 he,hb,hc,hd',he⟩

/-- New finite replacement interface, with the exact three tree-cap hypotheses.
`e` is the smaller shore's cycle contribution, and `q` the larger shore's
contribution after dividing by the smaller shore's cycle-space size. -/
theorem common_full_cross_of_tree_caps (hx : FourState x p) (ha : LargeState a u)
    (e z q : ℝ) (he : e≤1/1000) (hq : q≤z/2)
    (hcap : ∀ α : Fin 3,z+pathSum a+forestSum u-u α≤4001/1000)
    (htotal : 4≤e+q+(pairSum x a+pairingSum p u)) :
    ∃ i j k l : Fin 4,Distinct4 i j k l ∧
      x i k=1 ∧ x i l=1 ∧ x j k=1 ∧ x j l=1 ∧
      a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1 := by
  have hc := tree_cap_bilinear hx ha.toFourState z (4001/1000) hcap
  have hn := tree_cap_near_four e z q (pairSum x a+pairingSum p u) he hq htotal
    (by linarith)
  exact common_full_cross hx ha hn.2

end Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCapArithmetic

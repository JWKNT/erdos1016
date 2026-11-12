import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofRigidity

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
open ExactMaximum
variable {x a : Fin 4 → Fin 4 → ℝ} {p u : Fin 3 → ℝ}

theorem pairSum_ports (hx : FourState x p) (ha : FourState a u)
    (i j k l : Fin 4) (hd : Distinct4 i j k l) :
    pairSum x a=x i j*a i j+x i k*a i k+x i l*a i l+
      x j k*a j k+x j l*a j l+x k l*a k l := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have x10:=hx.symm 1 0; have x20:=hx.symm 2 0; have x30:=hx.symm 3 0
  have x21:=hx.symm 2 1; have x31:=hx.symm 3 1; have x32:=hx.symm 3 2
  have a10:=ha.symm 1 0; have a20:=ha.symm 2 0; have a30:=ha.symm 3 0
  have a21:=ha.symm 2 1; have a31:=ha.symm 3 1; have a32:=ha.symm 3 2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> norm_num at * <;>
    dsimp [pairSum] <;>
    (try simp only [x10,x20,x30,x21,x31,x32,a10,a20,a30,a21,a31,a32]) <;> ring

theorem pairSum_le (hx : FourState x p) (ha : FourState a u) :
    pairSum x a≤pathSum a := by
  have hh (i j : Fin 4) : x i j*a i j≤a i j := by
    exact (mul_le_mul_of_nonneg_right (hx.le_one i j) (ha.nonneg i j)).trans_eq (one_mul _)
  have h01:=hh 0 1; have h02:=hh 0 2; have h03:=hh 0 3
  have h12:=hh 1 2; have h13:=hh 1 3; have h23:=hh 2 3
  dsimp [pairSum,pathSum]; linarith

/-- One nonfull coordinate opposite a full coordinate gives the exact loss 1/16. -/
theorem pairSum_loss (hx : FourState x p) (ha : FourState a u)
    (i j : Fin 4) (hij : i≠j) (hfull : a i j=1) (hgap : x i j≤15/16) :
    pairSum x a≤pathSum a-1/16 := by
  obtain ⟨k,l,hd⟩ := complete_pair i j hij
  have hp := pairSum_ports hx ha i j k l hd
  obtain ⟨_,hik,hil,hjk,hjl,hkl⟩ := hd
  have hs := path_sum_ports ha i j k l hij hik hil hjk hjl hkl
  have hh (v w : Fin 4) : x v w*a v w≤a v w := by
    exact (mul_le_mul_of_nonneg_right (hx.le_one v w) (ha.nonneg v w)).trans_eq (one_mul _)
  have hb:=hh i k; have hc:=hh i l; have hd':=hh j k; have he:=hh j l; have hf:=hh k l
  rw [hp,←hs,hfull,mul_one]
  linarith

/-- The other three path coordinates of a full star are at most κ. -/
theorem star_pathSum (h : LargeState a u) (i : Fin 4)
    (hstar : ∀ j,j≠i → a i j=1) : pathSum a≤3003/1000 := by
  obtain ⟨j,hij⟩ : ∃ j : Fin 4,i≠j := by
    by_cases hi : i=0
    · exact ⟨1,by subst i; decide⟩
    · exact ⟨0,hi⟩
  obtain ⟨k,l,_,hik,hil,hjk,hjl,hkl⟩ := complete_pair i j hij
  have hab := hstar j (Ne.symm hij)
  have hac := hstar k (Ne.symm hik)
  have had := hstar l (Ne.symm hil)
  have hbc : a j k≤1/1000 := by
    apply h.t1 j k i hjk (Ne.symm hij) (Ne.symm hik)
    rw [h.symm j i,h.symm k i,hab,hac]; norm_num
  have hbd : a j l≤1/1000 := by
    apply h.t1 j l i hjl (Ne.symm hij) (Ne.symm hil)
    rw [h.symm j i,h.symm l i,hab,had]; norm_num
  have hcd : a k l≤1/1000 := by
    apply h.t1 k l i hkl (Ne.symm hik) (Ne.symm hil)
    rw [h.symm k i,h.symm l i,hac,had]; norm_num
  have hs:=path_sum_ports h.toFourState i j k l hij hik hil hjk hjl hkl
  rw [←hs]
  linarith

/-- A full cross leaves at most 0.003 in the forest coordinates. -/
theorem full_cross_bounds (h : LargeState a u) (i j k l : Fin 4)
    (hd : Distinct4 i j k l) (hb : a i k=1) (hc : a i l=1)
    (hd' : a j k=1) (he : a j l=1) :
    pathSum a≤4002/1000 ∧ forestSum u≤3/1000 := by
  obtain ⟨hij,hik,hil,hjk,hjl,hkl⟩ := hd
  obtain ⟨hij',hkl',hU⟩ := high_cross_small h i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩
    (by dsimp [crossSum]; rw [hb,hc,hd',he]; norm_num)
  have hs:=path_sum_ports h.toFourState i j k l hij hik hil hjk hjl hkl
  have hf:=forest_sum_ports (u:=u) i j k l hij hik hil hjk hjl hkl
  have hsmall:=opposite_bound h i k j l hik hij hil (Ne.symm hjk) hkl hjl (by rw [he]; norm_num)
  rw [hb] at hsmall
  have hu:=h.u_nonneg (pairingOf i l)
  constructor
  · rw [←hs]; linarith
  · rw [←hf]; linarith

end Erdos1016.ExactMaximumSupport.FourCutArithmeticProof

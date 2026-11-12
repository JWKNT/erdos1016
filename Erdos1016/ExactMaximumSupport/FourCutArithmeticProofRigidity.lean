import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofStates

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
open ExactMaximum

abbrev crossSum (a : Fin 4 → Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  a i k+a i l+a j k+a j l
abbrev FullStar (a : Fin 4 → Fin 4 → ℝ) : Prop := ∃ i,∀ j,j≠i → a i j=1
abbrev FullCross (a : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∃ i j k l,Distinct4 i j k l ∧ a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1

variable {a : Fin 4 → Fin 4 → ℝ} {u : Fin 3 → ℝ}

theorem four_exhaust (i j k l : Fin 4) (hd : Distinct4 i j k l) (v : Fin 4) :
    v=i ∨ v=j ∨ v=k ∨ v=l := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  simp only [ne_eq,Fin.ext_iff] at *
  omega


/-- The two opposite coordinates are small when the four cross coordinates are large. -/
theorem high_cross_small (h : LargeState a u) (i j k l : Fin 4) (hd : Distinct4 i j k l)
    (hc : 2004/1000≤crossSum a i j k l) :
    a i j≤1/1000 ∧ a k l≤1/1000 ∧
      u (pairingOf i k)+u (pairingOf i l)≤1/1000 := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  refine ⟨?_,?_,h.t2 i j k l hij hik hil hjk hjl hkl hc⟩
  · by_cases hb : 1002/1000≤a i k+a j k
    · exact h.t1 i j k hij hik hjk hb
    · apply h.t1 i j l hij hil hjl
      dsimp [crossSum] at hc; linarith
  · by_cases hb : 1002/1000≤a k i+a l i
    · exact h.t1 k l i hkl (Ne.symm hik) (Ne.symm hil) hb
    · apply h.t1 k l j hkl (Ne.symm hjk) (Ne.symm hjl)
      rw [h.symm k i,h.symm l i] at hb
      rw [h.symm k j,h.symm l j]
      dsimp [crossSum] at hc; linarith

/-- A numerical form of the high-cross case of rigidity. -/
theorem high_cross_scalar (b c d e f : ℝ)
    (hb1 : b≤1) (hc1 : c≤1) (hd1 : d≤1) (he1 : e≤1)
    (ht : 399/100≤b+c+d+e+f+3/1000)
    (hcross : 2004/1000≤b+c+d+e)
    (hb : 1/1000<e → b+f<1002/1000)
    (hc : 1/1000<d → c+f<1002/1000)
    (hd : 1/1000<c → d+f<1002/1000)
    (he : 1/1000<b → e+f<1002/1000) :
    15/16<b ∧ 15/16<c ∧ 15/16<d ∧ 15/16<e := by
  have bpos : 1/1000<b := by
    by_contra hn
    have cp : 1/1000<c := by linarith
    have dp : 1/1000<d := by linarith
    have hh := hc dp
    linarith
  have cpos : 1/1000<c := by
    by_contra hn
    have ep : 1/1000<e := by linarith
    have hh := hb ep
    linarith
  have dpos : 1/1000<d := by
    by_contra hn
    have hh := he bpos
    linarith
  have epos : 1/1000<e := by
    by_contra hn
    have hh := hc dpos
    linarith
  have hb' := hb epos; have hc' := hc dpos
  have hd' := hd cpos; have he' := he bpos
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Every high cross is full once the total state is near four. -/
theorem high_cross_full (h : LargeState a u) (ht : 399/100≤pathSum a+forestSum u)
    (i j k l : Fin 4) (hd : Distinct4 i j k l) (hc : 2004/1000≤crossSum a i j k l) :
    a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1 := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  obtain ⟨hab,hcd,hU⟩ := high_cross_small h i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ hc
  have hs := path_sum_ports h.toFourState i j k l hij hik hil hjk hjl hkl
  have hf := forest_sum_ports (u:=u) i j k l hij hik hil hjk hjl hkl
  rw [←hs,←hf] at ht
  have hji := pairing_comm j i
  have hjk' := pairing_complement i l j k hil hij hik (Ne.symm hjl) (Ne.symm hkl) hjk
  have hjl' := pairing_complement i k j l hik hij hil (Ne.symm hjk) hkl hjl
  have hb : 1/1000<a j l → a i k+u (pairingOf i j)<1002/1000 := by
    intro hp
    have hh := opposite_bound h i k j l hik hij hil (Ne.symm hjk) hkl hjl hp
    have hu := h.u_nonneg (pairingOf i l)
    linarith
  have hc' : 1/1000<a j k → a i l+u (pairingOf i j)<1002/1000 := by
    intro hp
    have hh := opposite_bound h i l j k hil hij hik (Ne.symm hjl) (Ne.symm hkl) hjk hp
    have hu := h.u_nonneg (pairingOf i k)
    linarith
  have hd' : 1/1000<a i l → a j k+u (pairingOf i j)<1002/1000 := by
    intro hp
    have hh := opposite_bound h j k i l hjk (Ne.symm hij) hjl (Ne.symm hik) hkl hil hp
    rw [hji] at hh
    have hu := h.u_nonneg (pairingOf j l)
    linarith
  have he : 1/1000<a i k → a j l+u (pairingOf i j)<1002/1000 := by
    intro hp
    have hh := opposite_bound h j l i k hjl (Ne.symm hij) hjk (Ne.symm hil) (Ne.symm hkl) hik hp
    rw [hji] at hh
    have hu := h.u_nonneg (pairingOf j k)
    linarith
  obtain ⟨hbgt,hcgt,hdgt,hegt⟩ := high_cross_scalar (a i k) (a i l) (a j k) (a j l)
    (u (pairingOf i j)) (h.le_one i k) (h.le_one i l) (h.le_one j k) (h.le_one j l)
    (by linarith) hc hb hc' hd' he
  exact ⟨(h.gap i k hik).resolve_right (not_le_of_gt hbgt),
    (h.gap i l hil).resolve_right (not_le_of_gt hcgt),
    (h.gap j k hjk).resolve_right (not_le_of_gt hdgt),
    (h.gap j l hjl).resolve_right (not_le_of_gt hegt)⟩

/-- In the low-cross case, one small coordinate forces a full star. -/
theorem low_cross_star (h : LargeState a u) (ht : 399/100≤pathSum a+forestSum u)
    (hlow : ∀ i j k l,Distinct4 i j k l → crossSum a i j k l<2004/1000)
    (i j k l : Fin 4) (hd : Distinct4 i j k l) (hsmall : a k l≤1/1000) : FullStar a := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have hS : 299/100≤pathSum a := by have := h.u_sum; dsimp [forestSum] at *; linarith
  have hs := path_sum_ports h.toFourState i j k l hij hik hil hjk hjl hkl
  have hc0 := hlow i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have hc1 := hlow i k j l ⟨hik,hij,hil,Ne.symm hjk,hkl,hjl⟩
  have hc2 := hlow i l j k ⟨hil,hij,hik,Ne.symm hjl,Ne.symm hkl,hjk⟩
  rw [←hs] at hS
  dsimp [crossSum] at hc0 hc1 hc2
  rw [h.symm k j] at hc1
  rw [h.symm l j,h.symm l k] at hc2
  have hab : a i j=1 := (h.gap i j hij).resolve_right (by linarith)
  by_cases hb : a i k<2/1000
  · have he : a j l=1 := (h.gap j l hjl).resolve_right (by linarith)
    have hc : a i l≤1/1000 := by
      apply h.t1 i l j hil hij (Ne.symm hjl)
      rw [hab,h.symm l j,he]; norm_num
    have hd' : a j k=1 := (h.gap j k hjk).resolve_right (by linarith)
    refine ⟨j,?_⟩
    intro q hq
    rcases four_exhaust i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ q with rfl | rfl | rfl | rfl
    · exact (h.symm _ _).trans hab
    · exact (hq rfl).elim
    · exact hd'
    · exact he
  · have hd' : a j k≤1/1000 := by
      apply h.t1 j k i hjk (Ne.symm hij) (Ne.symm hik)
      rw [h.symm j i,h.symm k i,hab]; linarith
    have hc : a i l=1 := (h.gap i l hil).resolve_right (by linarith)
    have he : a j l≤1/1000 := by
      apply h.t1 j l i hjl (Ne.symm hij) (Ne.symm hil)
      rw [h.symm j i,h.symm l i,hab,hc]; norm_num
    have hb' : a i k=1 := (h.gap i k hik).resolve_right (by linarith)
    refine ⟨i,?_⟩
    intro q hq
    rcases four_exhaust i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ q with rfl | rfl | rfl | rfl
    · exact (hq rfl).elim
    · exact hab
    · exact hb'
    · exact hc

/-- The scalar rigidity lemma: a near-maximal total contains a full star or a full cross. -/
theorem rigidity (h : LargeState a u) (ht : 399/100≤pathSum a+forestSum u) :
    FullStar a ∨ FullCross a := by
  by_cases hc : ∃ i j k l,Distinct4 i j k l ∧ 2004/1000≤crossSum a i j k l
  · obtain ⟨i,j,k,l,hd,hc⟩ := hc
    exact Or.inr ⟨i,j,k,l,hd,high_cross_full h ht i j k l hd hc⟩
  · have hlow : ∀ i j k l,Distinct4 i j k l → crossSum a i j k l<2004/1000 := by
      intro i j k l hd
      exact lt_of_not_ge fun hh => hc ⟨i,j,k,l,hd,hh⟩
    have hc0 := hlow 0 1 2 3 (by decide)
    have hc1 := hlow 0 2 1 3 (by decide)
    have hc2 := hlow 0 3 1 2 (by decide)
    dsimp [crossSum] at hc0 hc1 hc2
    rw [h.symm 2 1] at hc1
    rw [h.symm 3 1,h.symm 3 2] at hc2
    have hS : pathSum a<3006/1000 := by dsimp [crossSum,pathSum] at *; linarith
    have hn : ¬(∀ i j,i≠j → 1/1000<a i j) := by
      intro hp
      have hh := all_opposite_sum h hp
      dsimp [pathSum,forestSum] at hS ht hh
      linarith
    push_neg at hn
    obtain ⟨k,l,hkl,hsmall⟩ := hn
    obtain ⟨i,j,hd⟩ := complete_pair k l hkl
    rcases hd with ⟨_,hki,hkj,hli,hlj,hij⟩
    exact Or.inl (low_cross_star h ht hlow i j k l
      ⟨hij,Ne.symm hki,Ne.symm hli,Ne.symm hkj,Ne.symm hlj,hkl⟩ hsmall)

end Erdos1016.ExactMaximumSupport.FourCutArithmeticProof

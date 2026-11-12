import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofStates

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Exact limiting four-pole rigidity.  Unlike the frozen quantitative proof,
this uses no decimal thresholds, gap hypothesis, or near-equality estimate.
Only the finite port identities are reused from FourCutArithmeticProofStates.
The passage from actual graphs to these limit hypotheses is a separate
compactness argument, recorded in the companion research note. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutLimitRigidity
open ExactMaximum FourCutArithmeticProof

/-- The qualitative gadget inequalities in a convergent sequence of large poles.
The gap and full-star half-pairing hypotheses are deliberately absent. -/
structure LimitState (a : Fin 4 → Fin 4 → ℝ) (u : Fin 3 → ℝ) : Prop where
  symm : ∀ i j, a i j=a j i
  nonneg : ∀ i j, 0≤a i j
  le_one : ∀ i j, a i j≤1
  u_nonneg : ∀ α, 0≤u α
  u_sum : u 0+u 1+u 2≤1
  t1 : ∀ i j k, i≠j → i≠k → j≠k → 0<a i j → a i k+a j k≤1
  t2 : ∀ i j k l, Distinct4 i j k l → 2<a i k+a i l+a j k+a j l →
    u (pairingOf i k)+u (pairingOf i l)=0
  t3 : ∀ i j k l, Distinct4 i j k l → 0<a k l →
    a i j+u (pairingOf i k)+u (pairingOf i l)≤1

abbrev crossSum (a : Fin 4 → Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  a i k+a i l+a j k+a j l
abbrev FullStar (a : Fin 4 → Fin 4 → ℝ) : Prop := ∃ i,∀ j,j≠i → a i j=1
abbrev FullCross (a : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∃ i j k l,Distinct4 i j k l ∧ a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1

private theorem four_exhaust (i j k l : Fin 4) (hd : Distinct4 i j k l) (v : Fin 4) :
    v=i ∨ v=j ∨ v=k ∨ v=l := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  simp only [ne_eq,Fin.ext_iff] at *
  omega

/-- A high cross and total at least four have only the exact unit solution. -/
theorem high_cross_scalar (b c d e f : ℝ)
    (hb1 : b≤1) (hc1 : c≤1) (hd1 : d≤1) (he1 : e≤1) (hf0 : 0≤f)
    (ht : 4≤b+c+d+e+f) (hx : 2<b+c+d+e)
    (hb : 0<e → b+f≤1) (hc : 0<d → c+f≤1)
    (hd : 0<c → d+f≤1) (he : 0<b → e+f≤1) :
    b=1 ∧ c=1 ∧ d=1 ∧ e=1 ∧ f=0 := by
  have bp : 0<b := by
    by_contra hn
    have dp : 0<d := by linarith
    have hh := hc dp
    linarith
  have cp : 0<c := by
    by_contra hn
    have ep : 0<e := by linarith
    have hh := hb ep
    linarith
  have dp : 0<d := by
    by_contra hn
    have hh := he bp
    linarith
  have ep : 0<e := by
    by_contra hn
    have hh := hc dp
    linarith
  have hb' := hb ep; have hc' := hc dp; have hd' := hd cp; have he' := he bp
  have hf : f=0 := by linarith
  exact ⟨by linarith,by linarith,by linarith,by linarith,hf⟩

variable {a : Fin 4 → Fin 4 → ℝ} {u : Fin 3 → ℝ}

private theorem path_sum_reindex (h : LimitState a u) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    a i j+a i k+a i l+a j k+a j l+a k l=pathSum a := by
  have h10 := h.symm 1 0; have h20 := h.symm 2 0; have h30 := h.symm 3 0
  have h21 := h.symm 2 1; have h31 := h.symm 3 1; have h32 := h.symm 3 2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num at * <;> dsimp [pathSum] <;> (try simp only [h10,h20,h30,h21,h31,h32]) <;> ring

theorem high_cross_exact (h : LimitState a u) (ht : 4≤pathSum a+forestSum u)
    (i j k l : Fin 4) (hd : Distinct4 i j k l) (hx : 2<crossSum a i j k l) :
    (a i k=1 ∧ a i l=1 ∧ a j k=1 ∧ a j l=1) ∧ pathSum a=4 ∧ forestSum u=0 := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have ha : a i j=0 := by
    have hn := h.nonneg i j
    by_contra hz
    have hp : 0<a i j := by exact lt_of_le_of_ne hn (Ne.symm hz)
    have h1 := h.t1 i j k hij hik hjk hp
    have h2 := h.t1 i j l hij hil hjl hp
    dsimp [crossSum] at hx; linarith
  have hz : a k l=0 := by
    have hn := h.nonneg k l
    by_contra hz
    have hp : 0<a k l := lt_of_le_of_ne hn (Ne.symm hz)
    have h1 := h.t1 k l i hkl (Ne.symm hik) (Ne.symm hil) hp
    have h2 := h.t1 k l j hkl (Ne.symm hjk) (Ne.symm hjl) hp
    rw [h.symm k i,h.symm l i] at h1
    rw [h.symm k j,h.symm l j] at h2
    dsimp [crossSum] at hx; linarith
  have hU := h.t2 i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ hx
  have hs := path_sum_reindex h i j k l hij hik hil hjk hjl hkl
  have hf := forest_sum_ports (u:=u) i j k l hij hik hil hjk hjl hkl
  have hb : 0<a j l → a i k+u (pairingOf i j)≤1 := by
    intro hp
    have hh := h.t3 i k j l ⟨hik,hij,hil,Ne.symm hjk,hkl,hjl⟩ hp
    have hu := h.u_nonneg (pairingOf i l)
    linarith
  have hc : 0<a j k → a i l+u (pairingOf i j)≤1 := by
    intro hp
    have hh := h.t3 i l j k ⟨hil,hij,hik,Ne.symm hjl,Ne.symm hkl,hjk⟩ hp
    have hu := h.u_nonneg (pairingOf i k)
    linarith
  have hd' : 0<a i l → a j k+u (pairingOf i j)≤1 := by
    intro hp
    have hh := h.t3 j k i l ⟨hjk,Ne.symm hij,hjl,Ne.symm hik,hkl,hil⟩ hp
    rw [pairing_comm j i] at hh
    have hu := h.u_nonneg (pairingOf j l)
    linarith
  have he : 0<a i k → a j l+u (pairingOf i j)≤1 := by
    intro hp
    have hh := h.t3 j l i k ⟨hjl,Ne.symm hij,hjk,Ne.symm hil,Ne.symm hkl,hik⟩ hp
    rw [pairing_comm j i] at hh
    have hu := h.u_nonneg (pairingOf j k)
    linarith
  obtain ⟨hb',hc',hd'',he',hf'⟩ := high_cross_scalar (a i k) (a i l) (a j k) (a j l)
    (u (pairingOf i j)) (h.le_one i k) (h.le_one i l) (h.le_one j k)
    (h.le_one j l) (h.u_nonneg _) (by linarith) hx hb hc hd' he
  exact ⟨⟨hb',hc',hd'',he'⟩,by linarith,by linarith⟩

/-- With every cross at most two, a zero edge forces a full star. -/
theorem low_cross_star (h : LimitState a u) (hs3 : pathSum a=3)
    (hlow : ∀ i j k l,Distinct4 i j k l → crossSum a i j k l≤2)
    (i j k l : Fin 4) (hd : Distinct4 i j k l) (hz : a k l=0) : FullStar a := by
  rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have hs := path_sum_reindex h i j k l hij hik hil hjk hjl hkl
  have h0 := hlow i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩
  have h1 := hlow i k j l ⟨hik,hij,hil,Ne.symm hjk,hkl,hjl⟩
  have h2 := hlow i l j k ⟨hil,hij,hik,Ne.symm hjl,Ne.symm hkl,hjk⟩
  dsimp [crossSum] at h0 h1 h2
  rw [h.symm k j] at h1
  rw [h.symm l j,h.symm l k] at h2
  have hab : a i j=1 := by have := h.le_one i j; linarith
  by_cases hp : 0<a i k
  · have hb := h.t1 i k j hik hij (Ne.symm hjk) hp
    rw [h.symm k j,hab] at hb
    have hd0 : a j k=0 := by have := h.nonneg j k; linarith
    have hc1 : a i l=1 := by have := h.le_one i l; linarith
    have he := h.t1 i l j hil hij (Ne.symm hjl) (by rw [hc1]; norm_num)
    rw [h.symm l j,hab] at he
    have he0 : a j l=0 := by have := h.nonneg j l; linarith
    have hb1 : a i k=1 := by linarith
    refine ⟨i,?_⟩
    intro q hq
    rcases four_exhaust i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ q with rfl|rfl|rfl|rfl
    · exact (hq rfl).elim
    · exact hab
    · exact hb1
    · exact hc1
  · have hb0 : a i k=0 := by have := h.nonneg i k; linarith
    have he1 : a j l=1 := by have := h.le_one j l; linarith
    have hc := h.t1 j l i hjl (Ne.symm hij) (Ne.symm hil) (by rw [he1]; norm_num)
    rw [h.symm j i,h.symm l i,hab] at hc
    have hc0 : a i l=0 := by have := h.nonneg i l; linarith
    have hd1 : a j k=1 := by linarith
    refine ⟨j,?_⟩
    intro q hq
    rcases four_exhaust i j k l ⟨hij,hik,hil,hjk,hjl,hkl⟩ q with rfl|rfl|rfl|rfl
    · exact (h.symm _ _).trans hab
    · exact (hq rfl).elim
    · exact hd1
    · exact he1

/-- Exact classification: the only totals at least four are a full cross with
zero forests, or a full star with total forest mass one. -/
theorem rigidity (h : LimitState a u) (ht : 4≤pathSum a+forestSum u) :
    (FullCross a ∧ pathSum a=4 ∧ forestSum u=0) ∨
    (FullStar a ∧ pathSum a=3 ∧ forestSum u=1) := by
  by_cases hc : ∃ i j k l,Distinct4 i j k l ∧ 2<crossSum a i j k l
  · obtain ⟨i,j,k,l,hd,hc⟩ := hc
    obtain ⟨hh,hs,hf⟩ := high_cross_exact h ht i j k l hd hc
    exact Or.inl ⟨⟨i,j,k,l,hd,hh⟩,hs,hf⟩
  · have hlow : ∀ i j k l,Distinct4 i j k l → crossSum a i j k l≤2 := by
      intro i j k l hd
      exact le_of_not_gt fun hh => hc ⟨i,j,k,l,hd,hh⟩
    have h0 := hlow 0 1 2 3 (by decide)
    have h1 := hlow 0 2 1 3 (by decide)
    have h2 := hlow 0 3 1 2 (by decide)
    dsimp [crossSum] at h0 h1 h2
    rw [h.symm 2 1] at h1
    rw [h.symm 3 1,h.symm 3 2] at h2
    have hs3 : pathSum a=3 := by
      have := h.u_sum
      dsimp [pathSum,forestSum] at *; linarith
    have hf1 : forestSum u=1 := by
      have := h.u_sum; dsimp [forestSum] at *; linarith
    have hn : ¬(∀ i j,i≠j → 0<a i j) := by
      intro hp
      have h01 := h.t3 0 1 2 3 (by decide) (hp 2 3 (by decide))
      have h02 := h.t3 0 2 1 3 (by decide) (hp 1 3 (by decide))
      have h03 := h.t3 0 3 1 2 (by decide) (hp 1 2 (by decide))
      have h12 := h.t3 1 2 0 3 (by decide) (hp 0 3 (by decide))
      have h13 := h.t3 1 3 0 2 (by decide) (hp 0 2 (by decide))
      have h23 := h.t3 2 3 0 1 (by decide) (hp 0 1 (by decide))
      change a 0 1+u 1+u 2≤1 at h01
      change a 0 2+u 0+u 2≤1 at h02
      change a 0 3+u 0+u 1≤1 at h03
      change a 1 2+u 0+u 1≤1 at h12
      change a 1 3+u 0+u 2≤1 at h13
      change a 2 3+u 1+u 2≤1 at h23
      dsimp [pathSum,forestSum] at hs3 hf1
      linarith
    push_neg at hn
    obtain ⟨k,l,hkl,hzero⟩ := hn
    have hz : a k l=0 := by have := h.nonneg k l; linarith
    obtain ⟨i,j,hd⟩ := complete_pair k l hkl
    rcases hd with ⟨_,hki,hkj,hli,hlj,hij⟩
    exact Or.inr ⟨low_cross_star h hs3 hlow i j k l
      ⟨hij,Ne.symm hki,Ne.symm hli,Ne.symm hkj,Ne.symm hlj,hkl⟩ hz,hs3,hf1⟩

end Erdos1016.ExactMaximumSupport.Shortening.FourCutLimitRigidity

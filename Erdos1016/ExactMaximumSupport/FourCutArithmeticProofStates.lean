import Erdos1016.ExactMaximum.FourCutArithmetic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! # Scalar state estimates for a four-edge cut

All hypotheses are the literal `FourState` and `LargeState` interfaces.
The finite port identities only renumber the six unordered pairs.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutArithmeticProof
open ExactMaximum

abbrev Distinct4 (i j k l : Fin 4) : Prop :=
  i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l

theorem complete_pair (i j : Fin 4) (hij : i≠j) : ∃ k l,Distinct4 i j k l := by
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide

abbrev pathSum (a : Fin 4 → Fin 4 → ℝ) : ℝ :=
  a 0 1 + a 0 2 + a 0 3 + a 1 2 + a 1 3 + a 2 3
abbrev forestSum (u : Fin 3 → ℝ) : ℝ := u 0+u 1+u 2

variable {a : Fin 4 → Fin 4 → ℝ} {u : Fin 3 → ℝ}

theorem forest_nonneg (h : FourState a u) : 0 ≤ forestSum u := by
  have := h.u_nonneg 0; have := h.u_nonneg 1; have := h.u_nonneg 2
  dsimp [forestSum]; linarith

theorem forest_le_one (h : FourState a u) : forestSum u ≤ 1 := h.u_sum

theorem coordinate_le_forest (h : FourState a u) (q : Fin 3) : u q ≤ forestSum u := by
  have := h.u_nonneg 0; have := h.u_nonneg 1; have := h.u_nonneg 2
  fin_cases q <;> dsimp [forestSum] <;> linarith

theorem pairing_comm (i j : Fin 4) : pairingOf i j = pairingOf j i := by
  simp only [pairingOf, Nat.add_comm]

theorem pairing_complement (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    pairingOf k l = pairingOf i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [pairingOf] at *

theorem forest_sum_ports (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    u (pairingOf i j)+u (pairingOf i k)+u (pairingOf i l)=forestSum u := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [pairingOf,forestSum] at * <;> ring

theorem path_sum_ports (h : FourState a u) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    a i j+a i k+a i l+a j k+a j l+a k l=pathSum a := by
  have h10 := h.symm 1 0; have h20 := h.symm 2 0; have h30 := h.symm 3 0
  have h21 := h.symm 2 1; have h31 := h.symm 3 1; have h32 := h.symm 3 2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num at * <;> dsimp [pathSum] <;> (try simp only [h10,h20,h30,h21,h31,h32]) <;> ring

/-- The contrapositive of (T3), with its strict threshold retained. -/
theorem opposite_bound (h : LargeState a u) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (hopp : 1/1000 < a k l) :
    a i j+u (pairingOf i k)+u (pairingOf i l)<1002/1000 := by
  by_contra hn
  exact (not_le_of_gt hopp) (h.t3 i j k l hij hik hil hjk hjl hkl (le_of_not_gt hn))

/-- All six opposite-pair inequalities summed once. -/
theorem all_opposite_sum (h : LargeState a u)
    (hpos : ∀ i j, i≠j → 1/1000<a i j) :
    pathSum a+4*forestSum u<6012/1000 := by
  have h01 := opposite_bound h 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 2 3 (by decide))
  have h02 := opposite_bound h 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 1 3 (by decide))
  have h03 := opposite_bound h 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 1 2 (by decide))
  have h12 := opposite_bound h 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 0 3 (by decide))
  have h13 := opposite_bound h 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 0 2 (by decide))
  have h23 := opposite_bound h 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hpos 0 1 (by decide))
  change a 0 1+u 1+u 2<1002/1000 at h01
  change a 0 2+u 0+u 2<1002/1000 at h02
  change a 0 3+u 0+u 1<1002/1000 at h03
  change a 1 2+u 0+u 1<1002/1000 at h12
  change a 1 3+u 0+u 2<1002/1000 at h13
  change a 2 3+u 1+u 2<1002/1000 at h23
  dsimp [pathSum,forestSum]
  linarith

/-- A large total with uniformly small coordinates makes every opposite pair positive. -/
theorem coordinates_pos (h : FourState a u)
    (hlow : ∀ i j, i≠j → a i j≤501/1000) (hs : 27/10<pathSum a) :
    ∀ i j, i≠j → 1/1000<a i j := by
  intro i j hij
  obtain ⟨k,l,hij,hik,hil,hjk,hjl,hkl⟩ := complete_pair i j hij
  have hs' := path_sum_ports h i j k l hij hik hil hjk hjl hkl
  have hb := hlow i k hik; have hc := hlow i l hil
  have hd := hlow j k hjk; have he := hlow j l hjl; have hf := hlow k l hkl
  dsimp [pathSum] at hs hs'
  linarith

/-- The low-state estimate needed when the small shore has rank at least two. -/
theorem low_total (h : LargeState a u)
    (hlow : ∀ i j, i≠j → a i j≤501/1000) :
    pathSum a+forestSum u≤382/100 := by
  have hF := h.u_sum
  by_cases hs : pathSum a≤27/10
  · dsimp [forestSum]; linarith
  · have hp := coordinates_pos h.toFourState hlow (lt_of_not_ge hs)
    have ht := all_opposite_sum h hp
    have h01 := hlow 0 1 (by decide); have h02 := hlow 0 2 (by decide)
    have h03 := hlow 0 3 (by decide); have h12 := hlow 1 2 (by decide)
    have h13 := hlow 1 3 (by decide); have h23 := hlow 2 3 (by decide)
    dsimp [pathSum,forestSum] at *
    linarith

/-- The low-state estimate for a rank-one small shore. -/
theorem low_half_total (h : LargeState a u)
    (hlow : ∀ i j, i≠j → a i j≤501/1000) (q : Fin 3) :
    pathSum a+(forestSum u+u q)/2≤37/10 := by
  have hF := h.u_sum
  have hq := coordinate_le_forest h.toFourState q
  by_cases hs : pathSum a≤27/10
  · dsimp [forestSum] at *; linarith
  · have hp := coordinates_pos h.toFourState hlow (lt_of_not_ge hs)
    have h01 := opposite_bound h 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 2 3 (by decide))
    have h02 := opposite_bound h 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 1 3 (by decide))
    have h03 := opposite_bound h 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 1 2 (by decide))
    have h12 := opposite_bound h 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 0 3 (by decide))
    have h13 := opposite_bound h 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 0 2 (by decide))
    have h23 := opposite_bound h 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (hp 0 1 (by decide))
    have ha01 := hlow 0 1 (by decide); have ha02 := hlow 0 2 (by decide)
    have ha03 := hlow 0 3 (by decide); have ha12 := hlow 1 2 (by decide)
    have ha13 := hlow 1 3 (by decide); have ha23 := hlow 2 3 (by decide)
    change a 0 1+u 1+u 2<1002/1000 at h01
    change a 0 2+u 0+u 2<1002/1000 at h02
    change a 0 3+u 0+u 1<1002/1000 at h03
    change a 1 2+u 0+u 1<1002/1000 at h12
    change a 1 3+u 0+u 2<1002/1000 at h13
    change a 2 3+u 1+u 2<1002/1000 at h23
    fin_cases q <;> dsimp [pathSum,forestSum] at * <;> linarith

end Erdos1016.ExactMaximumSupport.FourCutArithmeticProof

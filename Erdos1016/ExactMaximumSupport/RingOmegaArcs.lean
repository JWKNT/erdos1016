import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Literal cyclic arcs for the ring count

Indices are the actual `Fin m` tile positions. No cyclic counting or
enumeration hypothesis is part of the definitions.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.RingOmega
variable {m : ℕ}

def forwardDistance (i j : Fin m) : ℕ := (j.val+m-i.val)%m

def closedArc (i j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun v => forwardDistance i v ≤ forwardDistance i j

def squareCount (A : Finset (Fin m)) (i j : Fin m) : ℕ := (A ∩ closedArc i j).card

def partialSum (A : Finset (Fin m)) : ℕ :=
  ∑ i : Fin m, ∑ j ∈ Finset.univ.erase i, 2 ^ squareCount A i j

theorem forwardDistance_eq (i j : Fin m) :
    forwardDistance i j = if i.val ≤ j.val then j.val-i.val else j.val+m-i.val := by
  unfold forwardDistance
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val ≤ j.val
  · rw [if_pos h]
    have he : j.val+m-i.val = (j.val-i.val)+m := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h,Nat.mod_eq_of_lt (by omega)]

@[simp] theorem forwardDistance_self (i : Fin m) : forwardDistance i i = 0 := by
  simp [forwardDistance_eq]

theorem forwardDistance_injective (i : Fin m) : Function.Injective (forwardDistance i) := by
  intro j k h
  rw [forwardDistance_eq,forwardDistance_eq] at h
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  apply Fin.ext
  split_ifs at h <;> omega

theorem backwardDistance_injective (i : Fin m) :
    Function.Injective (fun j : Fin m => forwardDistance j i) := by
  intro j k h
  change forwardDistance j i = forwardDistance k i at h
  rw [forwardDistance_eq,forwardDistance_eq] at h
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  apply Fin.ext
  split_ifs at h <;> omega

theorem mem_closedArc_iff (i j v : Fin m) :
    v ∈ closedArc i j ↔
      if i.val ≤ j.val then i.val ≤ v.val ∧ v.val ≤ j.val
      else i.val ≤ v.val ∨ v.val ≤ j.val := by
  simp only [closedArc,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [forwardDistance_eq,forwardDistance_eq]
  have hi := i.isLt
  have hj := j.isLt
  have hv := v.isLt
  split_ifs <;> omega

/-- The same closed arc is a prefix in the reverse distance from its last tile. -/
theorem mem_closedArc_backward (i j v : Fin m) :
    v ∈ closedArc j i ↔ forwardDistance v i ≤ forwardDistance j i := by
  rw [mem_closedArc_iff,forwardDistance_eq,forwardDistance_eq]
  have hi := i.isLt
  have hj := j.isLt
  have hv := v.isLt
  split_ifs <;> omega

@[simp] theorem closedArc_self (i : Fin m) : closedArc i i = {i} := by
  ext v
  rw [mem_closedArc_iff,if_pos le_rfl,Finset.mem_singleton,Fin.ext_iff]
  omega

theorem arcs_cover (i j : Fin m) (hij : i ≠ j) :
    closedArc i j ∪ closedArc j i = Finset.univ := by
  ext v
  simp only [Finset.mem_union,Finset.mem_univ,iff_true,mem_closedArc_iff]
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  split_ifs <;> omega

theorem arcs_inter (i j : Fin m) (hij : i ≠ j) :
    closedArc i j ∩ closedArc j i = {i,j} := by
  ext v
  simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,mem_closedArc_iff,
    Fin.ext_iff] at ⊢
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  split_ifs <;> omega

/-- Two complementary closed arcs count each endpoint twice. -/
theorem squareCount_add_reverse (A : Finset (Fin m)) (i j : Fin m) (hij : i ≠ j) :
    squareCount A i j + squareCount A j i = A.card + (A ∩ {i,j}).card := by
  have hu : (A ∩ closedArc i j) ∪ (A ∩ closedArc j i) = A := by
    rw [← Finset.inter_union_distrib_left,arcs_cover i j hij,Finset.inter_univ]
  have hi : (A ∩ closedArc i j) ∩ (A ∩ closedArc j i) = A ∩ {i,j} := by
    rw [← arcs_inter i j hij]
    ext v
    simp only [Finset.mem_inter]
    tauto
  have hh := Finset.card_union_add_card_inter (A ∩ closedArc i j) (A ∩ closedArc j i)
  rw [hu,hi] at hh
  exact hh.symm

/-- The two orientations of a rung pair cost at most `2^a+1`. -/
theorem rung_pair_bound (A : Finset (Fin m)) (i j : Fin m)
    (hi : i ∉ A) (hj : j ∉ A) (hij : i ≠ j) :
    (2 : ℤ)^squareCount A i j + 2^squareCount A j i ≤ 2^A.card+1 := by
  have he := squareCount_add_reverse A i j hij
  have hz : A ∩ {i,j} = ∅ := by ext v; simp only [Finset.mem_inter,
    Finset.mem_insert,Finset.mem_singleton,Finset.not_mem_empty,iff_false]; aesop
  rw [hz,Finset.card_empty,add_zero] at he
  have h1 : (1 : ℤ) ≤ 2^squareCount A i j := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℤ) ≤ 2^squareCount A j i := one_le_pow₀ (by norm_num)
  have hh := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
  rw [← he,pow_add]
  nlinarith

/-- Without squares every distinct ordered pair has weight one. -/
theorem partialSum_empty : partialSum (∅ : Finset (Fin m)) = m*(m-1) := by
  classical
  unfold partialSum squareCount
  simp only [Finset.empty_inter,Finset.card_empty,pow_zero,Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,
    Nat.nsmul_eq_mul,mul_one]

end Erdos1016.ExactMaximumSupport.RingOmega

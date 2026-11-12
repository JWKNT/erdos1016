import Erdos1016.ExactMaximumSupport.RingOmegaRanks

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The cyclic weighted sum in the ring formula

The four endpoint-type sums are derived from the actual square set and
cyclic arcs. Integer arithmetic keeps all subtractions exact.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.RingOmega
variable {m : ℕ}

def orderedWeight (A : Finset (Fin m)) (i j : Fin m) : ℤ :=
  if i = j then 0 else 2 ^ squareCount A i j

def blockSum (A X Y : Finset (Fin m)) : ℤ := ∑ i ∈ X, ∑ j ∈ Y, orderedWeight A i j

theorem sum_without_diagonal {α : Type*} [DecidableEq α] (X : Finset α)
    (f : α → ℤ) (i : α) :
    (∑ j ∈ X, if i = j then 0 else f j) + (if i ∈ X then f i else 0) = ∑ j ∈ X, f j := by
  rw [← Finset.sum_ite_eq X i f,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> omega

theorem squareCount_self_of_mem (A : Finset (Fin m)) (i : Fin m) (hi : i ∈ A) :
    squareCount A i i = 1 := by
  simp [squareCount,closedArc_self,Finset.inter_singleton_of_mem hi]

theorem square_target_ordered_sum (A : Finset (Fin m)) (i : Fin m) :
    (∑ j ∈ A, orderedWeight A i j)+(if i ∈ A then 2 else 0)+2 = 2^(A.card+1) := by
  have hh := sum_without_diagonal A (fun j => (2 : ℤ)^squareCount A i j) i
  have hdiag : (if i ∈ A then (2 : ℤ)^squareCount A i i else 0) =
      if i ∈ A then 2 else 0 := by
    by_cases hi : i ∈ A
    · simp [hi,squareCount_self_of_mem A i hi]
    · simp [hi]
  change (∑ j ∈ A, orderedWeight A i j)+_ = _ at hh
  rw [hdiag] at hh
  have hsum := square_targets_sum A i
  omega

theorem square_source_ordered_sum (A : Finset (Fin m)) (i : Fin m) :
    (∑ j ∈ A, orderedWeight A j i)+(if i ∈ A then 2 else 0)+2 = 2^(A.card+1) := by
  have hh := sum_without_diagonal A (fun j => (2 : ℤ)^squareCount A j i) i
  have hdiag : (if i ∈ A then (2 : ℤ)^squareCount A i i else 0) =
      if i ∈ A then 2 else 0 := by
    by_cases hi : i ∈ A
    · simp [hi,squareCount_self_of_mem A i hi]
    · simp [hi]
  have he : (∑ j ∈ A, if i = j then (0 : ℤ) else 2 ^ squareCount A j i) =
      ∑ j ∈ A, orderedWeight A j i := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [orderedWeight,eq_comm]
  rw [he,hdiag] at hh
  have hsum := square_sources_sum A i
  omega

/-- The square-square contribution is exact, including its missing diagonal. -/
theorem square_square_sum (A : Finset (Fin m)) :
    blockSum A A A + 4*(A.card : ℤ) = (A.card : ℤ)*2^(A.card+1) := by
  have hrow (i : Fin m) (hi : i ∈ A) :
      (∑ j ∈ A, orderedWeight A i j)+4 = (2 : ℤ)^(A.card+1) := by
    have hh := square_target_ordered_sum A i
    rw [if_pos hi] at hh
    omega
  have hh := Finset.sum_congr rfl hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  change blockSum A A A + _ = _ at hh
  nlinarith

/-- From every rung, the square-target geometric sum is exact. -/
theorem rung_square_sum (A R : Finset (Fin m)) (hdis : Disjoint A R) :
    blockSum A R A + 2*(R.card : ℤ) = (R.card : ℤ)*2^(A.card+1) := by
  have hrow (i : Fin m) (hi : i ∈ R) :
      (∑ j ∈ A, orderedWeight A i j)+2 = (2 : ℤ)^(A.card+1) := by
    have hh := square_target_ordered_sum A i
    rw [if_neg (fun ha => Finset.disjoint_left.mp hdis ha hi),add_zero] at hh
    exact hh
  have hh := Finset.sum_congr rfl hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  change blockSum A R A + _ = _ at hh
  nlinarith

/-- The reverse cyclic enumeration gives the same mixed endpoint contribution. -/
theorem square_rung_sum (A R : Finset (Fin m)) (hdis : Disjoint A R) :
    blockSum A A R + 2*(R.card : ℤ) = (R.card : ℤ)*2^(A.card+1) := by
  have hrow (i : Fin m) (hi : i ∈ R) :
      (∑ j ∈ A, orderedWeight A j i)+2 = (2 : ℤ)^(A.card+1) := by
    have hh := square_source_ordered_sum A i
    rw [if_neg (fun ha => Finset.disjoint_left.mp hdis ha hi),add_zero] at hh
    exact hh
  have hh := Finset.sum_congr rfl hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  rw [Finset.sum_comm] at hh
  change blockSum A A R + _ = _ at hh
  nlinarith

theorem constant_off_diagonal_sum {α : Type*} [DecidableEq α] (R : Finset α) (C : ℤ) :
    (∑ i ∈ R, ∑ j ∈ R, if i = j then 0 else C) =
      (R.card : ℤ)*((R.card : ℤ)-1)*C := by
  have hrow (i : α) (hi : i ∈ R) :
      (∑ j ∈ R, if i = j then (0 : ℤ) else C)+C = (R.card : ℤ)*C := by
    simpa only [if_pos hi,Finset.sum_const,nsmul_eq_mul] using
      sum_without_diagonal R (fun _ => C) i
  have hh := Finset.sum_congr rfl hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  linear_combination hh

/-- Pair the two orientations of every distinct rung pair. -/
theorem rung_rung_sum_le (A R : Finset (Fin m)) (hdis : Disjoint A R) :
    2*blockSum A R R ≤ (R.card : ℤ)*((R.card : ℤ)-1)*(2^A.card+1) := by
  have hterm (i : Fin m) (hi : i ∈ R) (j : Fin m) (hj : j ∈ R) :
      orderedWeight A i j+orderedWeight A j i ≤
        if i = j then (0 : ℤ) else 2^A.card+1 := by
    by_cases hij : i = j
    · subst j
      simp [orderedWeight]
    · simpa only [orderedWeight,if_neg hij,if_neg (Ne.symm hij)] using
        rung_pair_bound A i j (fun ha => Finset.disjoint_left.mp hdis ha hi)
          (fun ha => Finset.disjoint_left.mp hdis ha hj) hij
  have hh := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  simp only [Finset.sum_add_distrib] at hh
  have he : (∑ i ∈ R, ∑ j ∈ R, orderedWeight A j i) = blockSum A R R := by
    rw [Finset.sum_comm]
    rfl
  rw [he,constant_off_diagonal_sum] at hh
  change blockSum A R R + blockSum A R R ≤ _ at hh
  omega

theorem partialSum_cast (A : Finset (Fin m)) :
    (partialSum A : ℤ) = blockSum A Finset.univ Finset.univ := by
  unfold partialSum blockSum
  simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro i _
  have hh := Finset.sum_erase_add Finset.univ (orderedWeight A i) (Finset.mem_univ i)
  have hz : orderedWeight A i i = 0 := by simp [orderedWeight]
  rw [hz,add_zero] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  rw [orderedWeight,if_neg (Ne.symm hji)]

/-- The paper's complete weighted cyclic endpoint bound. -/
theorem partialSum_bound (A : Finset (Fin m)) :
    let a := (A.card : ℤ)
    let s := ((m-A.card : ℕ) : ℤ)
    2*(partialSum A : ℤ) ≤ (2 : ℤ)^A.card*(4*a+8*s+s*(s-1))-8*a-8*s+s*(s-1) := by
  classical
  let R := Finset.univ \ A
  have hdis : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro i hi hr
    exact (Finset.mem_sdiff.mp hr).2 hi
  have hunion : A ∪ R = Finset.univ := by
    ext i
    simp only [R,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and,iff_true]
    exact Classical.em (i ∈ A)
  have hcard : R.card = m-A.card := by
    rw [Finset.card_sdiff (Finset.subset_univ A),Finset.card_univ,Fintype.card_fin]
  have htotal : (partialSum A : ℤ) = blockSum A A A + blockSum A A R +
      blockSum A R A + blockSum A R R := by
    rw [partialSum_cast]
    unfold blockSum
    rw [← hunion,Finset.sum_union hdis]
    simp_rw [Finset.sum_union hdis,Finset.sum_add_distrib]
    ring
  have hAA := square_square_sum A
  have hRA := rung_square_sum A R hdis
  have hAR := square_rung_sum A R hdis
  have hRR := rung_rung_sum_le A R hdis
  rw [hcard] at hRA hAR hRR
  dsimp only
  rw [pow_succ] at hAA hRA hAR
  nlinarith

end Erdos1016.ExactMaximumSupport.RingOmega

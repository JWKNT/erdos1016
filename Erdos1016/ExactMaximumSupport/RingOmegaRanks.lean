import Erdos1016.ExactMaximumSupport.RingOmegaArcs

set_option autoImplicit false

/-!
# Exact square-endpoint sums in cyclic order

Sorting the actual distance images proves the geometric-series enumeration;
the endpoint counts are not hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.RingOmega

theorem prefix_card {α : Type*} [LinearOrder α] (B : Finset α) (i : Fin B.card) :
    (B.filter fun b => b ≤ B.orderEmbOfFin rfl i).card = i.val+1 := by
  classical
  let e := B.orderEmbOfFin rfl
  have hs : (Finset.Iic i).map e.toEmbedding = B.filter fun b => b ≤ e i := by
    ext b
    simp only [Finset.mem_map,Finset.mem_Iic,Finset.mem_filter]
    constructor
    · rintro ⟨j,hji,rfl⟩
      exact ⟨B.orderEmbOfFin_mem rfl j,e.monotone hji⟩
    · rintro ⟨hb,hbi⟩
      have hr : b ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hb
      obtain ⟨j,rfl⟩ := hr
      exact ⟨j,e.le_iff_le.mp hbi,rfl⟩
  rw [← hs,Finset.card_map,Fin.card_Iic]

theorem geometric_prefix_sum (a : ℕ) :
    (∑ i : Fin a, (2 : ℤ)^(i.val+1))+2 = 2^(a+1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    have hp : (2 : ℤ)^(a+1+1) = 2^(a+1)*2 := pow_succ _ _
    rw [hp]
    omega

theorem sum_prefix_ranks {α : Type*} [LinearOrder α] (B : Finset α) :
    (∑ b ∈ B, (2 : ℤ)^((B.filter fun c => c ≤ b).card))+2 = 2^(B.card+1) := by
  classical
  have he : (∑ b ∈ B, (2 : ℤ)^((B.filter fun c => c ≤ b).card)) =
      ∑ i : Fin B.card, (2 : ℤ)^(i.val+1) := by
    symm
    apply Finset.sum_bij (fun i _ => B.orderEmbOfFin rfl i)
    · intro i _
      exact B.orderEmbOfFin_mem rfl i
    · intro i _ j _ h
      exact (B.orderEmbOfFin rfl).injective h
    · intro b hb
      have hr : b ∈ Set.range (B.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hb
      obtain ⟨i,hi⟩ := hr
      exact ⟨i,Finset.mem_univ _,hi⟩
    · intro i _
      rw [prefix_card]
  rw [he]
  exact geometric_prefix_sum B.card

theorem sum_injective_ranks {α : Type*} [DecidableEq α] (A : Finset α)
    (f : α → ℕ) (hf : Function.Injective f) :
    (∑ j ∈ A, (2 : ℤ)^((A.filter fun v => f v ≤ f j).card))+2 = 2^(A.card+1) := by
  classical
  let B := A.image f
  have hcard (j : α) : (A.filter fun v => f v ≤ f j).card =
      (B.filter fun b => b ≤ f j).card := by
    have he : (A.filter fun v => f v ≤ f j).image f = B.filter fun b => b ≤ f j := by
      ext b
      simp only [Finset.mem_image,Finset.mem_filter]
      constructor
      · rintro ⟨v,⟨hv,hvj⟩,rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,hvj⟩
      · rintro ⟨hb,hbj⟩
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
        exact ⟨v,⟨hv,hbj⟩,rfl⟩
    rw [← he,Finset.card_image_of_injective _ hf]
  have he : (∑ j ∈ A, (2 : ℤ)^((A.filter fun v => f v ≤ f j).card)) =
      ∑ b ∈ B, (2 : ℤ)^((B.filter fun c => c ≤ b).card) := by
    apply Finset.sum_bij (fun j _ => f j)
    · intro j hj
      exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
    · intro i _ j _ hij
      exact hf hij
    · intro b hb
      obtain ⟨j,hj,hjb⟩ := Finset.mem_image.mp hb
      exact ⟨j,hj,hjb⟩
    · intro j _
      rw [hcard]
  rw [he]
  have hh := sum_prefix_ranks B
  have hb : B.card = A.card := Finset.card_image_of_injective _ hf
  rwa [hb] at hh

variable {m : ℕ}

/-- All square targets, in the genuine forward cyclic order, have ranks `1..a`. -/
theorem square_targets_sum (A : Finset (Fin m)) (i : Fin m) :
    (∑ j ∈ A, (2 : ℤ)^squareCount A i j)+2 = 2^(A.card+1) := by
  have he (j : Fin m) : A ∩ closedArc i j =
      A.filter fun v => forwardDistance i v ≤ forwardDistance i j := by
    ext v
    simp [closedArc]
  simp only [squareCount,he]
  exact sum_injective_ranks A (forwardDistance i) (forwardDistance_injective i)

/-- The reverse cyclic order gives the same exact sum for square sources. -/
theorem square_sources_sum (A : Finset (Fin m)) (i : Fin m) :
    (∑ j ∈ A, (2 : ℤ)^squareCount A j i)+2 = 2^(A.card+1) := by
  have he (j : Fin m) : A ∩ closedArc j i =
      A.filter fun v => forwardDistance v i ≤ forwardDistance j i := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_filter,mem_closedArc_backward]
  simp only [squareCount,he]
  exact sum_injective_ranks A (fun j => forwardDistance j i) (backwardDistance_injective i)

end Erdos1016.ExactMaximumSupport.RingOmega

import Erdos1016.Probability.Finite.Counting

set_option autoImplicit false

/-!
# Uniform finite laws and linear images

These lemmas use the existing `Erdos1016.Finite.density`. In particular, the
law is uniform on the ENTIRE finite type; no empirical witness law occurs.

The last theorem bounds the cost of conditioning on the kernel of a linear
map by the cardinality of its codomain. It is proved here, not an input.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Bit := ZMod 2

@[simp] theorem bit_add_self (x : Bit) : x + x = 0 := by
  have h : (2 : Bit) = 0 := by decide
  calc
    x + x = (2 : Bit) * x := by ring
    _ = 0 := by rw [h, zero_mul]

@[simp] theorem word_add_self {ι : Type*} (x : ι → Bit) : x + x = 0 := by
  funext i
  exact bit_add_self (x i)

@[simp] theorem bit_neg (x : Bit) : -x = x := by
  calc
    -x = -x + (x + x) := by rw [bit_add_self, add_zero]
    _ = x := by abel

@[simp] theorem word_neg {ι : Type*} (x : ι → Bit) : -x = x := by
  funext i
  exact bit_neg (x i)



theorem count_eq_subtype_card {X : Type*} [Fintype X] (P : X → Prop) :
    Finite.count P = (Nat.card {x : X // P x} : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hcard : Fintype.card {x : X // P x} = (Finset.univ.filter P).card :=
    Fintype.card_of_subtype _ (by intro x; simp)
  rw [hcard]
  unfold Finite.count
  rw [← Finset.sum_filter]
  simp

/-- An inclusion of actual event states gives a count inequality. -/
theorem count_on_subtype_le {X : Type*} [Fintype X]
    (Q P : X → Prop) :
    Finite.count (fun x : {x : X // Q x} => P x.1) ≤ Finite.count P := by
  classical
  rw [count_eq_subtype_card, count_eq_subtype_card]
  have h : Nat.card {x : {x : X // Q x} // P x.1} ≤
      Nat.card {x : X // P x} := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_le_of_injective
        (fun x : {x : {x : X // Q x} // P x.1} =>
          (⟨x.1.1, x.2⟩ : {x : X // P x}))
        (by intro x y hxy; apply Subtype.ext; apply Subtype.ext
            simpa only [Subtype.mk.injEq] using hxy)
  exact_mod_cast h

/-- A dummy independent coordinate does not change a uniform event law. -/
theorem density_prod_left {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty Y] (P : X → Prop) :
    Finite.density (fun z : X × Y => P z.1) = Finite.density P := by
  classical
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Y)
  have hcount : Finite.count (fun z : X × Y => P z.1) =
      (Fintype.card Y : ℝ) * Finite.count P := by
    unfold Finite.count
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x : X, (∑ y : Y, if P x then (1 : ℝ) else 0) =
        (Fintype.card Y : ℝ) * (if P x then 1 else 0) := by
      intro x
      by_cases hx : P x <;> simp [hx]
    simp_rw [hinner]
    rw [← Finset.mul_sum]
  unfold Finite.density
  rw [hcount, Fintype.card_prod, Nat.cast_mul]
  by_cases hx : (Fintype.card X : ℝ) = 0
  · simp [hx]
  · field_simp [hx, hy] <;> ring

section Linear

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]
  [Fintype M] [Fintype N]

/-- A selected preimage is only used to construct an equivalence; the
resulting distribution does not depend on which preimages were selected. -/
def preimage (f : M →ₗ[K] N) (hf : Function.Surjective f) (y : N) : M :=
  Classical.choose (hf y)

@[simp] theorem preimage_spec (f : M →ₗ[K] N)
    (hf : Function.Surjective f) (y : N) :
    f (preimage f hf y) = y :=
  Classical.choose_spec (hf y)

/-- Exact equal-fiber decomposition for a surjective linear map. -/
def surjectiveEquivProdKer (f : M →ₗ[K] N) (hf : Function.Surjective f) :
    M ≃ N × LinearMap.ker f where
  toFun x := (f x, ⟨x - preimage f hf (f x), by simp⟩)
  invFun z := preimage f hf z.1 + z.2.1
  left_inv x := by dsimp; abel
  right_inv z := by
    rcases z with ⟨y, k⟩
    have hk : f k.1 = 0 := k.2
    apply Prod.ext
    · simp [hk]
    · apply Subtype.ext
      simp only [map_add, preimage_spec, hk, add_zero]
      abel

/-- Surjectivity plus linearity gives the uniform law, not merely full support. -/
theorem density_surjective_linear (f : M →ₗ[K] N)
    (hf : Function.Surjective f) (P : N → Prop) :
    Finite.density (fun x : M => P (f x)) = Finite.density P := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  rw [Finite.density_equiv (surjectiveEquivProdKer f hf)
    (P := fun x : M => P (f x))
    (Q := fun z : N × LinearMap.ker f => P z.1)
    (by intro x; rfl)]
  exact density_prod_left P

/-- Rank-free cardinal form of the finite linear fiber identity. -/
theorem card_eq_card_range_mul_card_ker (f : M →ₗ[K] N) :
    Fintype.card M = Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) := by
  classical
  letI : Fintype (LinearMap.range f) := Fintype.ofFinite _
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  let fr : M →ₗ[K] LinearMap.range f := f.rangeRestrict
  have hsurj : Function.Surjective fr := by
    rintro ⟨y, x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  have hker : LinearMap.ker fr = LinearMap.ker f := by
    ext x
    change (fr x = 0) ↔ f x = 0
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have he := Fintype.card_congr (surjectiveEquivProdKer fr hsurj)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, hker] using he

/-- Conditioning on linear constraints costs at most the number of possible
constraint values. Neither an empirical law nor a favorable fiber is used. -/
theorem density_kernel_le (f : M →ₗ[K] N) (P : M → Prop) :
    Finite.density (fun x : LinearMap.ker f => P x.1) ≤
      (Fintype.card N : ℝ) * Finite.density P := by
  classical
  have hcount : Finite.count (fun x : LinearMap.ker f => P x.1) ≤
      Finite.count P := count_on_subtype_le (fun x => x ∈ LinearMap.ker f) P
  have hc := card_eq_card_range_mul_card_ker f
  have hcard : (Fintype.card M : ℝ) =
      (Fintype.card (LinearMap.range f) : ℝ) *
        (Fintype.card (LinearMap.ker f) : ℝ) := by
    simpa only [Nat.card_eq_fintype_card, Nat.cast_mul] using congrArg (Nat.cast : ℕ → ℝ) hc
  have hr : (0 : ℝ) < Fintype.card (LinearMap.range f) := by
    exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card (LinearMap.ker f) := by
    exact_mod_cast Fintype.card_pos
  have hsmall : (Fintype.card (LinearMap.range f) : ℝ) ≤ Fintype.card N := by
    exact_mod_cast Fintype.card_le_of_injective
      (Subtype.val : LinearMap.range f → N) Subtype.val_injective
  calc
    Finite.density (fun x : LinearMap.ker f => P x.1)
        ≤ Finite.count P / (Fintype.card (LinearMap.ker f) : ℝ) :=
      div_le_div_of_nonneg_right hcount hk.le
    _ = (Fintype.card (LinearMap.range f) : ℝ) * Finite.density P := by
      unfold Finite.density
      rw [hcard]
      calc
        _ = (Finite.count P * (Fintype.card (LinearMap.ker f) : ℝ)⁻¹) * 1 := by ring
        _ = (Finite.count P * (Fintype.card (LinearMap.ker f) : ℝ)⁻¹) *
            ((Fintype.card (LinearMap.range f) : ℝ) *
              (Fintype.card (LinearMap.range f) : ℝ)⁻¹) := by
              rw [mul_inv_cancel₀ (ne_of_gt hr)]
        _ = _ := by ring
    _ ≤ (Fintype.card N : ℝ) * Finite.density P :=
      mul_le_mul_of_nonneg_right hsmall (Finite.density_nonneg P)

end Linear

/-- Deleting one coordinate leaves exactly `2^(c-1)` possible binary labels. -/
theorem card_drop_one (C : Type*) [Fintype C] (c₀ : C) :
    Fintype.card ({c : C // c ≠ c₀} → Bit) = 2 ^ (Fintype.card C - 1) := by
  classical
  have hc : Fintype.card {c : C // c ≠ c₀} = Fintype.card C - 1 := by
    rw [Fintype.card_of_subtype (Finset.univ.erase c₀) (by intro c; simp)]
    simp
  rw [Fintype.card_fun, hc]
  simp [Bit]

end Erdos1016.BoundaryTrace

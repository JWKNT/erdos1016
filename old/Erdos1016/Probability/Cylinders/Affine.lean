import Erdos1016.Probability.Finite.Counting

set_option autoImplicit false

/-!
# Affine cylinders in finite binary dual spaces

An affine cylinder prescribes the restriction of a point of a finite dual
space to a subspace.  The first result gives its exact uniform density.  The
pair-intersection calculation is phrased through the combined restriction to
the sum of two subspaces; compatibility means that the two assignments arise
from one assignment on that sum.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.AffineCylinders

abbrev F₂ := ZMod 2

variable {W : Type*} [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W]
  [Fintype W] [Fintype F₂]

noncomputable instance dualFintype : Fintype (Module.Dual F₂ W) := by
  classical
  exact Fintype.ofEquiv W (Basis.toDualEquiv (Basis.ofVectorSpace F₂ W))

/-- Points satisfying a prescribed linear functional assignment on `L`. -/
def Cylinder (L : Submodule F₂ W) (a : Module.Dual F₂ L) :
    Module.Dual F₂ W → Prop := fun x => L.dualRestrict x = a

/-- Uniform probability on a finite type, represented by a subtype count. -/
def probability (P : Module.Dual F₂ W → Prop) : ℝ := by
  classical
  exact (Nat.card {x : Module.Dual F₂ W // P x} : ℝ) /
    (Nat.card (Module.Dual F₂ W) : ℝ)

/-- The restriction map is onto: every assignment on a subspace extends. -/
theorem restriction_surjective (L : Submodule F₂ W) :
    Function.Surjective (L.dualRestrict : Module.Dual F₂ W →ₗ[F₂] Module.Dual F₂ L) :=
  Subspace.dualRestrict_surjective (W := L)

/-- The homogeneous kernel of restriction has the expected dimension. -/
theorem restriction_ker_finrank (L : Submodule F₂ W) :
    Module.finrank F₂ (LinearMap.ker L.dualRestrict) +
      Module.finrank F₂ L = Module.finrank F₂ W := by
  have h := LinearMap.finrank_range_add_finrank_ker L.dualRestrict
  have hrange : LinearMap.range L.dualRestrict = ⊤ :=
    LinearMap.range_eq_top.2 (restriction_surjective L)
  rw [hrange] at h
  simpa [add_comm] using h

/-- A nonempty fiber of a linear map is a translate of its kernel. -/
def fiberEquivKernel {U V : Type*} [AddCommGroup U] [Module F₂ U]
    [AddCommGroup V] [Module F₂ V] (f : U →ₗ[F₂] V) {b : V}
    (x₀ : {x : U // f x = b}) : {x : U // f x = b} ≃ LinearMap.ker f where
  toFun x := ⟨x.1 - x₀.1, by
    change f (x.1 - x₀.1) = 0
    rw [map_sub, x.2, x₀.2, sub_self]⟩
  invFun z := ⟨(z.1 : U) + x₀.1, by
    have hz : f (z.1 : U) = 0 := z.2
    rw [map_add, hz, x₀.2, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    exact sub_add_cancel x.1 x₀.1
  right_inv z := by
    apply Subtype.ext
    exact add_sub_cancel_right (z.1 : U) x₀.1

noncomputable instance fiberFintype {U V : Type*} [AddCommGroup U] [Module F₂ U]
    [AddCommGroup V] [Module F₂ V] [Fintype U] (f : U →ₗ[F₂] V) (b : V) :
    Fintype {x : U // f x = b} := by classical exact Fintype.ofFinite _

noncomputable instance kerFintype {U V : Type*} [AddCommGroup U] [Module F₂ U]
    [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ U] [Fintype U]
    (f : U →ₗ[F₂] V) : Fintype (LinearMap.ker f) := by classical exact Fintype.ofFinite _

/-- A feasible fiber of a linear map over `F₂` has `2^dim ker` elements. -/
theorem fiber_card {U V : Type*} [AddCommGroup U] [Module F₂ U]
    [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ U]
    [Fintype U] [Fintype V] (f : U →ₗ[F₂] V) {b : V}
    (x₀ : {x : U // f x = b}) :
    Fintype.card {x : U // f x = b} =
      2 ^ Module.finrank F₂ (LinearMap.ker f) := by
  rw [Fintype.card_congr (fiberEquivKernel f x₀)]
  have h := Module.natCard_eq_pow_finrank (K := F₂) (V := LinearMap.ker f)
  have h' : Nat.card (LinearMap.ker f) =
      2 ^ Module.finrank F₂ (LinearMap.ker f) := by
    simpa [F₂, Nat.card_eq_fintype_card] using h
  simpa [Nat.card_eq_fintype_card] using h'


/-- The feasible fiber cardinality in `Nat.card`, independent of any chosen
enumeration of the finite subtype. -/
theorem fiber_natCard {U V : Type*} [AddCommGroup U] [Module F₂ U]
    [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ U]
    [Fintype U] [Fintype V] (f : U →ₗ[F₂] V) {b : V}
    (x₀ : {x : U // f x = b}) :
    Nat.card {x : U // f x = b} =
      2 ^ Module.finrank F₂ (LinearMap.ker f) := by
  calc
    Nat.card {x : U // f x = b} = Nat.card (LinearMap.ker f) :=
      Nat.card_congr (fiberEquivKernel f x₀)
    _ = 2 ^ Module.finrank F₂ (LinearMap.ker f) :=
      by simpa [F₂, Nat.card_eq_fintype_card] using
        (Module.natCard_eq_pow_finrank (K := F₂) (V := LinearMap.ker f))

/-- The exact cylinder probability is the reciprocal of the number of
independent binary constraints. -/
theorem cylinder_probability (L : Submodule F₂ W) (a : Module.Dual F₂ L) :
    probability (Cylinder L a) = 1 / (2 : ℝ) ^ Module.finrank F₂ L := by
  classical
  let f := L.dualRestrict
  have hsurj : Function.Surjective f := restriction_surjective L
  obtain ⟨x₀, hx₀⟩ := hsurj a
  have hfiber := fiber_natCard f (⟨x₀, hx₀⟩ : {x : Module.Dual F₂ W // f x = a})
  have hcard : Nat.card (Module.Dual F₂ W) =
      2 ^ Module.finrank F₂ W := by
    have h := Module.natCard_eq_pow_finrank (K := F₂)
      (V := Module.Dual F₂ W)
    simpa [F₂, Subspace.dual_finrank_eq] using h
  have hdim := restriction_ker_finrank L
  have hker :
      Module.finrank F₂ (LinearMap.ker f) + Module.finrank F₂ L =
        Module.finrank F₂ W := hdim
  unfold probability Cylinder
  dsimp [f] at hfiber hker
  rw [hfiber, hcard]
  have hpow :
      (2 : ℝ) ^ Module.finrank F₂ (LinearMap.ker f) *
          (2 : ℝ) ^ Module.finrank F₂ L =
        (2 : ℝ) ^ Module.finrank F₂ W := by
    rw [← pow_add, hker]
  have hden : (2 : ℝ) ^ Module.finrank F₂ W ≠ 0 := by positivity
  have hsub : (2 : ℝ) ^ Module.finrank F₂ L ≠ 0 := by positivity
  field_simp
  nlinarith

end Erdos1016.Proof.AffineCylinders

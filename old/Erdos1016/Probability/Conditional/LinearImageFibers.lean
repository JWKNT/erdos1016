import Erdos1016.Probability.Conditional.UniformReveal

set_option autoImplicit false

/-!
# Uniform fibers of a linear map onto its image

Restricting a uniform finite vector space through a linear map gives equal-size
fibers over the image. This is the right reveal codomain for coordinate
reveals whose ambient assignment space contains infeasible values.
-/

noncomputable section

namespace Erdos1016.Proof.RangeRevealFiber

open Erdos1016.Proof.RevealedFiberProbability

variable {K Ω Y : Type*} [Field K] [Fintype Ω] [Fintype Y]
  [AddCommGroup Ω] [Module K Ω] [AddCommGroup Y] [Module K Y]

/-- Reveal the value of a linear map, with codomain restricted to its image. -/
def reveal (f : Ω →ₗ[K] Y) : Ω → LinearMap.range f :=
  fun x => ⟨f x, ⟨x, rfl⟩⟩



/-- Each fiber over an image value is an affine translate of the kernel. -/
noncomputable def fiberEquivKer (f : Ω →ₗ[K] Y) (y : LinearMap.range f) :
    fiber (reveal f) y ≃ LinearMap.ker f := by
  classical
  let x₀ := Classical.choose y.2
  have hx₀ : f x₀ = y.1 := Classical.choose_spec y.2
  exact {
    toFun := fun x => ⟨x.1 - x₀, by
      have hx : f x.1 = y.1 := by
        have h := congrArg Subtype.val x.2
        exact h
      change f (x.1 - x₀) = 0
      rw [map_sub, hx, hx₀, sub_self]⟩
    invFun := fun z => ⟨z.1 + x₀, by
      apply Subtype.ext
      change f (z.1 + x₀) = y.1
      rw [map_add, z.2, hx₀, zero_add]⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact sub_add_cancel x.1 x₀
    right_inv := fun z => by
      apply Subtype.ext
      exact add_sub_cancel_right z.1 x₀ }



/-- Fintype spelling for callers that materialize the kernel's finite instance. -/
theorem fiber_card (f : Ω →ₗ[K] Y) [Fintype (LinearMap.ker f)]
    (y : LinearMap.range f) :
    Fintype.card (fiber (reveal f) y) = Fintype.card (LinearMap.ker f) :=
  Fintype.card_congr (fiberEquivKer f y)

end Erdos1016.Proof.RangeRevealFiber

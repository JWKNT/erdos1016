import Mathlib

set_option autoImplicit false

/-!
# Binary parity spaces and complete fibers

The objects are full fibers of a linear boundary map. No connectedness is
assumed. In a graph, the kernel dimension is the cycle-space rank, including
all components and isolated vertices.
-/

noncomputable section

namespace Erdos1016

abbrev F₂ := ZMod 2
abbrev EdgeWord (E : Type*) := E → F₂

namespace Parity

variable {E V : Type*} [Fintype E] [Fintype V]

abbrev BoundaryMap := EdgeWord E →ₗ[F₂] (V → F₂)

/-- The complete parity fiber, not a selected family of witnesses. -/
def Fiber (boundary : BoundaryMap (E := E) (V := V)) (t : V → F₂) :=
  {x : EdgeWord E // boundary x = t}

instance fiberFinite (boundary : BoundaryMap (E := E) (V := V)) (t : V → F₂) :
    Finite (Fiber boundary t) := by
  unfold Fiber
  infer_instance

noncomputable instance fiberFintype
    (boundary : BoundaryMap (E := E) (V := V)) (t : V → F₂) :
    Fintype (Fiber boundary t) := Fintype.ofFinite _

/-- A witness translates a nonempty affine fiber to the homogeneous kernel. -/
def fiberEquivKernel (boundary : BoundaryMap (E := E) (V := V))
    {t : V → F₂} (x₀ : Fiber boundary t) : Fiber boundary t ≃ LinearMap.ker boundary where
  toFun x := ⟨x.1 - x₀.1, by
    change boundary (x.1 - x₀.1) = 0
    rw [map_sub, x.2, x₀.2, sub_self]⟩
  invFun z := ⟨(z.1 : EdgeWord E) + x₀.1, by
    have hz : boundary (z.1 : EdgeWord E) = 0 := z.2
    rw [map_add, hz, x₀.2, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    exact sub_add_cancel x.1 x₀.1
  right_inv z := by
    apply Subtype.ext
    exact add_sub_cancel_right (z.1 : EdgeWord E) x₀.1

/-- Exact affine denominator: every feasible parity fiber has `2^rank` words. -/
theorem fiber_natCard (boundary : BoundaryMap (E := E) (V := V))
    {t : V → F₂} (x₀ : Fiber boundary t) :
    Nat.card (Fiber boundary t) = 2 ^ Module.finrank F₂ (LinearMap.ker boundary) := by
  rw [Nat.card_congr (fiberEquivKernel boundary x₀)]
  have h := Module.natCard_eq_pow_finrank
    (K := F₂) (V := LinearMap.ker boundary)
  simpa [F₂, Nat.card_eq_fintype_card] using h







/-- For a full coordinate split, fixing the outside gives exactly the residual
parity equation. This is the set-level assertion; uniform counting is separate. -/
theorem split_equation {I O : Type*} [Fintype I] [Fintype O]
    (boundaryI : BoundaryMap (E := I) (V := V))
    (boundaryO : BoundaryMap (E := O) (V := V))
    (x : EdgeWord I) (y : EdgeWord O) (t : V → F₂) :
    boundaryI x + boundaryO y = t ↔ boundaryI x = t - boundaryO y := by
  exact eq_sub_iff_add_eq.symm

end Parity
end Erdos1016

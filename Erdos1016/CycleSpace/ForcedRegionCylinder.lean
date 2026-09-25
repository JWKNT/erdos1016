import Erdos1016.CycleSpace.NetworkRank
import Erdos1016.Boundary.Shore

set_option autoImplicit false

/-!
# Exact selected-region cylinder count in an original owner

An event prescribes every edge incident with a vertex region, including
chords and outgoing edges. A homogeneous seed witnesses feasibility. The
remaining free space is exactly the cycle space of the induced ORIGINAL
exterior. We construct the bijection explicitly.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace Network
local instance forcedRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- All physical incidences are frozen, not just the chosen cycle edges. -/
def ForcedRegion (N : Network V E) (S : Finset V)
    (z x : N.Word) : Prop :=
  ∀ e, N.src e ∈ S ∨ N.dst e ∈ S → x e = z e

namespace Exterior

variable (N : Network V E) (S : Finset V)

abbrev O := Network.Shore.outside N S

def extend : (O N S).Word →ₗ[Bit] N.Word :=
  push (Subtype.val : Network.Shore.OutsideEdge N S → E)

@[simp] theorem extend_apply_inside (x : (O N S).Word) (e : E)
    (he : N.src e ∈ S ∨ N.dst e ∈ S) : extend N S x e = 0 := by
  rw [extend, push_apply]
  apply Finset.sum_eq_zero
  intro f _
  have hne : f.1 ≠ e := by
    intro h
    subst e
    rcases he with hs | hd
    · exact f.2.1 hs
    · exact f.2.2 hd
  simp [hne]

@[simp] theorem extend_apply_outside (x : (O N S).Word)
    (e : Network.Shore.OutsideEdge N S) : extend N S x e.1 = x e := by
  rw [extend, push_apply]
  have heq (f : Network.Shore.OutsideEdge N S) : f.1 = e.1 ↔ f = e :=
    Subtype.val_injective.eq_iff
  simp only [heq]
  simp

theorem boundary_extend (x : (O N S).Word) :
    N.boundary (extend N S x) =
      push (Subtype.val : Network.Shore.OutsideVertex S → V)
        ((O N S).boundary x) := by
  change push N.src (push Subtype.val x) + push N.dst (push Subtype.val x) =
    push Subtype.val (push (O N S).src x + push (O N S).dst x)
  rw [map_add, push_comp, push_comp, push_comp, push_comp]
  rfl

/-- Extension by zero carries the entire exterior cycle space into the owner. -/
def extendCycle : (O N S).CycleSpace →ₗ[Bit] N.CycleSpace where
  toFun y := ⟨extend N S y.1, by
    change N.boundary (extend N S y.1) = 0
    rw [boundary_extend, y.2, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)

/-- A word supported outside is the literal extension of its restriction. -/
theorem extend_restrict_of_zero_incident (x : N.Word)
    (hx : ForcedRegion N S 0 x) :
    extend N S (fun e : Network.Shore.OutsideEdge N S => x e.1) = x := by
  funext e
  by_cases hs : N.src e ∈ S
  · rw [extend_apply_inside N S _ e (Or.inl hs)]
    exact (hx e (Or.inl hs)).symm
  · by_cases hd : N.dst e ∈ S
    · rw [extend_apply_inside N S _ e (Or.inr hd)]
      exact (hx e (Or.inr hd)).symm
    · exact extend_apply_outside N S _ ⟨e, hs, hd⟩

/-- No exterior solvability oracle: evenness follows from the original
boundary equation and injectivity of the vertex extension. -/
theorem restrict_even_of_zero_incident (x : N.CycleSpace)
    (hx : ForcedRegion N S 0 x.1) :
    (O N S).boundary (fun e : Network.Shore.OutsideEdge N S => x.1 e.1) = 0 := by
  have h := boundary_extend N S
    (fun e : Network.Shore.OutsideEdge N S => x.1 e.1)
  rw [extend_restrict_of_zero_incident N S x.1 hx, x.2] at h
  apply push_injective (Subtype.val : Network.Shore.OutsideVertex S → V)
    Subtype.val_injective
  simpa only [map_zero] using h.symm

/-- Exact equivalence between forced owner states and full exterior even words. -/
def forcedEquivExterior (z : N.CycleSpace) :
    {x : N.CycleSpace // ForcedRegion N S z.1 x.1} ≃ (O N S).CycleSpace where
  toFun x := ⟨(fun e => x.1.1 e.1 - z.1 e.1), by
    let w : N.CycleSpace := x.1 - z
    have hw : ForcedRegion N S 0 w.1 := by
      intro e he
      change x.1.1 e - z.1 e = 0
      rw [x.2 e he, sub_self]
    exact restrict_even_of_zero_incident N S w hw⟩
  invFun y := ⟨z + extendCycle N S y, by
    intro e he
    change z.1 e + extend N S y.1 e = z.1 e
    rw [extend_apply_inside N S y.1 e he, add_zero]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    let w : N.CycleSpace := x.1 - z
    have hw : ForcedRegion N S 0 w.1 := by
      intro e he
      change x.1.1 e - z.1 e = 0
      rw [x.2 e he, sub_self]
    have h := extend_restrict_of_zero_incident N S w.1 hw
    change z.1 + extend N S (fun e => w.1 e.1) = x.1.1
    rw [h]
    change z.1 + (x.1.1 - z.1) = x.1.1
    abel
  right_inv y := by
    apply Subtype.ext
    funext e
    change z.1 e.1 + extend N S y.1 e.1 - z.1 e.1 = y.1 e
    rw [extend_apply_outside]
    ring

end Exterior

/-- Complete, exact cylinder probability, including empty exteriors. -/
local instance forcedOutsideVertexFintype (N : Network V E) (S : Finset V) :
    Fintype (Network.Shore.OutsideVertex S) :=
  Network.Shore.outsideVertexFintype N S

local instance forcedOutsideEdgeFintype (N : Network V E) (S : Finset V) :
    Fintype (Network.Shore.OutsideEdge N S) :=
  Network.Shore.outsideEdgeFintype N S

theorem forced_region_probability (N : Network V E) (S : Finset V)
    (z : N.CycleSpace) :
    Finite.density (fun x : N.CycleSpace => ForcedRegion N S z.1 x.1) =
      (2 : ℝ) ^ networkRank (Network.Shore.outside N S) /
        (2 : ℝ) ^ networkRank N := by
  rw [Finite.density, count_eq_subtype_card]
  rw [Nat.card_congr (Exterior.forcedEquivExterior N S z)]
  rw [Nat.card_eq_fintype_card, cycleSpace_card_network, cycleSpace_card_network]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem forced_region_probability_dyadic (N : Network V E) (S : Finset V)
    (z : N.CycleSpace) :
    Finite.density (fun x : N.CycleSpace => ForcedRegion N S z.1 x.1) =
      dyadic ((networkRank (Network.Shore.outside N S) : ℤ) - networkRank N) := by
  rw [forced_region_probability, dyadic_sub, dyadic_nat, dyadic_nat]

end Erdos1016.BoundaryDecay

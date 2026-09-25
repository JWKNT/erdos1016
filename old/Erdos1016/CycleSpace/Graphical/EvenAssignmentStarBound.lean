import Erdos1016.CycleSpace.Graphical.EvenLinkAssignments

set_option autoImplicit false

/-!
# The one-coordinate obstruction in the pair-link quotient

Once a graph-specific argument identifies a triple common-star functional
with a functional on even link assignments, and shows that it vanishes on
assignments supported away from the link containing the third vertex, the
remaining dimension bound is purely linear algebra. This module proves that
generic step. It deliberately does not assert the missing graph-specific
factorization or avoidance statements.
-/

noncomputable section

namespace Erdos1016.Proof.GraphicalTripleStarBound

open Erdos1016
open Erdos1016.Proof.GraphicalAbstractLinks

abbrev F₂ := ZMod 2

variable {ι : Type*} [Fintype ι]

/-- Restriction to one coordinate, on the subspace of even assignments. -/
def evenCoordinate (k : ι) : EvenLinkAssignments (ι := ι) →ₗ[F₂] F₂ where
  toFun z := z.1 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Even link assignments whose distinguished coordinate is zero. -/
def evenAssignmentsAway (k : ι) : Submodule F₂ (EvenLinkAssignments (ι := ι)) :=
  LinearMap.ker (evenCoordinate k)

/-- The space of linear observations on even link assignments that vanish
whenever the distinguished coordinate vanishes has dimension at most one. -/
theorem finrank_dualAnnihilator_evenAssignmentsAway_le_one
    (k : ι) :
    Module.finrank F₂
      (evenAssignmentsAway (ι := ι) k).dualAnnihilator ≤ 1 := by
  let V := EvenLinkAssignments (ι := ι)
  let e := evenCoordinate (ι := ι) k
  have hrank := LinearMap.finrank_range_add_finrank_ker e
  have hrange : Module.finrank F₂ (LinearMap.range e) ≤ 1 := by
    calc
      Module.finrank F₂ (LinearMap.range e) ≤ Module.finrank F₂ (⊤ : Submodule F₂ F₂) :=
        Submodule.finrank_mono (le_top : LinearMap.range e ≤ ⊤)
      _ = 1 := by simp
  have hdim : Module.finrank F₂ V ≤
      Module.finrank F₂ (evenAssignmentsAway (ι := ι) k) + 1 := by
    change Module.finrank F₂ V ≤ Module.finrank F₂ (LinearMap.ker e) + 1
    calc
      Module.finrank F₂ V = Module.finrank F₂ (LinearMap.range e) +
          Module.finrank F₂ (LinearMap.ker e) := hrank.symm
      _ ≤ 1 + Module.finrank F₂ (LinearMap.ker e) :=
        Nat.add_le_add_right hrange _
      _ = Module.finrank F₂ (LinearMap.ker e) + 1 := by omega
  have hdual := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (evenAssignmentsAway (ι := ι) k)
  rw [← hdual] at hdim
  omega

/-- Abstract factorization step for the graph theorem. If a surjective map
has kernel equal to the first two avoiding spaces, and the image of the third
avoiding space contains all even assignments with coordinate `k` zero, then
the common annihilator has dimension at most one. -/
theorem finrank_dualAnnihilator_kerSup_le_one
    {V : Type*} [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V]
    (f : V →ₗ[F₂] EvenLinkAssignments (ι := ι))
    (hf : Function.Surjective f) (W : Submodule F₂ V) (k : ι)
    (haway : evenAssignmentsAway (ι := ι) k ≤
      LinearMap.range (f.comp W.subtype)) :
    Module.finrank F₂ ((LinearMap.ker f ⊔ W).dualAnnihilator) ≤ 1 := by
  let A := (evenAssignmentsAway (ι := ι) k).dualAnnihilator
  let g : A →ₗ[F₂] (V →ₗ[F₂] F₂) := f.dualMap.comp A.subtype
  have hsub : (LinearMap.ker f ⊔ W).dualAnnihilator ≤ LinearMap.range g := by
    intro φ hφ
    have hker : φ ∈ (LinearMap.ker f).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator φ).mpr
      intro x hx
      exact (Submodule.mem_dualAnnihilator φ).mp hφ x
        ((le_sup_left : LinearMap.ker f ≤ LinearMap.ker f ⊔ W) hx)
    have hφrange : φ ∈ LinearMap.range f.dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective f hf]
      exact hker
    obtain ⟨ψ, hψ⟩ := hφrange
    have hψaway : ψ ∈ A := by
      apply (Submodule.mem_dualAnnihilator ψ).mpr
      intro z hz
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (haway hz)
      have hzero : φ y.1 = 0 :=
        (Submodule.mem_dualAnnihilator φ).mp hφ y.1
          ((le_sup_right : W ≤ LinearMap.ker f ⊔ W) y.2)
      have hEq : φ = f.dualMap ψ := hψ.symm
      have heval := congrArg (fun q : V →ₗ[F₂] F₂ => q y.1) hEq
      have hvalue : ψ (f y.1) = 0 := by
        simpa [LinearMap.dualMap_apply] using heval.symm.trans hzero
      rw [← hy]
      exact hvalue
    refine ⟨⟨ψ, hψaway⟩, ?_⟩
    change f.dualMap (A.subtype ⟨ψ, hψaway⟩) = φ
    simpa [g, A] using hψ
  have hdim : Module.finrank F₂ ((LinearMap.ker f ⊔ W).dualAnnihilator) ≤
      Module.finrank F₂ (LinearMap.range g) := Submodule.finrank_mono hsub
  calc
    Module.finrank F₂ ((LinearMap.ker f ⊔ W).dualAnnihilator) ≤
        Module.finrank F₂ (LinearMap.range g) := hdim
    _ ≤ Module.finrank F₂ A := LinearMap.finrank_range_le g
    _ ≤ 1 := by
      simpa [A] using finrank_dualAnnihilator_evenAssignmentsAway_le_one
        (ι := ι) k

end Erdos1016.Proof.GraphicalTripleStarBound

import Erdos1016.CycleSpace.Incidence

set_option autoImplicit false

/-!
# The exact inside/cut/outside parity space

A pin here is an individually labelled CUT EDGE. It has one endpoint in the
inside network and one in the outside network. In a cubic owner with a min-2
induced core these pin edges correspond bijectively to degree-two vertices.
The probability comparison itself does not need that additional restriction.

The owner-to-local restriction is proved surjective onto the kernel of the
ACTUAL exterior-component equations. A completing exterior word is constructed
using `Network.exists_word_of_component_even`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance portedSpaceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

structure Ported {U V EI EO : Type*}
    (I : Network U EI) (O : Network V EO) (P : Type*) where
  inside : P → U
  outside : P → V

namespace Ported

variable {U V EI EO P : Type*}
  [Fintype U] [Fintype V] [Fintype EI] [Fintype EO] [Fintype P]
  {I : Network U EI} {O : Network V EO}

abbrev LocalWord (_L : Ported I O P) := (EI → Bit) × (P → Bit)
abbrev FullWord (L : Ported I O P) := L.LocalWord × (EO → Bit)

def localBoundary (L : Ported I O P) : L.LocalWord →ₗ[Bit] (U → Bit) where
  toFun w := I.boundary w.1 + push L.inside w.2
  map_add' x y := by
    change I.boundary (x.1 + y.1) + push L.inside (x.2 + y.2) =
      (I.boundary x.1 + push L.inside x.2) +
        (I.boundary y.1 + push L.inside y.2)
    rw [map_add, map_add]
    abel
  map_smul' a x := by
    change I.boundary (a • x.1) + push L.inside (a • x.2) =
      a • (I.boundary x.1 + push L.inside x.2)
    rw [map_smul, map_smul, smul_add]

abbrev LocalSpace (L : Ported I O P) := LinearMap.ker L.localBoundary

noncomputable instance localSpaceFintype (L : Ported I O P) :
    Fintype L.LocalSpace := Fintype.ofFinite _

def fullBoundary (L : Ported I O P) :
    L.FullWord →ₗ[Bit] ((U → Bit) × (V → Bit)) where
  toFun w := (L.localBoundary w.1, O.boundary w.2 + push L.outside w.1.2)
  map_add' x y := by
    apply Prod.ext
    · exact L.localBoundary.map_add x.1 y.1
    · change O.boundary (x.2 + y.2) + push L.outside (x.1.2 + y.1.2) =
        (O.boundary x.2 + push L.outside x.1.2) +
          (O.boundary y.2 + push L.outside y.1.2)
      rw [map_add, map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · exact L.localBoundary.map_smul a x.1
    · change O.boundary (a • x.2) + push L.outside (a • x.1.2) =
        a • (O.boundary x.2 + push L.outside x.1.2)
      rw [map_smul, map_smul, smul_add]

abbrev FullSpace (L : Ported I O P) := LinearMap.ker L.fullBoundary

noncomputable instance fullSpaceFintype (L : Ported I O P) :
    Fintype L.FullSpace := Fintype.ofFinite _

/-- The restriction retains the inside word AND every labelled cut coordinate. -/
def project (L : Ported I O P) : L.FullSpace →ₗ[Bit] L.LocalSpace where
  toFun w := ⟨w.1.1, congrArg Prod.fst w.2⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl

/-- Total cut parity is forced already by the internal vertex equations. -/
theorem local_cut_even (L : Ported I O P) (x : L.LocalSpace) :
    total x.1.2 = 0 := by
  have h : total (I.boundary x.1.1 + push L.inside x.1.2) = 0 := by
    simpa only [map_zero] using congrArg total x.2
  simpa only [map_add, Network.total_boundary, total_push, zero_add] using h

def exteriorDemand (L : Ported I O P) : L.LocalSpace →ₗ[Bit] (V → Bit) where
  toFun x := push L.outside x.1.2
  map_add' x y := by
    exact (push L.outside).map_add x.1.2 y.1.2
  map_smul' a x := by
    exact (push L.outside).map_smul a x.1.2

def allConstraints (L : Ported I O P) :
    L.LocalSpace →ₗ[Bit] (O.Component → Bit) :=
  O.componentBoundary.comp L.exteriorDemand

/-- The sum of all component equations is redundant, as a proved identity. -/
theorem allConstraints_total (L : Ported I O P) (x : L.LocalSpace) :
    total (L.allConstraints x) = 0 := by
  change total (push O.component (push L.outside x.1.2)) = 0
  rw [total_push, total_push]
  exact L.local_cut_even x

/-- Keep all original exterior-component equations except one. -/
def constraints (L : Ported I O P) (c₀ : O.Component) :
    L.LocalSpace →ₗ[Bit] ({c : O.Component // c ≠ c₀} → Bit) where
  toFun x c := L.allConstraints x c.1
  map_add' x y := by funext c; exact congrFun (L.allConstraints.map_add x y) c.1
  map_smul' a x := by funext c; exact congrFun (L.allConstraints.map_smul a x) c.1

theorem constraints_eq_zero_iff (L : Ported I O P) (c₀ : O.Component)
    (x : L.LocalSpace) :
    L.constraints c₀ x = 0 ↔ L.allConstraints x = 0 := by
  constructor
  · intro h
    apply eq_zero_of_total_zero_of_off_eq_zero c₀ _ (L.allConstraints_total x)
    intro c hc
    exact congrFun h ⟨c, hc⟩
  · intro h
    funext c
    exact congrFun h c.1

theorem project_satisfies_constraints (L : Ported I O P) (c₀ : O.Component)
    (w : L.FullSpace) :
    L.constraints c₀ (L.project w) = 0 := by
  apply (L.constraints_eq_zero_iff c₀ _).2
  have hout : O.boundary w.1.2 + push L.outside w.1.1.2 = 0 :=
    congrArg Prod.snd w.2
  have h := congrArg O.componentBoundary hout
  simpa only [map_add, Network.componentBoundary_boundary, zero_add, map_zero] using h

/-- The range is a concrete kernel of exterior component equations. -/
def projectToKernel (L : Ported I O P) (c₀ : O.Component) :
    L.FullSpace →ₗ[Bit] LinearMap.ker (L.constraints c₀) where
  toFun w := ⟨L.project w, L.project_satisfies_constraints c₀ w⟩
  map_add' x y := by apply Subtype.ext; exact L.project.map_add x y
  map_smul' a x := by apply Subtype.ext; exact L.project.map_smul a x

/-- Every compatible local state lifts to an actual full owner word. -/
theorem projectToKernel_surjective (L : Ported I O P) (c₀ : O.Component) :
    Function.Surjective (L.projectToKernel c₀) := by
  intro x
  have hcomp : O.componentBoundary (L.exteriorDemand x.1) = 0 :=
    (L.constraints_eq_zero_iff c₀ x.1).1 x.2
  obtain ⟨z, hz⟩ := O.exists_word_of_component_even (L.exteriorDemand x.1) hcomp
  let w : L.FullSpace := ⟨(x.1.1, z), by
    apply Prod.ext
    · exact x.1.2
    · change O.boundary z + L.exteriorDemand x.1 = 0
      rw [hz, word_add_self]⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rfl



/-- Exact law: a uniform whole word restricts uniformly to the compatible
local subspace. The equal-fiber assertion follows from the proved linear lift. -/
theorem full_density_eq_kernel_density (L : Ported I O P) (c₀ : O.Component)
    (Good : L.LocalSpace → Prop) :
    Finite.density (fun w : L.FullSpace => Good (L.project w)) =
      Finite.density (fun x : LinearMap.ker (L.constraints c₀) => Good x.1) := by
  exact density_surjective_linear (L.projectToKernel c₀)
    (L.projectToKernel_surjective c₀) (fun x => Good x.1)

/-- The complete original-exterior comparison, valid for every local event. -/
theorem full_density_le_local_density (L : Ported I O P) (c₀ : O.Component)
    (Good : L.LocalSpace → Prop) :
    Finite.density (fun w : L.FullSpace => Good (L.project w)) ≤
      (2 : ℝ) ^ (Fintype.card O.Component - 1) * Finite.density Good := by
  rw [L.full_density_eq_kernel_density c₀ Good]
  have h := density_kernel_le (L.constraints c₀) Good
  have hc := card_drop_one O.Component c₀
  simpa only [hc, Nat.cast_pow, Nat.cast_ofNat] using h





end Ported
end Erdos1016.BoundaryTrace

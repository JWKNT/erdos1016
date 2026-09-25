import Erdos1016.CycleSpace.Graphical.VertexStarSpaces
import Erdos1016.CycleSpace.CoordinateSpan
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalTripleReduction

open Erdos1016
open Erdos1016.Proof.GraphicalCommonInformation


/-- Intersection of two subspaces, written explicitly to avoid lattice
instance inference on dependent dual spaces. -/
def subspaceInter {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (A B : Submodule F V) : Submodule F V where
  carrier := {x | x ∈ A ∧ x ∈ B}
  zero_mem' := ⟨zero_mem A, zero_mem B⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨A.add_mem hx.1 hy.1, B.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro a x hx
    exact ⟨A.smul_mem a hx.1, B.smul_mem a hx.2⟩





/-- Common part of three physical vertex-star spaces. -/
def tripleStarSpace (G : PhysicalGraph) (u v w : G.Vertex) :
    Submodule F₂ (G.CycleSpace →ₗ[F₂] F₂) :=
  subspaceInter (subspaceInter (vertexStarSpace G u) (vertexStarSpace G v))
    (vertexStarSpace G w)







end Erdos1016.Proof.GraphicalTripleReduction

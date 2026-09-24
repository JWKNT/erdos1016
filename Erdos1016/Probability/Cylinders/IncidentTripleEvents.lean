import Erdos1016.Probability.Cylinders.ActiveCoordinateUniformity
import Erdos1016.CycleSpace.Graphical.VertexStarSpaces
import Erdos1016.CycleSpace.CoordinateSpan
import Erdos1016.Probability.Cylinders.TripleLowerBound

set_option autoImplicit false

/-!
# Selected incident triples as affine cylinders

This module connects a feasible all-one assignment on three edge coordinates
to its uniform probability and to the vertex-star functional space.  The
remaining graph-specific task is to produce such a feasible triple from the
Section 10 hypotheses.
-/

noncomputable section

namespace Erdos1016.Proof.ActiveTripleBridge

open Erdos1016
open Erdos1016.Proof.ActiveEdgeUniform
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.CoordinateFunctionalSpan

local notation "F₂" => ZMod 2

/-- The three selected edge observations as one linear map. -/
def tripleObservation (G : PhysicalGraph) (e : Fin 3 → G.Edge) :
    G.CycleSpace →ₗ[F₂] (Fin 3 → F₂) where
  toFun x i := ActiveEdgeUniform.edgeCoordinate G (e i) x
  map_add' x y := by
    funext i
    exact map_add (ActiveEdgeUniform.edgeCoordinate G (e i)) x y
  map_smul' a x := by
    funext i
    exact map_smul (ActiveEdgeUniform.edgeCoordinate G (e i)) a x

/-- The event that all three chosen incident edges are selected. -/
def allSelectedTriple (G : PhysicalGraph) (e : Fin 3 → G.Edge)
    (x : G.CycleSpace) : Prop :=
  tripleObservation G e x = fun _ => (1 : F₂)

/-- A feasible all-one triple has probability at least `1/8`. -/
theorem allSelectedTriple_probability_ge_one_eighth
    (G : PhysicalGraph) (e : Fin 3 → G.Edge)
    (hfeasible : ∃ x : G.CycleSpace, allSelectedTriple G e x) :
    (1 / 8 : ℝ) ≤
      Erdos1016.Proof.FinitePaleyZygmund.probability (allSelectedTriple G e) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hfeasible
  have hdim : Module.finrank F₂ (Fin 3 → F₂) ≤ 3 := by
    norm_num [Module.finrank_pi_fintype]
  have hprob := Erdos1016.Proof.SelectedTripleCylinder.eventProbability_fiber_ge_one_eighth
    (tripleObservation G e) (fun _ => (1 : F₂)) hdim ⟨x₀, by
      simpa [allSelectedTriple] using hx₀⟩
  simpa [allSelectedTriple] using hprob

/-- The linear constraints defining a triple of edges incident to `v` lie in
the vertex-star space. -/
theorem tripleObservation_dualRange_le_vertexStarSpace
    (G : PhysicalGraph) (v : G.Vertex) (e : Fin 3 → G.Edge)
    (hinc : ∀ i, G.incident (e i) v) :
    LinearMap.range (tripleObservation G e).dualMap ≤ vertexStarSpace G v := by
  classical
  rw [CoordinateFunctionalSpan.dualMap_range_eq_span_coordinates
    (F := F₂) (tripleObservation G e)]
  apply Submodule.span_le.2
  rintro f ⟨i, rfl⟩
  have heq : CoordinateFunctionalSpan.pulledCoordinate
      (tripleObservation G e) i = ActiveEdgeUniform.edgeCoordinate G (e i) := by
    ext x
    simp [CoordinateFunctionalSpan.pulledCoordinate_apply, tripleObservation,
      ActiveEdgeUniform.edgeCoordinate]
  rw [heq]
  exact edgeCoordinate_mem_vertexStarSpace G v (e i) (hinc i)

/-- The actual affine constraint space observed by a selected triple. -/
def tripleConstraintSpace (G : PhysicalGraph) (e : Fin 3 → G.Edge) :
    Submodule F₂ (Module.Dual F₂ G.CycleSpace) :=
  LinearMap.range (tripleObservation G e).dualMap

/-- The assignment on the triple's constraint space induced by a feasible
all-one cycle word. -/
def tripleCylinderAssignment (G : PhysicalGraph) (e : Fin 3 → G.Edge)
    (x₀ : G.CycleSpace) : Module.Dual F₂ (tripleConstraintSpace G e) :=
  (tripleConstraintSpace G e).dualRestrict (Module.evalEquiv F₂ G.CycleSpace x₀)

/-- The selected-triple event is precisely the corresponding affine cylinder
after identifying cycle words with points of the double dual. -/
theorem allSelectedTriple_iff_affineCylinder
    (G : PhysicalGraph) (e : Fin 3 → G.Edge)
    (x₀ : G.CycleSpace) (hx₀ : allSelectedTriple G e x₀)
    (x : G.CycleSpace) :
    allSelectedTriple G e x ↔
      Erdos1016.Proof.AffineCylinders.Cylinder (tripleConstraintSpace G e)
        (tripleCylinderAssignment G e x₀) (Module.evalEquiv F₂ G.CycleSpace x) := by
  classical
  let f := tripleObservation G e
  let L := tripleConstraintSpace G e
  change f x = (fun _ => (1 : F₂)) ↔
    Erdos1016.Proof.AffineCylinders.Cylinder L
      (L.dualRestrict (Module.evalEquiv F₂ G.CycleSpace x₀))
      (Module.evalEquiv F₂ G.CycleSpace x)
  rw [Erdos1016.Proof.AffineCylinders.Cylinder]
  constructor
  · intro hx
    apply LinearMap.ext
    intro y
    obtain ⟨ψ, hψ⟩ := y.2
    change (Module.evalEquiv F₂ G.CycleSpace x) y.1 =
      (Module.evalEquiv F₂ G.CycleSpace x₀) y.1
    rw [← hψ]
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply,
      LinearMap.dualMap_apply]
    rw [hx, hx₀]
  · intro h
    funext i
    let ψ := CoordinateFunctionalSpan.coordinate (F := F₂) i
    let y : L := ⟨f.dualMap ψ, ⟨ψ, rfl⟩⟩
    have hy := (LinearMap.ext_iff.mp h) y
    have hvalue : (Module.evalEquiv F₂ G.CycleSpace x) y.1 =
        (Module.evalEquiv F₂ G.CycleSpace x₀) y.1 := hy
    change (f x) i = 1
    have hvalue' : ψ (f x) = ψ (f x₀) := by
      simpa [Module.evalEquiv_apply, Module.Dual.eval_apply,
        LinearMap.dualMap_apply, CoordinateFunctionalSpan.coordinate_apply] using hvalue
    have hx₀i : (f x₀) i = 1 := by
      simpa [f, allSelectedTriple] using congrFun hx₀ i
    have hcoord : (f x) i = (f x₀) i := by
      simpa [ψ, CoordinateFunctionalSpan.coordinate] using hvalue'
    rw [hx₀i] at hcoord
    exact hcoord





end Erdos1016.Proof.ActiveTripleBridge

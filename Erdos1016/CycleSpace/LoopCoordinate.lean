import Erdos1016.Graph.Multigraph.BoundaryImage

set_option autoImplicit false

/-!
For a loop, the corresponding edge coordinate is a genuine nonzero
functional on the multigraph cycle space: the unit word on that loop is a
cycle and has coordinate one.
-/

noncomputable section

namespace Erdos1016.Proof

open Erdos1016

/-- Restriction of an edge coordinate to the cycle space. -/
def cycleCoordinate (G : FiniteMultiGraph) (e : G.Edge) :
    G.CycleSpace →ₗ[F₂] F₂ :=
  (LinearMap.proj e).comp (LinearMap.ker G.boundary).subtype

/-- A loop's coordinate functional on cycle space is nonzero. -/
theorem cycleCoordinate_ne_zero_of_loop
    (G : FiniteMultiGraph) (e : G.Edge) (hloop : G.src e = G.dst e) :
    cycleCoordinate G e ≠ 0 := by
  let z : G.CycleSpace := ⟨Pi.single e 1, by
    change G.boundary (Pi.single e 1) = 0
    rw [G.boundary_singleEdge, hloop]
    exact ZModModule.add_self (G.vertexUnit (G.dst e))⟩
  intro hzero
  have hz := congrArg (fun f : G.CycleSpace →ₗ[F₂] F₂ => f z) hzero
  have hval : cycleCoordinate G e z = 1 := by
    simp [cycleCoordinate, z]
  change cycleCoordinate G e z = 0 at hz
  rw [hval] at hz
  exact one_ne_zero hz

end Erdos1016.Proof

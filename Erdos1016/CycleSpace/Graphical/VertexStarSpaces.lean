import Erdos1016.Graph.Basic

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalCommonInformation

open Erdos1016

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The edge-coordinate functional restricted to the cycle space. -/
def edgeCoordinate (G : PhysicalGraph) (e : G.Edge) :
    G.CycleSpace →ₗ[F₂] F₂ where
  toFun x := x.1 e
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The space of coordinate functionals carried by the star of a vertex. -/
def vertexStarSpace (G : PhysicalGraph) (v : G.Vertex) :
    Submodule F₂ (G.CycleSpace →ₗ[F₂] F₂) :=
  Submodule.span F₂ {f | ∃ e, G.incident e v ∧ f = edgeCoordinate G e}

/-- Every edge-coordinate functional at a vertex belongs to its star space. -/
theorem edgeCoordinate_mem_vertexStarSpace (G : PhysicalGraph)
    (v : G.Vertex) (e : G.Edge) (he : G.incident e v) :
    edgeCoordinate G e ∈ vertexStarSpace G v := by
  apply Submodule.subset_span
  exact ⟨e, he, rfl⟩



/-- Edges incident to a marked vertex. -/
abbrev VertexStarEdges (G : PhysicalGraph) (v : G.Vertex) :=
  {e : G.Edge // G.incident e v}

/-- Restriction of a cycle word to the marked star. -/
def vertexStarRestriction (G : PhysicalGraph) (v : G.Vertex) :
    G.CycleSpace →ₗ[F₂] (VertexStarEdges G v → F₂) where
  toFun x e := x.1 e.1
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The subspace of cycle words that use no edge incident to `v`. -/
def cyclesAvoidingVertex (G : PhysicalGraph) (v : G.Vertex) :
    Submodule F₂ G.CycleSpace := LinearMap.ker (vertexStarRestriction G v)

/-- Evaluation at one marked-star coordinate. -/
def vertexStarEval (G : PhysicalGraph) (v : G.Vertex) (e : VertexStarEdges G v) :
    (VertexStarEdges G v → F₂) →ₗ[F₂] F₂ where
  toFun y := y e
  map_add' y z := rfl
  map_smul' a y := rfl

/-- Each incident edge coordinate is the pullback of its evaluation functional. -/
theorem edgeCoordinate_eq_dualMap_vertexStarRestriction (G : PhysicalGraph)
    (v : G.Vertex) (e : VertexStarEdges G v) :
    edgeCoordinate G e.1 =
      (vertexStarRestriction G v).dualMap (vertexStarEval G v e) := by
  ext x
  rfl

/-- A vertex star's cut-coordinate space is contained in the annihilator of
cycles avoiding that vertex. This is one direction of the restriction-kernel
characterization in the paper. -/
theorem vertexStarSpace_annihilates_avoiding (G : PhysicalGraph)
    (v : G.Vertex) (f : G.CycleSpace →ₗ[F₂] F₂)
    (hf : f ∈ vertexStarSpace G v) (x : cyclesAvoidingVertex G v) :
    f x.1 = 0 := by
  have hle : vertexStarSpace G v ≤
      LinearMap.range (vertexStarRestriction G v).dualMap := by
    apply Submodule.span_le.2
    intro g hg
    rcases hg with ⟨e, he, rfl⟩
    refine ⟨vertexStarEval G v ⟨e, he⟩, ?_⟩
    exact (edgeCoordinate_eq_dualMap_vertexStarRestriction G v ⟨e, he⟩).symm
  obtain ⟨ψ, hψ⟩ := hle hf
  have hx := x.property
  change vertexStarRestriction G v x.1 = 0 at hx
  rw [← hψ]
  simp [LinearMap.dualMap_apply, hx]

end Erdos1016.Proof.GraphicalCommonInformation

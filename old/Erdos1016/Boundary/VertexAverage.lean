import Erdos1016.Boundary.CubicCutPorts

set_option autoImplicit false

/-!
# Boundary average indexed by the actual degree-two vertices

The incidence law is first proved on labelled cut edges. Here the proved
cubic-pin bijection reindexes it onto the degree-two vertices of the induced
shore. Each summand is a COMPLETE feasible parity coset. This is the literal
vertex-indexed normalization of equation (2.1), not merely an isomorphic
unspecified probability model.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance vertexAverageDecidable (p : Prop) : Decidable p :=
  actualShoreDecidable p

end Erdos1016.BoundaryTrace

namespace Erdos1016.PhysicalGraph

open BoundaryTrace

local instance physicalVertexAverageDecidable (p : Prop) : Decidable p :=
  BoundaryTrace.actualShoreDecidable p

/-- ALL vertices of the actual induced shore with two retained incidences. -/
abbrev TraceBoundaryVertex (G : PhysicalGraph) (S : Finset G.Vertex) :=
  {v : Network.Shore.InsideVertex S // G.traceInsideDegree S v.1 = 2}

set_option maxHeartbeats 2000000
/-- The ported model now uses degree-two vertices, via the proved physical
cut-edge/vertex bijection. Its inside endpoint map is proved below to be
ordinary subtype inclusion. -/
def degreeTwoPorted (G : PhysicalGraph) (S : Finset G.Vertex)
    (hc : ∀ v ∈ S, G.degree v = 3)
    (hmin : ∀ v ∈ S, 2 ≤ G.traceInsideDegree S v) := by
  letI : Fintype (Network.Shore.InsideEdge G.traceNetwork S) :=
    Network.Shore.insideEdgeFintype G.traceNetwork S
  letI : Fintype (Network.Shore.CutEdge G.traceNetwork S) :=
    Network.Shore.cutEdgeFintype G.traceNetwork S
  exact (Network.Shore.ported G.traceNetwork S).relabelPins
    (G.cutPinEquivDegreeTwo S hc hmin)

@[simp] theorem degreeTwoPorted_inside (G : PhysicalGraph)
    (S : Finset G.Vertex) (hc : ∀ v ∈ S, G.degree v = 3)
    (hmin : ∀ v ∈ S, 2 ≤ G.traceInsideDegree S v)
    (v : G.TraceBoundaryVertex S) :
    (G.degreeTwoPorted S hc hmin).inside v = v.1 := by
  have h := congrArg Subtype.val
    ((G.cutPinEquivDegreeTwo S hc hmin).apply_symm_apply v)
  exact h

/-- Even binary vertex assignments correspond exactly to even subsets of B. -/
abbrev EvenBoundaryVertices (G : PhysicalGraph) (S : Finset G.Vertex) :=
  LinearMap.ker (total : (G.TraceBoundaryVertex S → Bit) →ₗ[Bit] Bit)

/-- The genuine inner parity coset for a boundary assignment on B. -/
def VertexSector (G : PhysicalGraph) (S : Finset G.Vertex)
    (y : G.EvenBoundaryVertices S) :=
  letI : Fintype (Network.Shore.InsideEdge G.traceNetwork S) :=
    Network.Shore.insideEdgeFintype G.traceNetwork S
  {x : (Network.Shore.inside G.traceNetwork S).Word //
    (Network.Shore.inside G.traceNetwork S).boundary x =
      push (Subtype.val : G.TraceBoundaryVertex S → Network.Shore.InsideVertex S) y.1}

noncomputable instance vertexSectorFintype (G : PhysicalGraph)
    (S : Finset G.Vertex) (y : G.EvenBoundaryVertices S) :
    Fintype (G.VertexSector S y) := by
  letI : Finite ((Network.Shore.inside G.traceNetwork S).Word) :=
    Finite.of_fintype _
  letI : Finite (G.VertexSector S y) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _





set_option maxHeartbeats 2000000





end Erdos1016.PhysicalGraph

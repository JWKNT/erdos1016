import Erdos1016.CycleSpace.Graphical.MultigraphCutFunctionals

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalActualCutTripleQuotientPackage

open Erdos1016
open Erdos1016.Proof.GraphicalActualCutMultigraphBridge
open Erdos1016.Proof.ActualCutPairProbability
open Erdos1016.Proof.GraphicalTripleReduction

local notation "𝔽" => ZMod 2

/-- The exact data needed to transfer a three-star bound from a contracted
finite multigraph to three physical cut-coordinate spaces. The construction
of this package from three connected physical regions is the remaining
combinatorial task: the edge labels must be precisely the edges crossing
between contraction fibers, and restriction of cycles must be onto. -/
structure Data (G : PhysicalGraph) (M : FiniteMultiGraph)
    (U V W : Finset G.Vertex) where
  edgeMap : M.Edge → G.Edge
  cycleRestriction : ∀ x : G.CycleSpace,
    M.boundary (restrictWord M edgeMap x.1) = 0
  surjective : Function.Surjective (restrictCycles G M edgeMap cycleRestriction)
  u : M.Vertex
  v : M.Vertex
  w : M.Vertex
  Uincident : ∀ e : M.Edge,
    (M.src e = u ∨ M.dst e = u) ↔ edgeMap e ∈ G.cutEdges U
  Ucovered : ∀ a : G.Edge, a ∈ G.cutEdges U → ∃ e : M.Edge,
    edgeMap e = a
  Vinc : ∀ e : M.Edge,
    (M.src e = v ∨ M.dst e = v) ↔ edgeMap e ∈ G.cutEdges V
  Vcovered : ∀ a : G.Edge, a ∈ G.cutEdges V → ∃ e : M.Edge,
    edgeMap e = a
  Winc : ∀ e : M.Edge,
    (M.src e = w ∨ M.dst e = w) ↔ edgeMap e ∈ G.cutEdges W
  Wcovered : ∀ a : G.Edge, a ∈ G.cutEdges W → ∃ e : M.Edge,
    edgeMap e = a

/-- Once the quotient has been constructed and its three-star intersection
has rank at most one, the actual cut spaces inherit that bound. -/
theorem actualCutTripleIntersection_finrank_le_one
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (U V W : Finset G.Vertex) (D : Data G M U V W)
    (hrank : Module.finrank 𝔽
      (multiTripleStarSpace M D.u D.v D.w) ≤ 1) :
    Module.finrank 𝔽
      (subspaceInter (subspaceInter (cutConstraintSpace G U)
        (cutConstraintSpace G V)) (cutConstraintSpace G W)) ≤ 1 := by
  exact actualCutTripleIntersection_finrank_le_one_of_multigraph_quotient
    G M D.edgeMap D.cycleRestriction D.surjective U V W D.u D.v D.w
    D.Uincident D.Ucovered D.Vinc D.Vcovered D.Winc D.Wcovered hrank

end Erdos1016.Proof.PhysicalActualCutTripleQuotientPackage

end

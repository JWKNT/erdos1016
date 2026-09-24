import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# Actual edges, actual cuts, and the fixed-threshold inverse

No contraction, minor model, or selected-edge cut is substituted for an
actual host cut. The packing inverse below is a proposition, not a theorem.
-/

noncomputable section

namespace Erdos1016
namespace PhysicalGraph

/-- Individually labelled host edges crossing a vertex shore. -/
def cutEdges (G : PhysicalGraph) (U : Finset G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (G.src e ∈ U ∧ G.dst e ∉ U) ∨ (G.src e ∉ U ∧ G.dst e ∈ U)

def actualCut (G : PhysicalGraph) (U : Finset G.Vertex) : ℕ :=
  (G.cutEdges U).card

@[simp] lemma actualCut_empty (G : PhysicalGraph) : G.actualCut ∅ = 0 := by
  simp [actualCut, cutEdges]

@[simp] lemma actualCut_univ (G : PhysicalGraph) :
    G.actualCut Finset.univ = 0 := by
  simp [actualCut, cutEdges]



/-- Connected, cyclic, induced, with its cut taken in the original host. -/
def IsCyclicRegion (G : PhysicalGraph) (U : Finset G.Vertex) : Prop :=
  (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected ∧
  ¬ (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsAcyclic



end PhysicalGraph



/-- A literal edge subgraph with injections into the host's vertices and edges.
Orientation is inherited, so no physical labels are identified. -/
structure ActualSubgraph (H : PhysicalGraph) where
  graph : PhysicalGraph
  vertexMap : graph.Vertex ↪ H.Vertex
  edgeMap : graph.Edge ↪ H.Edge
  src_commutes : ∀ e, H.src (edgeMap e) = vertexMap (graph.src e)
  dst_commutes : ∀ e, H.dst (edgeMap e) = vertexMap (graph.dst e)

namespace ActualSubgraph

def restrict {H : PhysicalGraph} (D : ActualSubgraph H) (x : H.Word) : D.graph.Word :=
  fun e => x (D.edgeMap e)



@[simp] lemma restrict_zero {H : PhysicalGraph} (D : ActualSubgraph H) :
    D.restrict 0 = 0 := rfl



end ActualSubgraph
end Erdos1016

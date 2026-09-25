import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false

/-!
# Connected components of finite labelled multigraphs

The simple graph below forgets edge labels but retains adjacency whenever at
least one labelled edge joins the two vertices. Thus loops and parallel edges
remain in the multigraph's boundary/cycle space, while connectedness has its
usual vertex-level meaning.
-/

namespace Erdos1016
namespace FiniteMultiGraph

/-- The simple graph underlying a labelled multigraph. -/
def toSimpleGraph (G : FiniteMultiGraph) : SimpleGraph G.Vertex where
  Adj u v := u ≠ v ∧ ∃ e : G.Edge,
    (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
  symm := by
    intro u v h
    rcases h with ⟨hne, e, h | h⟩
    · exact ⟨hne.symm, e, Or.inr h⟩
    · exact ⟨hne.symm, e, Or.inl h⟩
  loopless := by
    intro v h
    exact h.1 rfl

abbrev ConnectedComponent (G : FiniteMultiGraph) := G.toSimpleGraph.ConnectedComponent

/-- The component containing a vertex. -/
def componentOf (G : FiniteMultiGraph) (v : G.Vertex) : G.ConnectedComponent :=
  G.toSimpleGraph.connectedComponentMk v

theorem componentOf_src_eq_dst (G : FiniteMultiGraph) (e : G.Edge) :
    G.componentOf (G.src e) = G.componentOf (G.dst e) := by
  by_cases h : G.src e = G.dst e
  · simpa [h]
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩







noncomputable instance connectedComponentFintype (G : FiniteMultiGraph) :
    Fintype G.ConnectedComponent := Fintype.ofFinite _

noncomputable def componentCount (G : FiniteMultiGraph) : ℕ :=
  Fintype.card G.ConnectedComponent



/-- Euler's formula follows once the incidence image has codimension equal to
the number of connected components. This isolates the remaining linear
algebraic bridge for the multigraph model. -/
theorem euler_of_boundaryRank_add_componentCount
    (G : FiniteMultiGraph)
    (h : G.boundaryRank + G.componentCount = G.vertexCount) :
    G.cycleRank + G.vertexCount = G.edgeCount + G.componentCount := by
  have hnull := G.cycleRank_add_boundaryRank
  omega

end FiniteMultiGraph
end Erdos1016

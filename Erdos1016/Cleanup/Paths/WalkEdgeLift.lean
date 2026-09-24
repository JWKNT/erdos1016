import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Erdos1016.CycleSpace.Graphical.LinkPairWitnesses

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.WalkEdgeLift

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.GraphicalLinkPairWitnesses

/-- The physical edge labels selected step-by-step along a simple-graph walk. -/
def liftedEdges (G : PhysicalGraph) {u v : G.Vertex} :
    G.toSimpleGraph.Walk u v → List G.Edge
  | .nil => []
  | .cons h p => physicalEdgeOfAdj G h :: liftedEdges G p

theorem liftedEdges_length (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) : (liftedEdges G p).length = p.length := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih => simp [liftedEdges, ih]

/-- The physical label chosen for a nonempty walk's first adjacency has the
correct endpoint pair. -/
theorem liftedEdges_head_spec (G : PhysicalGraph) {u v w : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) (p : G.toSimpleGraph.Walk v w) :
    (G.src (physicalEdgeOfAdj G h) = u ∧ G.dst (physicalEdgeOfAdj G h) = v) ∨
    (G.dst (physicalEdgeOfAdj G h) = u ∧ G.src (physicalEdgeOfAdj G h) = v) := by
  rcases physicalEdgeOfAdj_spec G h with hspec | hspec
  · exact Or.inl hspec
  · exact Or.inr ⟨hspec.2, hspec.1⟩

/-- Forgetting the physical label and retaining its unordered endpoint pair
recovers exactly the edge list of the underlying simple-graph walk. -/
theorem map_liftedEdges_eq_walk_edges (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    List.map (fun e : G.Edge => s(G.src e, G.dst e)) (liftedEdges G p) =
      p.edges := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
      simp only [liftedEdges, List.map_cons, SimpleGraph.Walk.edges_cons, ih]
      have hspec := physicalEdgeOfAdj_spec G h
      rcases hspec with hspec | hspec
      · simp [hspec]
      · simp [hspec, Sym2.eq_swap]

/-- The physical edge labels lifted from a path are distinct.  This follows
from simplicity of the physical graph: endpoint pairs determine labels. -/
theorem liftedEdges_nodup_of_isPath (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (hp : p.IsPath) :
    (liftedEdges G p).Nodup := by
  classical
  let pair : G.Edge → Sym2 G.Vertex := fun e => s(G.src e, G.dst e)
  have hpair : Function.Injective pair := by
    intro e f hef
    have hends := (Sym2.eq_iff.mp hef)
    apply G.simple e f
    rcases hends with hends | hends
    · exact Or.inl hends
    · exact Or.inr hends
  have hmap : List.map pair (liftedEdges G p) = p.edges := by
    simpa [pair] using map_liftedEdges_eq_walk_edges G p
  rw [← List.nodup_map_iff hpair, hmap]
  exact hp.isTrail.edges_nodup



end Erdos1016.Proof.WalkEdgeLift

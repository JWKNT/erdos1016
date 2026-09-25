import Erdos1016.Graph.Multigraph.InducedSimpleDegrees
import Erdos1016.Graph.ExteriorForestRegions

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

/-- Adjacency is preserved in both directions by the retained vertex map. -/
theorem adj_vertex_iff (u v : (graph G R hloop hsimple).Vertex) :
    (graph G R hloop hsimple).toSimpleGraph.Adj u v ↔
      G.toSimpleGraph.Adj (vertex G R hloop hsimple u) (vertex G R hloop hsimple v) := by
  simpa only [Equiv.apply_symm_apply, vertex] using
    graph_adj_iff G R hloop hsimple ((vertexEquiv G R).symm u) ((vertexEquiv G R).symm v)

/-- Relabeling an actual retained region commutes with taking its induced graph. -/
def regionGraphIso (A : Finset G.Vertex) (hAR : A ⊆ R) :
    G.toSimpleGraph.induce (↑A : Set G.Vertex) ≃g
      (graph G R hloop hsimple).toSimpleGraph.induce
        (↑(region G R hloop hsimple A) : Set (graph G R hloop hsimple).Vertex) where
  toEquiv := (regionEquiv G R hloop hsimple A hAR).symm
  map_rel_iff' := by
    intro u v
    change (graph G R hloop hsimple).toSimpleGraph.Adj
      (vertexEquiv G R ⟨u.1, hAR u.2⟩) (vertexEquiv G R ⟨v.1, hAR v.2⟩) ↔ _
    exact graph_adj_iff G R hloop hsimple _ _

/-- A labelled forest component remains an actual induced tree after the
finite relabeling. No connectedness or forest certificate is supplied for J. -/
theorem component_induced_tree (U : Finset G.Vertex)
    (c : ExteriorComponents.Component G U)
    (hcR : ExteriorComponents.vertices G U c ⊆ R)
    (hforest : G.IsForestWord (G.restrictEdges
      (G.internalEdges (ExteriorComponents.vertices G U c)) (fun _ => 1))) :
    ((graph G R hloop hsimple).toSimpleGraph.induce
      (↑(region G R hloop hsimple (ExteriorComponents.vertices G U c)) :
        Set (graph G R hloop hsimple).Vertex)).IsTree := by
  let iso := regionGraphIso G R hloop hsimple (ExteriorComponents.vertices G U c) hcR
  refine ⟨?_, ?_⟩
  · exact iso.connected_iff.mp (ExteriorComponents.vertices_connected G U c)
  · have ha := ExteriorComponents.internal_forest_induced_acyclic G _ hforest
    intro v p hp
    exact ha (p.map iso.symm.toHom)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective iso.symm.injective).mpr hp)

/-- Actual cubic incidence degrees on a retained exterior component give
ordinary simple-graph cubic degrees there. -/
theorem component_simple_degree_eq (U : Finset G.Vertex)
    (c : ExteriorComponents.Component G U)
    (hcR : ExteriorComponents.vertices G U c ⊆ R)
    (hout : ∀ v, v ∉ U → v ∈ R)
    (w : (graph G R hloop hsimple).Vertex)
    (hw : w ∈ region G R hloop hsimple (ExteriorComponents.vertices G U c)) :
    (graph G R hloop hsimple).toSimpleGraph.degree w =
      G.degree (vertex G R hloop hsimple w) := by
  rw [graph_degree_eq_physical]
  simpa only [Equiv.apply_symm_apply, vertex] using component_degree_eq
    G R hloop hsimple U c hcR hout ((vertexEquiv G R).symm w)
      ((mem_region G R hloop hsimple _ w).mp hw)

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization

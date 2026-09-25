import Erdos1016.Graph.Basic
import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false

/-! The actual labelled induced subgraph of a multigraph is realized as a
 PhysicalGraph once its retained edges have no loops or parallel copies.
 Vertices and edges are only reindexed by finite equivalences. -/
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)

abbrev RetainedVertex := {v : G.Vertex // v ∈ R}
abbrev RetainedEdge := {e : G.Edge // e ∈ G.internalEdges R}

def vertexEquiv : RetainedVertex G R ≃ Fin (Fintype.card (RetainedVertex G R)) :=
  Fintype.equivFin _
def edgeEquiv : RetainedEdge G R ≃ Fin (Fintype.card (RetainedEdge G R)) :=
  Fintype.equivFin _

theorem source_mem (e : RetainedEdge G R) : G.src e.1 ∈ R :=
  (Finset.mem_filter.mp e.2).2.1

theorem target_mem (e : RetainedEdge G R) : G.dst e.1 ∈ R :=
  (Finset.mem_filter.mp e.2).2.2

variable
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

def graph : PhysicalGraph where
  vertexCount := Fintype.card (RetainedVertex G R)
  edgeCount := Fintype.card (RetainedEdge G R)
  src e := vertexEquiv G R ⟨G.src ((edgeEquiv G R).symm e).1, source_mem G R _⟩
  dst e := vertexEquiv G R ⟨G.dst ((edgeEquiv G R).symm e).1, target_mem G R _⟩
  noLoops e heq := hloop _ ((edgeEquiv G R).symm e).2
    (congrArg Subtype.val ((vertexEquiv G R).injective heq))
  simple e f heq := by
    apply (edgeEquiv G R).symm.injective
    apply Subtype.ext
    apply hsimple _ ((edgeEquiv G R).symm e).2 _ ((edgeEquiv G R).symm f).2
    rcases heq with heq | heq
    · exact Or.inl ⟨congrArg Subtype.val ((vertexEquiv G R).injective heq.1),
        congrArg Subtype.val ((vertexEquiv G R).injective heq.2)⟩
    · exact Or.inr ⟨congrArg Subtype.val ((vertexEquiv G R).injective heq.1),
        congrArg Subtype.val ((vertexEquiv G R).injective heq.2)⟩

@[simp] theorem graph_vertexCount : (graph G R hloop hsimple).vertexCount = R.card := by
  simp [graph, RetainedVertex, Fintype.card_coe]

@[simp] theorem graph_edgeCount : (graph G R hloop hsimple).edgeCount = (G.internalEdges R).card := by
  simp [graph, RetainedEdge, Fintype.card_coe]

@[simp] theorem graph_src (e : RetainedEdge G R) :
    (graph G R hloop hsimple).src (edgeEquiv G R e) =
      vertexEquiv G R ⟨G.src e.1, source_mem G R e⟩ := by simp [graph]

@[simp] theorem graph_dst (e : RetainedEdge G R) :
    (graph G R hloop hsimple).dst (edgeEquiv G R e) =
      vertexEquiv G R ⟨G.dst e.1, target_mem G R e⟩ := by simp [graph]

/-- Original vertex and edge labels of the reindexed induced graph. -/
def vertex (v : (graph G R hloop hsimple).Vertex) : G.Vertex :=
  ((vertexEquiv G R).symm v).1

def edge (e : (graph G R hloop hsimple).Edge) : G.Edge :=
  ((edgeEquiv G R).symm e).1

theorem vertex_injective : Function.Injective (vertex G R hloop hsimple) := by
  intro u v h
  exact (vertexEquiv G R).symm.injective (Subtype.ext h)

theorem edge_injective : Function.Injective (edge G R hloop hsimple) := by
  intro e f h
  exact (edgeEquiv G R).symm.injective (Subtype.ext h)

@[simp] theorem vertex_src (e : (graph G R hloop hsimple).Edge) :
    vertex G R hloop hsimple ((graph G R hloop hsimple).src e) =
      G.src (edge G R hloop hsimple e) := by simp [vertex, graph, edge]

@[simp] theorem vertex_dst (e : (graph G R hloop hsimple).Edge) :
    vertex G R hloop hsimple ((graph G R hloop hsimple).dst e) =
      G.dst (edge G R hloop hsimple e) := by simp [vertex, graph, edge]

theorem graph_adj_iff (u v : RetainedVertex G R) :
    (graph G R hloop hsimple).toSimpleGraph.Adj (vertexEquiv G R u) (vertexEquiv G R v) ↔
      G.toSimpleGraph.Adj u.1 v.1 := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · have hs := congrArg (vertex G R hloop hsimple) h.1
      have ht := congrArg (vertex G R hloop hsimple) h.2
      simp only [vertex, graph, edge, Equiv.symm_apply_apply] at hs ht
      refine ⟨?_, edge G R hloop hsimple e, Or.inl ⟨hs, ht⟩⟩
      intro huv
      exact hloop _ ((edgeEquiv G R).symm e).2 (hs.trans (huv.trans ht.symm))
    · have hs := congrArg (vertex G R hloop hsimple) h.1
      have ht := congrArg (vertex G R hloop hsimple) h.2
      simp only [vertex, graph, edge, Equiv.symm_apply_apply] at hs ht
      refine ⟨?_, edge G R hloop hsimple e, Or.inr ⟨hs, ht⟩⟩
      intro huv
      exact hloop _ ((edgeEquiv G R).symm e).2 (hs.trans (huv.symm.trans ht.symm))
  · rintro ⟨hne, e, he⟩
    have hemem : e ∈ G.internalEdges R := by
      rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp [internalEdges, hs, ht, u.2, v.2]
    refine ⟨edgeEquiv G R ⟨e, hemem⟩, one_ne_zero, ?_⟩
    rw [graph_src, graph_dst]
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl ⟨congrArg (vertexEquiv G R) (Subtype.ext hs),
        congrArg (vertexEquiv G R) (Subtype.ext ht)⟩
    · exact Or.inr ⟨congrArg (vertexEquiv G R) (Subtype.ext hs),
        congrArg (vertexEquiv G R) (Subtype.ext ht)⟩

/-- Exact graph isomorphism from the usual induced graph to its Fin-labelled
 physical realization. -/
def graphIso : G.toSimpleGraph.induce (↑R : Set G.Vertex) ≃g
    (graph G R hloop hsimple).toSimpleGraph where
  toEquiv := vertexEquiv G R
  map_rel_iff' := by intro u v; exact graph_adj_iff G R hloop hsimple u v

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization

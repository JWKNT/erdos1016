import Erdos1016.Cycles.Geometry.DirectJoiningEdges
import Erdos1016.Graph.Multigraph.InducedSimpleRegions
import Erdos1016.Graph.Multigraph.DirectRegionEdges

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
open Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.Proof.ShortJoiningPaths
local instance retainedDirectEdgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

/-- Ambient vertex support of a walk in the retained physical graph. -/
def walkRegion {a b : (graph G R hloop hsimple).Vertex}
    (C : (graph G R hloop hsimple).toSimpleGraph.Walk a b) : Finset G.Vertex :=
  C.support.toFinset.image (vertex G R hloop hsimple)

theorem walkRegion_subset {a b : (graph G R hloop hsimple).Vertex}
    (C : (graph G R hloop hsimple).toSimpleGraph.Walk a b) :
    walkRegion G R hloop hsimple C ⊆ R := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact vertex_mem G R hloop hsimple u

/-- Direct ambient physical labels inject into the ordinary direct joining
edges of J. Retained simplicity prevents any lost parallel multiplicity. -/
theorem directLabels_card_le_directJoiningEdges
    {a b : (graph G R hloop hsimple).Vertex}
    (C : (graph G R hloop hsimple).toSimpleGraph.Walk a a)
    (C' : (graph G R hloop hsimple).toSimpleGraph.Walk b b) :
    (G.directLabels (walkRegion G R hloop hsimple C) (walkRegion G R hloop hsimple C')).card ≤
      Fintype.card (DirectJoiningEdges C C') := by
  let E := G.directLabels (walkRegion G R hloop hsimple C) (walkRegion G R hloop hsimple C')
  have hret : E ⊆ G.internalEdges R := G.directLabels_internal _ _ _
    (walkRegion_subset G R hloop hsimple C) (walkRegion_subset G R hloop hsimple C')
  have hex (e : E) : ∃ uv : DirectJoiningEdges C C',
      (G.src e = vertex G R hloop hsimple uv.1.1 ∧ G.dst e = vertex G R hloop hsimple uv.1.2) ∨
      (G.src e = vertex G R hloop hsimple uv.1.2 ∧ G.dst e = vertex G R hloop hsimple uv.1.1) := by
    have he := (G.mem_directLabels _ _ e.1).mp e.2
    rcases he with he | he
    · obtain ⟨u, hu, hsu⟩ := Finset.mem_image.mp he.1
      obtain ⟨v, hv, htv⟩ := Finset.mem_image.mp he.2
      have ha : (graph G R hloop hsimple).toSimpleGraph.Adj u v := by
        rw [adj_vertex_iff]
        refine ⟨?_, e, Or.inl ⟨hsu.symm, htv.symm⟩⟩
        simpa only [hsu, htv] using hloop e (hret e.2)
      exact ⟨⟨(u, v), List.mem_toFinset.mp hu, List.mem_toFinset.mp hv, ha⟩,
        Or.inl ⟨hsu.symm, htv.symm⟩⟩
    · obtain ⟨v, hv, hsv⟩ := Finset.mem_image.mp he.1
      obtain ⟨u, hu, htu⟩ := Finset.mem_image.mp he.2
      have ha : (graph G R hloop hsimple).toSimpleGraph.Adj u v := by
        rw [adj_vertex_iff]
        refine ⟨?_, e, Or.inr ⟨hsv.symm, htu.symm⟩⟩
        simpa only [htu, hsv, ne_comm] using hloop e (hret e.2)
      exact ⟨⟨(u, v), List.mem_toFinset.mp hu, List.mem_toFinset.mp hv, ha⟩,
        Or.inr ⟨hsv.symm, htu.symm⟩⟩
  let f : E → DirectJoiningEdges C C' := fun e => Classical.choose (hex e)
  have hinj : Function.Injective f := by
    intro e e' he
    have h := Classical.choose_spec (hex e)
    have h' := Classical.choose_spec (hex e')
    change _ = _ at he
    change (G.src e = vertex G R hloop hsimple (f e).1.1 ∧
      G.dst e = vertex G R hloop hsimple (f e).1.2) ∨
      (G.src e = vertex G R hloop hsimple (f e).1.2 ∧
      G.dst e = vertex G R hloop hsimple (f e).1.1) at h
    change (G.src e' = vertex G R hloop hsimple (f e').1.1 ∧
      G.dst e' = vertex G R hloop hsimple (f e').1.2) ∨
      (G.src e' = vertex G R hloop hsimple (f e').1.2 ∧
      G.dst e' = vertex G R hloop hsimple (f e').1.1) at h'
    rw [he] at h
    apply Subtype.ext
    apply hsimple e (hret e.2) e' (hret e'.2)
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Or.inl ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩
    · exact Or.inr ⟨h.1.trans h'.2.symm, h.2.trans h'.1.symm⟩
    · exact Or.inr ⟨h.1.trans h'.2.symm, h.2.trans h'.1.symm⟩
    · exact Or.inl ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- The direct-label contribution obeys the same block bound as the small
exterior trees. -/
theorem directLabels_card_le_length_blocks
    {a b : (graph G R hloop hsimple).Vertex}
    (C : (graph G R hloop hsimple).toSimpleGraph.Walk a a)
    (C' : (graph G R hloop hsimple).toSimpleGraph.Walk b b) (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hmax : ∀ v, G.degree v ≤ 3) (D q : ℕ) (hq : 0 < q)
    (hg : GirthGreater (graph G R hloop hsimple).toSimpleGraph D)
    (hbudget : 2 * (1 + 2 * q) ≤ D) :
    (G.directLabels (walkRegion G R hloop hsimple C) (walkRegion G R hloop hsimple C')).card ≤
      (C.length / q + 1) * (C'.length / q + 1) := by
  apply (directLabels_card_le_directJoiningEdges G R hloop hsimple C C').trans
  apply card_direct_joining_edges_le_length_blocks C C' hC hdisjoint _ D q hq hg hbudget
  intro v hv
  rw [graph_degree_eq_physical]
  have h := degree_le G R hloop hsimple ((vertexEquiv G R).symm v)
  simpa only [Equiv.apply_symm_apply] using h.trans (hmax _)

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization

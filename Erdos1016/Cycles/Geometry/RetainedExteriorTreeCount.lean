import Erdos1016.Graph.Multigraph.InducedSimpleRegions
import Erdos1016.Graph.PhysicalCutIncidences
import Erdos1016.Cycles.Geometry.ExteriorTreePathCount

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
open Erdos1016.Nonbacktracking.ShortWalks
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

/-- The small-tree link count in the actual retained physical graph.
All tree, degree, and cut facts for J are derived from the original
labelled exterior components. -/
theorem card_retained_exterior_trees_le_length_blocks
    (U : Finset G.Vertex) (S : Finset (ExteriorComponents.Component G U))
    {a b : (graph G R hloop hsimple).Vertex}
    (C : (graph G R hloop hsimple).toSimpleGraph.Walk a a)
    (C' : (graph G R hloop hsimple).toSimpleGraph.Walk b b) (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hmax : ∀ v, G.degree v ≤ 3)
    (hout : ∀ v, v ∉ U → v ∈ R)
    (hCU : ∀ v ∈ C.support, vertex G R hloop hsimple v ∉ U)
    (hC'U : ∀ v ∈ C'.support, vertex G R hloop hsimple v ∉ U)
    (hretained : ∀ c ∈ S, ExteriorComponents.vertices G U c ⊆ R)
    (hforest : ∀ c ∈ S, G.IsForestWord (G.restrictEdges
      (G.internalEdges (ExteriorComponents.vertices G U c)) (fun _ => 1)))
    (hcubic : ∀ c ∈ S, ∀ v ∈ ExteriorComponents.vertices G U c, G.degree v = 3)
    (D t q : ℕ) (hq : 0 < q) (hg : GirthGreater (graph G R hloop hsimple).toSimpleGraph D)
    (hbudget : 2 * (t + 2 * q) ≤ D)
    (hcut : ∀ c ∈ S, (G.cutEdges (ExteriorComponents.vertices G U c)).card ≤ t)
    (hattachC : ∀ c ∈ S, ∃ u ∈ C.support, ∃ x ∈ ExteriorComponents.vertices G U c,
      G.toSimpleGraph.Adj (vertex G R hloop hsimple u) x)
    (hattachC' : ∀ c ∈ S, ∃ v ∈ C'.support, ∃ y ∈ ExteriorComponents.vertices G U c,
      G.toSimpleGraph.Adj y (vertex G R hloop hsimple v)) :
    S.card ≤ (C.length / q + 1) * (C'.length / q + 1) := by
  let F : S → Finset (graph G R hloop hsimple).Vertex := fun c =>
    region G R hloop hsimple (ExteriorComponents.vertices G U c.1)
  have hdis : Pairwise (fun i j : S => Disjoint (F i) (F j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hi hj
    exact Finset.disjoint_left.mp (ExteriorComponents.vertices_disjoint G U
      (fun he => hij (Subtype.ext he)))
        ((mem_region G R hloop hsimple _ v).mp hi)
        ((mem_region G R hloop hsimple _ v).mp hj)
  have hh := Erdos1016.Proof.ExteriorTreePathCount.card_exterior_trees_le_length_blocks
    C C' hC hdisjoint (fun v _ => ?_) F hdis ?_ ?_ ?_ ?_ D t q hq hg hbudget ?_ ?_ ?_
  · simpa only [Fintype.card_coe] using hh
  · rw [graph_degree_eq_physical]
    have h := degree_le G R hloop hsimple ((vertexEquiv G R).symm v)
    simpa only [Equiv.apply_symm_apply] using h.trans (hmax _)
  · intro i v hv hCv
    exact hCU v hCv (ExteriorComponents.vertices_subset G U i.1
      ((mem_region G R hloop hsimple _ v).mp hv))
  · intro i v hv hCv
    exact hC'U v hCv (ExteriorComponents.vertices_subset G U i.1
      ((mem_region G R hloop hsimple _ v).mp hv))
  · intro i
    exact component_induced_tree G R hloop hsimple U i.1 (hretained i.1 i.2) (hforest i.1 i.2)
  · intro i v hv
    rw [component_simple_degree_eq G R hloop hsimple U i.1 (hretained i.1 i.2) hout v hv]
    exact hcubic i.1 i.2 _ ((mem_region G R hloop hsimple _ v).mp hv)
  · intro i
    calc
      _ ≤ ((graph G R hloop hsimple).cutEdges (F i)).card :=
        PhysicalGraph.boundary_incidences_le_cut _ _
      _ = (G.cutEdges (ExteriorComponents.vertices G U i.1)).card :=
        component_cut_card_eq G R hloop hsimple U i.1 (hretained i.1 i.2) hout
      _ ≤ t := hcut i.1 i.2
  · intro i
    obtain ⟨u, hu, x, hx, hux⟩ := hattachC i.1 i.2
    let w := vertexEquiv G R ⟨x, hretained i.1 i.2 hx⟩
    refine ⟨u, hu, w, ?_, ?_⟩
    · simpa only [F, mem_region, w, vertex_vertexEquiv] using hx
    · rw [adj_vertex_iff]
      simpa only [w, vertex_vertexEquiv] using hux
  · intro i
    obtain ⟨v, hv, y, hy, hyv⟩ := hattachC' i.1 i.2
    let w := vertexEquiv G R ⟨y, hretained i.1 i.2 hy⟩
    refine ⟨v, hv, w, ?_, ?_⟩
    · simpa only [F, mem_region, w, vertex_vertexEquiv] using hy
    · rw [adj_vertex_iff]
      simpa only [w, vertex_vertexEquiv] using hyv

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization

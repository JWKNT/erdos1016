import Erdos1016.Nonbacktracking.Girth.DeficitShrinkBound
import Erdos1016.Decomposition.TwoCore.DeletionDeficit

set_option autoImplicit false

/-!
# Cubic deficit of an induced physical region

No minimum degree is assumed: isolated vertices and leaves contribute their
full missing incidence count. The resulting deficit is exactly the original
physical cut size.
-/

noncomputable section

namespace Erdos1016.Proof.InducedCubicDeficit

open Erdos1016.SafeCore Erdos1016.Nonbacktracking
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.BoundaryTrace

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cubicDeficit_univ_eq_vertex_edge_ledger (G : PhysicalGraph) :
    cubicDeficit G.toSimpleGraph Finset.univ =
      3 * (G.vertexCount : ℤ) - 2 * (G.edgeCount : ℤ) := by
  unfold cubicDeficit
  simp only [Finset.card_univ, Fintype.card_fin]
  simp_rw [Erdos1016.Proof.FewDeletedCoreBudget.degreeWithin_univ_eq_degree,
    ← original_degree_eq_graph_degree]
  have hsum : (∑ v : G.Vertex, (G.degree v : ℤ)) = 2 * (G.edgeCount : ℤ) := by
    exact_mod_cast physical_degree_sum G
  rw [hsum]

theorem inducedPhysical_edgeCount_eq (G : PhysicalGraph) (R : Finset G.Vertex) :
    (inducedPhysical G R).edgeCount = (internalEdges G R).card := by
  change Fintype.card (Network.Shore.InsideEdge G.traceNetwork R) = _
  simp only [Network.Shore.InsideEdge, Fintype.subtype_card]
  rfl

theorem inducedPhysical_cubicDeficit_eq_cutSize
    (G : PhysicalGraph) (R : Finset G.Vertex)
    (hcubic : ∀ v ∈ R, G.degree v = 3) :
    cubicDeficit (inducedPhysical G R).toSimpleGraph Finset.univ =
      (cutSize G R : ℤ) := by
  rw [cubicDeficit_univ_eq_vertex_edge_ledger, inducedPhysical_vertexCount_eq_card,
    inducedPhysical_edgeCount_eq]
  have h := cubic_cut_identity G R hcubic
  omega

/-- The manuscript's high-girth deficit shrink theorem applied to an actual
induced cubic region, with its deficit discharged as the original cut. -/
theorem region_order_le_constant_cutSize
    (G : PhysicalGraph) (R : Finset G.Vertex)
    (hcubic : ∀ v ∈ R, G.degree v = 3)
    (M D : ℕ) (hM : 2 ≤ M) (hRM : R.card ≤ M)
    (hg : ShortWalks.GirthGreater (G.toSimpleGraph.induce (↑R : Set G.Vertex)) D)
    (C : ℝ) (hC : 2 < C)
    (hgap : (((D / 2 - 1 : ℕ) : ℝ) * (1 - 1 / (C - 1))) >
      Real.logb 2 ((M : ℝ) / 2)) :
    (R.card : ℝ) ≤ C * (cutSize G R : ℝ) := by
  let H := inducedPhysical G R
  have hmax : ∀ w, H.degree w ≤ 3 := by
    intro w
    let e := Fintype.equivFin (Network.Shore.InsideVertex R)
    obtain ⟨v, rfl⟩ := e.surjective w
    change (inducedPhysical G R).degree (Fintype.equivFin _ v) ≤ 3
    rw [inducedPhysical_degree_eq]
    calc
      degreeWithin G.toSimpleGraph R v.1 ≤ G.toSimpleGraph.degree v.1 :=
        degreeWithin_le_degree _ _ _
      _ = G.degree v.1 := (original_degree_eq_graph_degree G v.1).symm
      _ = 3 := hcubic v.1 v.2
  have hgraph : (inducedNetwork G R).graph =
      G.toSimpleGraph.induce (↑R : Set G.Vertex) := by
    rw [← G.traceNetwork_graph]
    exact Network.Shore.inside_graph_eq_induce G.traceNetwork R
  have hgH : ShortWalks.GirthGreater H.toSimpleGraph D := by
    apply girthGreater_graphIso (inducedPhysicalGraphIso G R) D
    simpa only [hgraph] using hg
  have hbound := order_le_constant_cubicDeficit_of_girth H hmax M D hM
    (by simpa [H, inducedPhysical_vertexCount_eq_card] using hRM) hgH C hC hgap
  rw [inducedPhysical_cubicDeficit_eq_cutSize G R hcubic] at hbound
  rw [show H.vertexCount = R.card from inducedPhysical_vertexCount_eq_card G R] at hbound
  exact_mod_cast hbound

end Erdos1016.Proof.InducedCubicDeficit

end

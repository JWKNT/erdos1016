import Erdos1016.Graph.Multigraph.InducedSimpleDegrees
import Erdos1016.Graph.Multigraph.SubcubicOrder
import Erdos1016.Nonbacktracking.Spectrum.DeficitSpectralBound

set_option autoImplicit false

/-! Exact order and degree-deficit ledgers for deleting a vertex set from
the marked cubic multigraph. The retained graph may have isolated vertices. -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

local instance deletionBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p

@[simp] theorem cutEdges_compl (G : FiniteMultiGraph) (R : Finset G.Vertex) :
    G.cutEdges Rᶜ = G.cutEdges R := by
  ext e
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_compl]
  tauto

theorem cut_card_le_three_mul_card (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hmax : ∀ v ∈ R, G.degree v ≤ 3) :
    (G.cutEdges R).card ≤ 3 * R.card := by
  have hledger := G.sum_region_degree R
  have hsum : (∑ v ∈ R, G.degree v) ≤ 3 * R.card := by
    calc
      _ ≤ ∑ _v ∈ R, 3 := Finset.sum_le_sum hmax
      _ = _ := by simp [Nat.mul_comm]
  omega

namespace InducedSimpleRealization

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

theorem max_degree_three (hmax : ∀ v, G.degree v ≤ 3) :
    ∀ v, (graph G R hloop hsimple).degree v ≤ 3 := by
  intro v
  obtain ⟨w, rfl⟩ := (vertexEquiv G R).surjective v
  exact (degree_le G R hloop hsimple w).trans (hmax w.1)

/-- Every missing incidence at a retained cubic vertex is exactly one cut
edge. Loops or parallel edges among deleted vertices cause no extra term. -/
theorem degreeDeficit_eq_cut (hcubic : ∀ v ∈ R, G.degree v = 3) :
    Nonbacktracking.degreeDeficit (graph G R hloop hsimple) =
      ((G.cutEdges R).card : ℝ) := by
  have hledger := G.sum_region_degree R
  have hsum : (∑ v ∈ R, G.degree v) = 3 * R.card := by
    rw [Finset.sum_congr rfl hcubic]
    simp [Nat.mul_comm]
  rw [hsum] at hledger
  have hreal : (3 : ℝ) * R.card =
      2 * (G.internalEdges R).card + (G.cutEdges R).card := by exact_mod_cast hledger
  rw [Nonbacktracking.degreeDeficit_eq_counts, graph_vertexCount, graph_edgeCount]
  linarith

theorem degreeDeficit_le_deleted (hmax : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v ∈ R, G.degree v = 3) :
    Nonbacktracking.degreeDeficit (graph G R hloop hsimple) ≤ 3 * (Rᶜ.card : ℝ) := by
  rw [degreeDeficit_eq_cut G R hloop hsimple hcubic]
  have h := G.cut_card_le_three_mul_card Rᶜ (fun v _ => hmax v)
  rw [cutEdges_compl] at h
  exact_mod_cast h

theorem order_add_deleted :
    (graph G R hloop hsimple).vertexCount + Rᶜ.card = G.vertexCount := by
  rw [graph_vertexCount, Finset.card_add_card_compl]
  simp [FiniteMultiGraph.Vertex]

/-- The error in the order is controlled by the marked set and the deleted
vertices; this estimate does not assume any lower degree in the retained graph. -/
theorem marked_order_bounds (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hmax : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    2 * G.cycleRank ≤ (graph G R hloop hsimple).vertexCount + Rᶜ.card + 2 ∧
      (graph G R hloop hsimple).vertexCount ≤ 2 * G.cycleRank + 3 * P.card := by
  have ho := order_add_deleted G R hloop hsimple
  have hb := G.marked_order_bounds P hG hmax hcubic
  omega

end InducedSimpleRealization
end Erdos1016.FiniteMultiGraph

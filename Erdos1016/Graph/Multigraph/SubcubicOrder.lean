import Erdos1016.Graph.Multigraph.Forest
import Erdos1016.Graph.Multigraph.BoundaryImage

set_option autoImplicit false

/-!
# Order of a connected subcubic multigraph

Incidence handshaking and the binary cycle-rank Euler formula give
`|V| + 2 = 2β + ∑(3-degree)`. If all unmarked vertices are cubic, only
marked vertices contribute. Loops and parallel labels are included correctly
in both the degree sum and Euler formula.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

theorem componentCount_eq_one (G : FiniteMultiGraph) (hG : G.toSimpleGraph.Connected) :
    G.componentCount = 1 := by
  haveI : Nonempty G.Vertex := hG.nonempty
  haveI : Nonempty G.ConnectedComponent :=
    ⟨G.componentOf (Classical.choice hG.nonempty)⟩
  haveI : Subsingleton G.ConnectedComponent := hG.preconnected.subsingleton_connectedComponent
  letI : Unique G.ConnectedComponent :=
    ⟨⟨Classical.choice (inferInstance : Nonempty G.ConnectedComponent)⟩,
      fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique

theorem connected_euler (G : FiniteMultiGraph) (hG : G.toSimpleGraph.Connected) :
    G.cycleRank + G.vertexCount = G.edgeCount + 1 := by
  simpa only [G.componentCount_eq_one hG] using G.euler_formula

/-- The total deficit from cubic incidence degree. -/
def cubicDeficit (G : FiniteMultiGraph) : ℕ := ∑ v, (3 - G.degree v)

theorem deficit_add_twice_edges (G : FiniteMultiGraph)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    G.cubicDeficit + 2 * G.edgeCount = 3 * G.vertexCount := by
  have hsum : (∑ v, (3 - G.degree v + G.degree v)) = 3 * G.vertexCount := by
    simp only [Nat.sub_add_cancel (hdegree _)]
    simp [Nat.mul_comm]
  rw [Finset.sum_add_distrib, G.sum_degree] at hsum
  exact hsum

/-- Exact connected order identity, with no truncated subtraction on the rank. -/
theorem order_add_two_eq_twice_rank_add_deficit (G : FiniteMultiGraph)
    (hG : G.toSimpleGraph.Connected) (hdegree : ∀ v, G.degree v ≤ 3) :
    G.vertexCount + 2 = 2 * G.cycleRank + G.cubicDeficit := by
  have heuler := G.connected_euler hG
  have hdegree := G.deficit_add_twice_edges hdegree
  omega

/-- Cubic vertices outside the marked set contribute no deficit. -/
theorem cubicDeficit_eq_marked_sum (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    G.cubicDeficit = ∑ v ∈ P, (3 - G.degree v) := by
  classical
  unfold cubicDeficit
  symm
  apply Finset.sum_subset (Finset.subset_univ P)
  intro v hv hnot
  rw [hcubic v hnot]
  simp

/-- The exact order identity for the marked auxiliary multigraph. -/
theorem order_add_two_eq_twice_rank_add_marked_deficit (G : FiniteMultiGraph)
    (P : Finset G.Vertex) (hG : G.toSimpleGraph.Connected)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    G.vertexCount + 2 = 2 * G.cycleRank + ∑ v ∈ P, (3 - G.degree v) := by
  rw [← G.cubicDeficit_eq_marked_sum P hcubic]
  exact G.order_add_two_eq_twice_rank_add_deficit hG hdegree

/-- Each marked vertex contributes at most three to the order error. -/
theorem cubicDeficit_le_three_mul_marked (G : FiniteMultiGraph)
    (P : Finset G.Vertex) (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    G.cubicDeficit ≤ 3 * P.card := by
  rw [G.cubicDeficit_eq_marked_sum P hcubic]
  calc
    _ ≤ ∑ _v ∈ P, 3 := Finset.sum_le_sum (fun v _ => Nat.sub_le _ _)
    _ = 3 * P.card := by simp [Nat.mul_comm]

/-- A quantitative form of `|Γ| = 2β(Γ) + O(|P|+1)`. -/
theorem marked_order_bounds (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hdegree : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    2 * G.cycleRank ≤ G.vertexCount + 2 ∧
      G.vertexCount + 2 ≤ 2 * G.cycleRank + 3 * P.card := by
  have hid := G.order_add_two_eq_twice_rank_add_deficit hG hdegree
  have hbound := G.cubicDeficit_le_three_mul_marked P hcubic
  omega

/-- Real-valued error estimate used when the marked set has size at most a
constant times the square root of the rank. -/
theorem marked_order_abs_error (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hdegree : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3) :
    |(G.vertexCount : ℝ) - 2 * G.cycleRank| ≤ 2 + 3 * P.card := by
  have hb := G.marked_order_bounds P hG hdegree hcubic
  have hlo : (2 : ℝ) * G.cycleRank ≤ G.vertexCount + 2 := by exact_mod_cast hb.1
  have hhi : (G.vertexCount : ℝ) + 2 ≤ 2 * G.cycleRank + 3 * P.card := by
    exact_mod_cast hb.2
  exact abs_le.mpr ⟨by linarith [show (0 : ℝ) ≤ (P.card : ℝ) by positivity], by linarith⟩

end Erdos1016.FiniteMultiGraph

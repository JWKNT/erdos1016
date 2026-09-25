import Erdos1016.Graph.Multigraph.InducedDeletionBounds
import Erdos1016.Cycles.Counting.ForestCutoffParameters

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! The graph remaining after removal of the marks and a short-region
packing has the order and full degree deficit needed by the trace estimate. -/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.RetainedSizeBounds
open FiniteMultiGraph
open FiniteMultiGraph.InducedSimpleRealization
open DeficitCutoffParameters ForestCutoffParameters

local instance retainedSizeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem deleted_size_le (G : FiniteMultiGraph) (P S : Finset G.Vertex)
    (x : ℝ) (hx : 1 ≤ x)
    (hP : (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2))
    (hS : S.card ≤ packingCutoff x * girthCutoff x) :
    ((P ∪ S).card : ℝ) ≤ 3 * x * (2 : ℝ) ^ (x / 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hD : (girthCutoff x : ℝ) ≤ x / 10 := Nat.floor_le (by positivity)
  have hB := packingCutoff_le x hx0
  have hSR : (S.card : ℝ) ≤ packingCutoff x * (girthCutoff x : ℝ) := by
    exact_mod_cast hS
  have hS' : (S.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) * (x / 10) :=
    hSR.trans (mul_le_mul hB hD (by positivity) (by positivity))
  have hU : ((P ∪ S).card : ℝ) ≤ (P.card : ℝ) + S.card := by
    exact_mod_cast Finset.card_union_le P S
  have hp : 0 ≤ (2 : ℝ) ^ (x / 2) := by positivity
  have hxp := mul_le_mul_of_nonneg_right hx hp
  nlinarith

/-- The spectral input is uniform over all choices of the graph and packing.
No connectedness or minimum degree is required of the retained graph. -/
theorem eventually_retained_size_and_deficit :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex)
      (hloop : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e)
      (hsimple : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ,
        ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) →
      S.card ≤ packingCutoff x * girthCutoff x →
      let J := graph G (P ∪ S)ᶜ hloop hsimple
      (∀ v, J.degree v ≤ 3) ∧
      (2 : ℝ) ^ x ≤ J.vertexCount ∧ J.vertexCount ≤ 3 * (2 : ℝ) ^ x ∧
      Nonbacktracking.degreeDeficit J ≤ 9 * x * (2 : ℝ) ^ (x / 2) := by
  have hdec := polynomial_dyadic_decay 1 (1 / 2) (by norm_num)
  have hzero := polynomial_dyadic_decay 0 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hdec.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8),
    hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)] with x hx hdec hzero
  intro G P S hloop hsimple hG hmax hcubic hrank hP hS
  let J := graph G (P ∪ S)ᶜ hloop hsimple
  have hp : 0 < (2 : ℝ) ^ (x / 2) := by positivity
  have hr : 0 < (2 : ℝ) ^ x := by positivity
  have hpower : (2 : ℝ) ^ x = (2 : ℝ) ^ (x / 2) * (2 : ℝ) ^ (x / 2) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hxsmall : x * (2 : ℝ) ^ (x / 2) ≤ (2 : ℝ) ^ x / 8 := by
    rw [show -(1 / 2 : ℝ) * x = -(x / 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hdec
    simp only [pow_one] at hdec
    have hxdiv : x / (2 : ℝ) ^ (x / 2) < 1 / 8 := by
      simpa only [div_eq_mul_inv] using hdec
    have hmul := (div_lt_iff₀ hp).mp hxdiv
    have hmul2 := mul_le_mul_of_nonneg_right hmul.le hp.le
    rw [hpower]
    nlinarith only [hmul2]
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ x / 2 := by
    simp only [pow_zero, one_mul, neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hzero
    have hdiv : 1 / (2 : ℝ) ^ x < 1 / 4 := by simpa only [one_div] using hzero
    have h := (div_lt_iff₀ hr).mp hdiv
    linarith
  have hdel := deleted_size_le G P S x hx hP hS
  have horder := InducedSimpleRealization.marked_order_bounds G (P ∪ S)ᶜ
    hloop hsimple P hG hmax hcubic
  simp only [compl_compl] at horder
  have hlo : 2 * (G.cycleRank : ℝ) ≤ (J.vertexCount : ℝ) + (P ∪ S).card + 2 := by
    exact_mod_cast horder.1
  have hhi : (J.vertexCount : ℝ) ≤ 2 * G.cycleRank + 3 * P.card := by
    exact_mod_cast horder.2
  rw [hrank] at hlo hhi
  have hxp := mul_le_mul_of_nonneg_right hx hp.le
  have hdegree := degreeDeficit_le_deleted G (P ∪ S)ᶜ hloop hsimple hmax (by
    intro v hv
    apply hcubic v
    exact fun hvP => (Finset.mem_compl.mp hv) (Finset.mem_union_left S hvP))
  simp only [compl_compl] at hdegree
  refine ⟨max_degree_three G (P ∪ S)ᶜ hloop hsimple hmax, ?_, ?_, ?_⟩
  · linarith
  · nlinarith only [hhi, hP, hxp, hxsmall]
  · dsimp [J]
    linarith

end Erdos1016.Proof.RetainedSizeBounds

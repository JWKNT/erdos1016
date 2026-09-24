import Erdos1016.Nonbacktracking.Spectrum.Operator

set_option autoImplicit false

/-!
# Uniform-dart stationarity and the mean logarithmic branching

No convergence-to-stationarity or mixing assumption is used. Stationarity
is a finite column-sum identity. The final mean-log formula is the local
quantity used in the source's entropy argument; that full path-entropy /
Perron-radius argument remains to be formalized separately.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance stationarityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Stochastic nonbacktracking transition on a min-degree-two graph. -/
def transition (G : PhysicalGraph) (d e : Dart G) : ℝ :=
  (if Next G d e then 1 else 0) / ((G.degree (head G d) : ℝ) - 1)



theorem transition_row_sum (G : PhysicalGraph) (hmin : ∀ u, 2 ≤ G.degree u)
    (d : Dart G) : (∑ e, transition G d e) = 1 := by
  have hden : (G.degree (head G d) : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ G.degree (head G d) := by exact_mod_cast hmin (head G d)
    linarith
  unfold transition
  rw [← Finset.sum_div, ← step_eq_sum_next G (fun _ => (1 : ℝ)) d]
  simp only [step, outgoing_one]
  exact div_self hden

theorem transition_reverse (G : PhysicalGraph) (d e : Dart G) :
    transition G d e = transition G (reverse G e) (reverse G d) := by
  have hr := next_reverse G d e
  unfold transition
  rw [head_reverse]
  by_cases hn : Next G d e
  · rw [if_pos hn, if_pos (hr.1 hn), hn.1]
  · rw [if_neg hn, if_neg (fun h => hn (hr.2 h)), zero_div, zero_div]

theorem transition_column_sum (G : PhysicalGraph) (hmin : ∀ u, 2 ≤ G.degree u)
    (e : Dart G) : (∑ d, transition G d e) = 1 := by
  calc
    _ = ∑ d, transition G (reverse G e) d := by
      apply Fintype.sum_equiv (reverseEquiv G)
      intro d
      exact transition_reverse G d e
    _ = 1 := transition_row_sum G hmin (reverse G e)



def degreeTwoCount (G : PhysicalGraph) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = 2)).card

def meanLogBranching (G : PhysicalGraph) : ℝ :=
  (∑ d : Dart G, Real.logb 2 ((G.degree (head G d) : ℝ) - 1)) /
    (2 * (G.edgeCount : ℝ))

private theorem degreeTwo_indicator_sum (G : PhysicalGraph) :
    (∑ v : G.Vertex, if G.degree v = 2 then (1 : ℝ) else 0) =
      (degreeTwoCount G : ℝ) := by
  unfold degreeTwoCount
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

theorem physical_degree_sum (G : PhysicalGraph) :
    (∑ v : G.Vertex, G.degree v) = 2 * G.edgeCount := by
  have h := SafeCore.degree_sum_region G Finset.univ
  simpa [SafeCore.internalEdges, SafeCore.cutSize, SafeCore.ownerCut,
    SafeCore.crossing] using h

theorem min_two_max_three_degree_sum (G : PhysicalGraph)
    (hmin : ∀ u, 2 ≤ G.degree u) (hmax : ∀ u, G.degree u ≤ 3) :
    2 * (G.edgeCount : ℝ) = 3 * G.vertexCount - degreeTwoCount G := by
  have hform (u : G.Vertex) : (G.degree u : ℝ) =
      3 - (if G.degree u = 2 then 1 else 0) := by
    have hl := hmin u
    have hh := hmax u
    have hc : G.degree u = 2 ∨ G.degree u = 3 := by omega
    rcases hc with h | h <;> simp [h] <;> norm_num
  have hsum := congrArg (fun n : ℕ => (n : ℝ)) (physical_degree_sum G)
  push_cast at hsum
  simp_rw [hform] at hsum
  rw [Finset.sum_sub_distrib, degreeTwo_indicator_sum] at hsum
  simpa [mul_comm] using hsum.symm

/-- The actual graph's directed-edge average, not an assigned entropy parameter. -/
theorem meanLogBranching_eq (G : PhysicalGraph)
    (hmin : ∀ u, 2 ≤ G.degree u) (hmax : ∀ u, G.degree u ≤ 3)
    (hm : 0 < G.edgeCount) :
    meanLogBranching G =
      1 - 2 * (degreeTwoCount G : ℝ) / (2 * (G.edgeCount : ℝ)) := by
  have hlocal (u : G.Vertex) :
      (G.degree u : ℝ) * Real.logb 2 ((G.degree u : ℝ) - 1) =
      3 - 3 * (if G.degree u = 2 then 1 else 0) := by
    have hl := hmin u
    have hh := hmax u
    have hc : G.degree u = 2 ∨ G.degree u = 3 := by omega
    rcases hc with h | h <;>
      norm_num [h, Real.logb_self_eq_one]
  have hnum : (∑ d : Dart G, Real.logb 2 ((G.degree (head G d) : ℝ) - 1)) =
      3 * G.vertexCount - 3 * degreeTwoCount G := by
    rw [sum_heads G (fun u : G.Vertex =>
      Real.logb 2 ((G.degree u : ℝ) - 1))]
    simp_rw [hlocal]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, degreeTwo_indicator_sum]
    simp [mul_comm]
  have hsum := min_two_max_three_degree_sum G hmin hmax
  have hden : (2 * (G.edgeCount : ℝ)) ≠ 0 := by
    have hm' : (0 : ℝ) < G.edgeCount := by exact_mod_cast hm
    positivity
  unfold meanLogBranching
  rw [hnum]
  field_simp [hden]
  nlinarith only [hsum]

/-- The coarse b/n entropy loss used in source (5.2). -/
theorem meanLogBranching_lower (G : PhysicalGraph)
    (hmin : ∀ u, 2 ≤ G.degree u) (hmax : ∀ u, G.degree u ≤ 3)
    (hn : 0 < G.vertexCount) :
    1 - (degreeTwoCount G : ℝ) / G.vertexCount ≤ meanLogBranching G := by
  have hb : degreeTwoCount G ≤ G.vertexCount := by
    unfold degreeTwoCount
    simpa using Finset.card_le_univ (Finset.univ.filter (fun v : G.Vertex => G.degree v = 2))
  have hsum := min_two_max_three_degree_sum G hmin hmax
  have hb' : (degreeTwoCount G : ℝ) ≤ G.vertexCount := by exact_mod_cast hb
  have hn' : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hmn : (G.vertexCount : ℝ) ≤ G.edgeCount := by linarith
  have hm' : (0 : ℝ) < G.edgeCount := hn'.trans_le hmn
  have hm : 0 < G.edgeCount := by exact_mod_cast hm'
  rw [meanLogBranching_eq G hmin hmax hm]
  have hdiv : (degreeTwoCount G : ℝ) / G.edgeCount ≤
      (degreeTwoCount G : ℝ) / G.vertexCount :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn' hmn
  have heq : 2 * (degreeTwoCount G : ℝ) / (2 * (G.edgeCount : ℝ)) =
      (degreeTwoCount G : ℝ) / G.edgeCount := by field_simp; ring
  rw [heq]
  linarith

end Erdos1016.Nonbacktracking

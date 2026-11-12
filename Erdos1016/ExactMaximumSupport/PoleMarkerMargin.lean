import Erdos1016.Probability.Avoidance.PoleMarker

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Pole layer bounds at any positive margin above one half

The boundary demand uses the complete physical parity fiber.
Its marker-supported representative preserves every edge outside the marker.
The strict layer theorem applies with half the given positive margin.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.PoleMarkerMargin
open FiniteMultiGraph Probability Probability.PoleMarker Probability.GeodesicMarker

local instance marginDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A fixed positive affine forest margin bounds every distance level. -/
theorem exists_pole_layer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∑ v, b v) = 0 → (∀ v, v ∉ ports → b v = 0) →
      (1/2 : ℝ)+ε ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  obtain ⟨B,hB⟩ := ThinMarkerLayers.exists_layer_width_bound (ε/2) (by positivity)
  refine ⟨B,?_⟩
  intro G ports o b hG hdegree hcubic ho hb hports hq
  apply hB G (marker G hG ports o) (level G o) ports.card hG hdegree
    (marker_connected G hG ports o ho)
  · intro v hv
    apply hcubic v
    exact fun hp => hv (ports_subset_marker G hG ports o hp)
  · exact level_edge G hG o
  · exact marker_layer_card G hG ports o
  · have hr := affineForestProbability_le_region G hG ports o b hb hports
    linarith

/-- Positive affine forest density already forces the required total demand parity. -/
theorem exists_supported_demand_layer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∀ v, v ∉ ports → b v = 0) →
      (1/2 : ℝ)+ε ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  obtain ⟨B,hB⟩ := exists_pole_layer_bound ε hε
  refine ⟨B,?_⟩
  intro G ports o b hG hdegree hcubic ho hports hq
  have hb : (∑ v, b v) = 0 := by
    by_contra hn
    rw [affineForestProbability_eq_zero_of_sum_ne_zero G b hn] at hq
    linarith
  exact hB G ports o b hG hdegree hcubic ho hb hports hq

/-- The explicit margin needed by the few-cycles argument. -/
theorem exists_pole_layer_bound_501 :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∑ v, b v) = 0 → (∀ v, v ∉ ports → b v = 0) →
      (501/1000 : ℝ) ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  simpa only [show (1/2 : ℝ)+1/1000=501/1000 by norm_num] using
    exists_pole_layer_bound (1/1000) (by norm_num)

/-- The fixed margin does not require a separate even-total-demand premise. -/
theorem exists_supported_demand_layer_bound_501 :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∀ v, v ∉ ports → b v = 0) →
      (501/1000 : ℝ) ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  simpa only [show (1/2 : ℝ)+1/1000=501/1000 by norm_num] using
    exists_supported_demand_layer_bound (1/1000) (by norm_num)

end Erdos1016.ExactMaximumSupport.PoleMarkerMargin

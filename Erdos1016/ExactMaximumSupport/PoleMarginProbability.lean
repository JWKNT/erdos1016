import Erdos1016.ExactMaximumSupport.PoleOutsideRank

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Path and exterior forest bounds at any positive margin

The affine path density gives the layer bound at the stated margin.
The actual exterior forest law then bounds disjoint short cycle regions.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleMarginProbability
open FiniteMultiGraph BoundaryTrace BoundaryTrace.Network BoundaryDecay
open Probability Probability.PoleMarker CycleRegions

local instance marginDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Any positive margin bounds the distance layers of a path-rich physical pole. -/
theorem exists_path_layer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (s t : G.Vertex),
      G.IsLoopless → G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → s ∈ ports → t ∈ ports → s ≠ t →
      (1/2 + ε) * (2:ℝ)^G.cycleRank ≤ G.looplessNetwork.numPaths s t →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist s v : ℤ) = j).card ≤
        B * (ports.card + 1)^2 := by
  obtain ⟨B,hB⟩ := PoleMarkerMargin.exists_supported_demand_layer_bound ε hε
  refine ⟨B,?_⟩
  intro G ports s t hloop hG hdeg hcubic hs ht hst hp
  apply hB G ports s (G.looplessNetwork.pathDemand s t) hG hdeg hcubic hs
  · intro v hv
    have hvs : v ≠ s := by rintro rfl; exact hv hs
    have hvt : v ≠ t := by rintro rfl; exact hv ht
    simp [Network.pathDemand, Pi.single_apply, hvs, hvt]
  · rw [PathForestProbability.affineForestProbability_eq_path_density G hloop hG s t hst]
    exact (le_div_iff₀ (by positivity)).mpr hp

/-- Translation by the prescribed path preserves its full positive exterior margin. -/
theorem restricted_forest_probability (ε : ℝ) (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (hG : G.toSimpleGraph.Connected) (s t : G.Vertex) (hst : s ≠ t)
    (hp : (1/2 + ε) * (2:ℝ)^G.cycleRank ≤ G.looplessNetwork.numPaths s t)
    (a : G.EdgeWord) (hb : G.boundary a = G.looplessNetwork.pathDemand s t)
    (E : Finset G.Edge) (hzero : ∀ e ∈ E, a e = 0) :
    (1/2:ℝ) + ε ≤
      Finite.density (fun z : G.CycleSpace => G.IsForestWord (G.restrictEdges E z.1)) := by
  apply le_trans ?_ (PathExteriorProbability.affineForestProbability_le_restricted G _ a hb E hzero)
  rw [PathForestProbability.affineForestProbability_eq_path_density G hloop hG s t hst]
  exact (le_div_iff₀ (by positivity)).mpr hp

/-- A positive exterior margin gives a uniform bound on disjoint short cycle regions. -/
theorem exists_packing_bound (ε : ℝ) (hε : 0 < ε) (d : ℕ) :
    ∃ K : ℕ, ∀ (G : FiniteMultiGraph), G.toSimpleGraph.Connected →
      (∀ v, G.degree v ≤ 3) →
      ∀ (ι : Type) [Fintype ι] (Z : ι → G.EdgeWord), (∀ i, G.IsCycleWord (Z i)) →
      Pairwise (fun i j => Disjoint (region G (Z i)) (region G (Z j))) →
      ∀ P : Finset G.Vertex, (∀ i, Disjoint (region G (Z i)) P) →
      (∀ i, G.wordLength (Z i) ≤ d) →
      (1/2:ℝ) + ε ≤ Finite.density (fun z : G.CycleSpace =>
        G.IsForestWord (G.restrictEdges (G.internalEdges Pᶜ) z.1)) →
      Fintype.card ι ≤ K := by
  obtain ⟨K,hK⟩ := exists_nat_ge (((d:ℝ) + 1) * (2:ℝ)^d / ε)
  refine ⟨K,?_⟩
  intro G hG hdegree ι _ Z hz hdisj P hout hsize hforest
  have hE (i : ι) : G.internalEdges (region G (Z i)) ⊆ G.internalEdges Pᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_compl.mpr (fun hp => Finset.disjoint_left.mp (hout i) hh.1 hp),
      Finset.mem_compl.mpr (fun hp => Finset.disjoint_left.mp (hout i) hh.2 hp)⟩
  have h := G.smallCut_packing_card_le (fun i => region G (Z i)) hG hdisj
    (fun i => cycle_region_connected G (Z i) (hz i)) Finset.univ d
    (fun i _ => (cycle_cut_le_length G (Z i) (hz i) hdegree).trans (hsize i))
    (fun i _ => cycle_region_cyclic G (Z i) (hz i))
    (G.internalEdges Pᶜ) (fun i _ => hE i) (ε/2) (by positivity)
    (lt_of_lt_of_le (by linarith) hforest)
  have hh : (Fintype.card ι : ℝ) ≤ ((d:ℝ) + 1) * (2:ℝ)^d / ε := by
    simpa only [Finset.card_univ, show 2 * (ε/2) = ε by ring] using h
  exact_mod_cast hh.trans hK

end Erdos1016.ExactMaximumSupport.PoleMarginProbability

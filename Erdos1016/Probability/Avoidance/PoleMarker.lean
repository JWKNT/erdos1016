import Erdos1016.Probability.Avoidance.GeodesicMarker
import Erdos1016.Probability.Avoidance.ThinMarkerLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Affine forest laws and thin pole markers

A boundary demand supported on the ports has a representative on the marker.
Translation by that representative preserves every edge outside the marker.
The exact uniform affine law therefore bounds the exterior forest law from below.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.Probability.PoleMarker
open FiniteMultiGraph GeodesicMarker

local instance poleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The proportion of forests in the complete physical parity fiber. -/
def affineForestProbability (G : FiniteMultiGraph) (b : G.Demand) : ℝ :=
  Finite.density (fun x : Parity.Fiber G.boundary b => G.IsForestWord x.1)

/-- An odd total demand has an empty physical parity fiber. -/
theorem affineForestProbability_eq_zero_of_sum_ne_zero (G : FiniteMultiGraph)
    (b : G.Demand) (hb : (∑ v, b v) ≠ 0) : affineForestProbability G b = 0 := by
  letI : IsEmpty (Parity.Fiber G.boundary b) := ⟨fun x => by
    apply hb
    have hh := RegionLocalization.sum_boundary_eq_zero G x.1
    rw [x.2] at hh
    exact hh⟩
  simp [affineForestProbability, Finite.density]

theorem walkWord_zero_of_src_not_mem (G : FiniteMultiGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (e : G.Edge) (he : G.src e ∉ p.support) :
    G.walkWord p e = 0 := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    have hs : G.src e ≠ a := by intro h; exact he (by simp [h])
    have hp : G.src e ∉ p.support := by intro h; exact he (by simp [h])
    have hb : G.src e ≠ b := by intro h; exact hp (h ▸ p.start_mem_support)
    have hne : e ≠ G.edgeForAdj hab := by
      intro h
      rcases G.edgeForAdj_endpoints hab with hh | hh
      · exact hs (h ▸ hh.1)
      · exact hb (h ▸ hh.1)
    rw [walkWord]
    change (Pi.single (G.edgeForAdj hab) (1 : F₂) : G.EdgeWord) e + G.walkWord p e = 0
    simp [Pi.single_apply, hne, ih hp]

variable (G : FiniteMultiGraph) (hG : G.toSimpleGraph.Connected)
  (ports : Finset G.Vertex) (o : G.Vertex)

def repair (b : G.Demand) : G.EdgeWord :=
  ∑ v, b v • G.walkWord (route G hG o v)

theorem boundary_repair (b : G.Demand) (hb : ∑ v, b v = 0) :
    G.boundary (repair G hG o b) = b := by
  ext z
  simp only [repair, map_sum, map_smul, boundary_walkWord, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hb, zero_mul, zero_add]
  simp [vertexUnit, Pi.single_apply]

theorem repair_zero_outside (b : G.Demand) (hports : ∀ v, v ∉ ports → b v = 0)
    (e : G.Edge) (he : G.src e ∉ marker G hG ports o) : repair G hG o b e = 0 := by
  simp only [repair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ ports
  · have hp : G.src e ∉ (route G hG o v).support := by
      intro h
      exact he ((mem_marker G hG ports o (G.src e)).mpr ⟨v, hv, h⟩)
    rw [walkWord_zero_of_src_not_mem G _ e hp, mul_zero]
  · rw [hports v hv, zero_mul]

theorem affineForestProbability_le_region (b : G.Demand) (hb : ∑ v, b v = 0)
    (hports : ∀ v, v ∉ ports → b v = 0) :
    affineForestProbability G b ≤ G.regionForestProbability (marker G hG ports o)ᶜ := by
  let f : Parity.Fiber G.boundary b := ⟨repair G hG o b, boundary_repair G hG o b hb⟩
  have he : affineForestProbability G b =
      Finite.density (fun z : G.CycleSpace => G.IsForestWord (z.1+f.1)) := by
    exact (Finite.density_equiv (Parity.fiberEquivKernel G.boundary f).symm (fun _ => Iff.rfl)).symm
  rw [he]
  have hi (z : G.CycleSpace) (hz : G.IsForestWord (z.1+f.1)) :
      G.IsForestWord (G.restrictEdges (G.internalEdges (marker G hG ports o)ᶜ) z.1) := by
    have hh := hz.restrictEdges (G.internalEdges (marker G hG ports o)ᶜ)
    have hword : G.restrictEdges (G.internalEdges (marker G hG ports o)ᶜ) (z.1+f.1) =
        G.restrictEdges (G.internalEdges (marker G hG ports o)ᶜ) z.1 := by
      funext e
      by_cases hm : e ∈ G.internalEdges (marker G hG ports o)ᶜ
      · have hs : G.src e ∉ marker G hG ports o :=
          Finset.mem_compl.mp ((Finset.mem_filter.mp hm).2.1)
        have hf : f.1 e = 0 := repair_zero_outside G hG ports o b hports e hs
        simp [restrictEdges, hm, hf]
      · simp [restrictEdges, hm]
    rw [hword] at hh
    exact hh
  have hc := Finite.count_mono hi
  have hd := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ Fintype.card G.CycleSpace)
  simpa only [Finite.density, regionForestProbability, Finite.count, G.cycleSpace_card,
    Nat.cast_pow, Nat.cast_ofNat, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hd

/-- Every distance level is bounded uniformly when one port-demand forest law is large. -/
theorem exists_pole_layer_bound :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∑ v, b v) = 0 → (∀ v, v ∉ ports → b v = 0) →
      (3/5 : ℝ) ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  obtain ⟨B, hB⟩ := ThinMarkerLayers.exists_layer_width_bound_three_fifths
  refine ⟨B, ?_⟩
  intro G ports o b hG hdegree hcubic ho hb hports hq
  apply hB G (marker G hG ports o) (level G o) ports.card hG hdegree
    (marker_connected G hG ports o ho)
  · intro v hv
    apply hcubic v
    exact fun hp => hv (ports_subset_marker G hG ports o hp)
  · exact level_edge G hG o
  · exact marker_layer_card G hG ports o
  · exact hq.trans (affineForestProbability_le_region G hG ports o b hb hports)

/-- The positive-probability hypothesis already forces the necessary even total demand. -/
theorem exists_supported_demand_layer_bound :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ ports → G.degree v = 3) → o ∈ ports →
      (∀ v, v ∉ ports → b v = 0) →
      (3/5 : ℝ) ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(ports.card+1)^2 := by
  obtain ⟨B, hB⟩ := exists_pole_layer_bound
  refine ⟨B, ?_⟩
  intro G ports o b hG hdegree hcubic ho hports hq
  have hb : (∑ v, b v) = 0 := by
    by_contra hn
    rw [affineForestProbability_eq_zero_of_sum_ne_zero G b hn] at hq
    norm_num at hq
  exact hB G ports o b hG hdegree hcubic ho hb hports hq

end Erdos1016.Probability.PoleMarker

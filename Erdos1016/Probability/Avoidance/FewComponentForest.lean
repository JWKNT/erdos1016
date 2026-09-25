import Erdos1016.Cycles.Selection.RetainedCycleSupply
import Erdos1016.Cycles.Geometry.ActualCycleLinkBound
import Erdos1016.Probability.Moments.InducedCycleAvoidance
import Erdos1016.Probability.Avoidance.MarkedForestReduction

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The complete few-component forest estimate. The same constructed
retained graph supplies the trace mass, vertex loads, and actual link count;
all numerical thresholds are uniform in the graph and marked set. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.ShortProof
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open Proof.DeficitCutoffParameters Proof.ForestCutoffParameters
open Proof.ExceptionalLoadCutoffs

theorem eventually_marked_forest_bound :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) →
      100 * (Nat.card (G.toSimpleGraph.induce (↑P : Set G.Vertex)).ConnectedComponent : ℝ) ≤ x →
      G.regionForestProbability Pᶜ ≤
        (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) := by
  classical
  have hy : Tendsto (Real.logb 2) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  have hz := hy.comp hy
  filter_upwards [eventually_exists_retained_cycle_supply, eventually_geometry_cutoffs,
    eventually_cutoff_exceptional_load_le_quarter 300000 (3 / 2) (by norm_num) (by norm_num),
    eventually_ge_atTop (100 : ℝ), hy.eventually_ge_atTop 2, hz.eventually_gt_atTop 0]
    with x hsupply hgeometry hload hx hy hz
  intro G P hG hmax hcubic hrank hP hcomponents
  by_contra hn
  have hbad : (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) < G.regionForestProbability Pᶜ :=
    lt_of_not_ge hn
  obtain ⟨F, hloop, hsimple, hF, hhit, hJmax, hg, hmass⟩ :=
    hsupply G P hG hmax hcubic hrank hP hbad
  let R := (P ∪ F.biUnion id)ᶜ
  let J := graph G R hloop hsimple
  let c : ℝ := Fintype.card (ExteriorComponents.Component G P)
  let e : ℝ := 300000 * linkEnvelope x
  let M : ℝ := (2 : ℝ) ^ (c + e)
  let L := 2 * upperHalfLength x
  let z := Real.logb 2 (Real.logb 2 x)
  have hc : c ≤ x / 100 := by
    have hc' : 100 * c ≤ x := by
      simpa only [Nat.card_eq_fintype_card] using hcomponents
    linarith
  have hL : (L : ℝ) ≤ x * Real.sqrt (Real.logb 2 x) := by
    have hf := Nat.floor_le (show 0 ≤ x * Real.sqrt (Real.logb 2 x) / 2 by positivity)
    change (upperHalfLength x : ℝ) ≤ _ at hf
    dsimp [L]
    push_cast
    linarith
  have hs : 0 < suffixCutoff x := by
    unfold suffixCutoff
    have := hgeometry.1
    omega
  have hshort : 2 * suffixCutoff x ≤ girthCutoff x := by unfold suffixCutoff; omega
  have herror : M * ((3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ suffixCutoff x) ≤ 1 / 4 :=
    hload c e hc (le_refl _)
  have hlinks : ∀ C C' : J.CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length C' ≤ L → C ≠ C' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') →
      BoundaryDecay.dyadic ((Nat.card (SeedPairCorrelation.Links G
        (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C')) : ℤ) - 1) ≤ M := by
    intro C C' hlen hlen' _ hdisj
    have hd : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C') := by
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact Finset.disjoint_left.mp hdisj
        ((mem_cycleRegion_vertex G R hloop hsimple C v).mpr hv)
        ((mem_cycleRegion_vertex G R hloop hsimple C' v).mpr hv')
    have hcard := actual_cycle_links_le G P F (girthCutoff x) (smallCutCutoff x) L
      hloop hsimple C C' hd hmax hcubic hF hhit hgeometry.1 hgeometry.2.1
      hgeometry.2.2.2.1 hgeometry.2.2.2.2 hlen hlen' hG (20 / z) (by positivity) hbad
    have hsmall : ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x / (2 * (20 / z)) =
        ((smallCutCutoff x : ℝ) + 1) * (2 : ℝ) ^ smallCutCutoff x * z / 40 := by
      have hz' : z ≠ 0 := ne_of_gt hz
      field_simp [hz']
      ring
    rw [hsmall] at hcard
    have henv := link_error_le_envelope x hx hy hz.le L hL
    have hcount : (Nat.card (SeedPairCorrelation.Links G
        (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C')) : ℝ) ≤ c + e := by
      dsimp [c, e, z, R] at *
      linarith
    dsimp [M]
    unfold BoundaryDecay.dyadic
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    push_cast
    linarith
  have hE : G.internalEdges R ⊆ G.internalEdges Pᶜ := by
    intro a ha
    have hends := (Finset.mem_filter.mp ha).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
    · exact fun hv => (Finset.mem_compl.mp hends.1) (Finset.mem_union_left _ hv)
    · exact fun hv => (Finset.mem_compl.mp hends.2) (Finset.mem_union_left _ hv)
  have hbound := InducedCycleAvoidance.forest_le_half_add_twenty G R hloop hsimple
    hG (fun v _ => hmax v) hJmax (girthCutoff x) L (suffixCutoff x) M z hg hs hshort
    (by dsimp [M]; positivity) hz hlinks hmass herror (G.internalEdges Pᶜ) hE
  rw [← G.regionForestProbability_eq_density] at hbound
  exact (not_lt_of_ge hbound) hbad

/-- The forest lemma of the shorter proof, for actual simple graphs and
actual nonempty cycle unions. No remaining mathematical premise. -/
theorem fewComponentForestEstimate : FewComponentForestEstimate :=
  fewComponentForestEstimate_of_marked_bound eventually_marked_forest_bound

end Erdos1016.ShortProof

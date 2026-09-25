import Erdos1016.Cycles.Selection.RetainedHighGirth
import Erdos1016.Cycles.Selection.RetainedSizeBounds
import Erdos1016.Cycles.Selection.ShortRegionObstructions

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.ShortProof
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open Proof.DeficitCutoffParameters Proof.ForestCutoffParameters
open Proof.RetainedSizeBounds Proof.SimpleRunWeight

/-- If the forest estimate failed, the maximal short-region packing would
produce an actual retained graph with the required positive cycle mass.
The mass, degree, and girth assertions all concern that same graph. -/
theorem eventually_exists_retained_cycle_supply :
    ∀ᶠ x : ℝ in atTop, ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) →
      (G.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) →
      (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x) < G.regionForestProbability Pᶜ →
      ∃ F : Finset (Finset G.Vertex),
      ∃ hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e,
      ∃ hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
        ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f,
      (∀ U ∈ F, G.ShortCyclicRegion P (girthCutoff x) U) ∧
      (∀ U, G.ShortCyclicRegion P (girthCutoff x) U → ((F.biUnion id) ∩ U).Nonempty) ∧
      let J := graph G (P ∪ F.biUnion id)ᶜ hloop hsimple
      (∀ v, J.degree v ≤ 3) ∧
      Nonbacktracking.ShortWalks.GirthGreater J.toSimpleGraph (girthCutoff x) ∧
      Real.logb 2 (Real.logb 2 x) / 64 ≤
        ∑ ell ∈ Finset.Icc 1 (2 * upperHalfLength x), cycleWordMassAtLength J ell := by
  filter_upwards [eventually_packing_threshold, eventually_geometry_cutoffs,
    eventually_retained_size_and_deficit, eventually_cycleWordMass_ge_loglog 9 (by norm_num)]
    with x hpacking hgeometry hsize hmass
  intro G P hG hmax hcubic hrank hP hforest
  obtain ⟨F, hF, _, _, hFS, _, hhit⟩ := G.exists_short_region_packing P
    (girthCutoff x) (packingCutoff x) (20 / Real.logb 2 (Real.logb 2 x)) hG
    (packingCutoff_pos x) hpacking hforest
  have hloop := G.retained_no_loops P (F.biUnion id) (girthCutoff x)
    (by have := hgeometry.1; omega) hmax hhit
  have hsimple := G.retained_simple P (F.biUnion id) (girthCutoff x)
    (by have := hgeometry.1; omega) hmax hhit
  let J := graph G (P ∪ F.biUnion id)ᶜ hloop hsimple
  have hg := G.retained_girth P (F.biUnion id) (girthCutoff x) hloop hsimple hmax hhit
  obtain ⟨hJmax, hnlo, hnhi, hd⟩ := hsize G P (F.biUnion id) hloop hsimple
    hG hmax hcubic hrank hP hFS
  exact ⟨F, hloop, hsimple, hF, hhit, hJmax, hg, hmass J hJmax hnlo hnhi hd hg⟩

end Erdos1016.ShortProof

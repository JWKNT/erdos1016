import Erdos1016.Graph.Cubicization.IncidenceRealization
import Erdos1016.Graph.Multigraph.ForestCharacterization
import Erdos1016.Extremal.Capacity.WitnessOutsideBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Forest transport through the incidence expansion

An even word supported outside the marked prefixes projects to an original
even word supported outside the witness. Injectivity of the cycle-space
projection is essential: a nonzero expanded cycle cannot disappear inside
the contracted path rows.
-/

noncomputable section

namespace Erdos1016.ShortProof.IncidencePaths

local instance incidenceForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

def outsideRegion : Finset (multigraph G W).Vertex := (markedVertices G W)ᶜ

def regionWord (x : (multigraph G W).CycleSpace) : (multigraph G W).EdgeWord :=
  (multigraph G W).restrictEdges ((multigraph G W).internalEdges (outsideRegion G W)) x.1

lemma projected_seed_supported_outside
    (x seed : (multigraph G W).CycleSpace)
    (hsub : ∀ e, seed.1 e ≠ 0 → regionWord G W x e ≠ 0) :
    ∀ e, (multigraphCycleSpaceEquiv G W seed).1 e ≠ 0 →
      G.extendOutsideWord W
        (G.outsideCycleProjection W (multigraphCycleSpaceEquiv G W x)) e ≠ 0 := by
  intro e he
  let f := edgeLabels G W (Sum.inr e)
  have hf : seed.1 f ≠ 0 := he
  have hx := hsub f hf
  have hins : f ∈ (multigraph G W).internalEdges (outsideRegion G W) := by
    by_contra hn
    simp only [regionWord, FiniteMultiGraph.restrictEdges, if_neg hn, ne_eq,
      not_true_eq_false] at hx
  have hsrc : (physical G W).src f ∉ markedVertices G W :=
    Finset.mem_compl.mp (Finset.mem_filter.mp hins).2.1
  have heW : e ∉ W := by
    intro h
    exact hsrc ((original_source_marked_iff G W e).mpr h)
  have hxe : x.1 f ≠ 0 := by
    simpa only [regionWord, FiniteMultiGraph.restrictEdges, if_pos hins] using hx
  simpa only [PhysicalGraph.extendOutsideWord, dif_neg heW,
    PhysicalGraph.outsideCycleProjection_apply, multigraphCycleSpaceEquiv_original_edge] using hxe

/-- If the original outside word is a forest, its expanded unmarked region
contains no nonzero even word. -/
theorem region_seed_eq_zero_of_outside_forest
    (x : (multigraph G W).CycleSpace)
    (hforest : IsOutsideForest G W
      (G.outsideCycleProjection W (multigraphCycleSpaceEquiv G W x)))
    (seed : (multigraph G W).CycleSpace)
    (hsub : ∀ e, seed.1 e ≠ 0 → regionWord G W x e ≠ 0) : seed.1 = 0 := by
  let y := multigraphCycleSpaceEquiv G W seed
  have hyforest : G.IsForest y.1 := by
    let inclusion : G.selectedGraph y.1 →g G.selectedGraph
        (G.extendOutsideWord W (G.outsideCycleProjection W (multigraphCycleSpaceEquiv G W x))) := {
      toFun := id
      map_rel' := by
        rintro u v ⟨e, he, hend⟩
        exact ⟨e, projected_seed_supported_outside G W x seed hsub e he, hend⟩ }
    intro v p hp
    exact hforest (p.map inclusion)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective (fun _ _ h => h)).mpr hp)
  have hy : y.1 = 0 := Proof.CycleSpaceForestZero.word_eq_zero_of_boundary_zero_of_forest
    G y.1 y.2 hyforest
  have hy' : multigraphCycleSpaceEquiv G W seed = 0 := Subtype.ext hy
  have hs : seed = 0 := (multigraphCycleSpaceEquiv G W).injective (by simpa using hy')
  exact congrArg Subtype.val hs

/-- A forest outside the original witness remains a forest on the expanded
region outside the marked incidence prefixes. -/
theorem outside_forest_implies_region_forest
    (x : (multigraph G W).CycleSpace)
    (hforest : IsOutsideForest G W
      (G.outsideCycleProjection W (multigraphCycleSpaceEquiv G W x))) :
    (multigraph G W).IsForestWord (regionWord G W x) := by
  apply ((multigraph G W).isForestWord_iff_no_even_support (regionWord G W x)).mpr
  exact region_seed_eq_zero_of_outside_forest G W x hforest

lemma outsideForestProbability_eq_density :
    outsideForestProbability G W = Finite.density
      (fun x : G.CycleSpace => IsOutsideForest G W (G.outsideCycleProjection W x)) := by
  unfold outsideForestProbability Finite.density Finite.count
  have hc : (Fintype.card G.CycleSpace : ℝ) = (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.cycleSpace_card
  rw [hc]
  simp only [Finset.sum_boole]

lemma regionForestProbability_eq_density :
    (multigraph G W).regionForestProbability (outsideRegion G W) =
      Finite.density (fun x : (multigraph G W).CycleSpace =>
        (multigraph G W).IsForestWord (regionWord G W x)) := by
  unfold FiniteMultiGraph.regionForestProbability Finite.density Finite.count regionWord
  have hc : (Fintype.card (multigraph G W).CycleSpace : ℝ) =
      (2 : ℝ) ^ (multigraph G W).cycleRank := by
    exact_mod_cast (multigraph G W).cycleSpace_card
  rw [hc]
  simp only [Finset.sum_boole]

/-- The original outside-forest probability is bounded by the actual
unmarked-region forest probability in the subcubic expansion. -/
theorem outsideForestProbability_le_region :
    outsideForestProbability G W ≤
      (multigraph G W).regionForestProbability (outsideRegion G W) := by
  rw [outsideForestProbability_eq_density, regionForestProbability_eq_density,
    ← density_multigraph_projection G W
      (fun x => IsOutsideForest G W (G.outsideCycleProjection W x))]
  unfold Finite.density
  apply div_le_div_of_nonneg_right
  · exact Finite.count_mono (outside_forest_implies_region_forest G W)
  · exact Nat.cast_nonneg _

end Erdos1016.ShortProof.IncidencePaths

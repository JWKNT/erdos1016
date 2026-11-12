import Erdos1016.ExactMaximumSupport.MinimalCyclicInterval
import Erdos1016.ExactMaximumSupport.ThinIntervalSize

set_option autoImplicit false

/-!
# Every cyclic interval contains a uniformly small cyclic interval

Minimum-span selection proves the first-layer forest premise.
The actual rank, boundary, and cycle-span estimates then bound the chosen region.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.SmallCyclicInterval
open FiniteMultiGraph ThinIntervalBoundary

/-- The local extraction step of the outside-rank argument. -/
theorem exists_small_interval (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (level : G.Vertex → ℤ) (θ : ℕ) (hloop : G.IsLoopless)
    (hdeg : ∀ v,G.degree v≤3) (hcubic : ∀ v,v∉P → G.degree v=3)
    (hfurther : ∀ v∈P,G.selectedDegree (outsideWord G P) v≤1)
    (hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1)
    (hwidth : ∀ j,(layer G P level j).card≤θ)
    (hmark : ∀ j,(Probability.LevelWindowBoundary.markedLayer G P level j).card≤1)
    {a b : ℤ} (hcyclic : G.HasCycleIn (region G P level a b)) :
    ∃ c d : ℤ,a≤c ∧ c≤d ∧ d≤b ∧
      region G P level c d ⊆ region G P level a b ∧
      G.HasCycleIn (region G P level c d) ∧
      (region G P level c d).card≤22*(θ+1) := by
  obtain ⟨c,d,hac,hcd,hdb,hregions,z,hz,hsub,⟨u,hu,huc⟩,⟨v,hv,hvd⟩,hforest⟩ :=
    MinimalCyclicInterval.exists_minimal_interval G P level hloop hcyclic
  refine ⟨c,d,hac,hcd,hdb,hregions,⟨z,hz,?_⟩,?_⟩
  · intro e he
    exact ⟨hsub ((CycleRegions.mem_region G z _).mpr (G.selectedDegree_src_pos he)),
      hsub ((CycleRegions.mem_region G z _).mpr (G.selectedDegree_dst_pos he))⟩
  · exact ThinIntervalSize.card_le_of_first_layer_forest G P level c d θ hloop hdeg
      hcubic hfurther hlevel hwidth hmark hforest z hz hsub u v hu hv huc hvd

end Erdos1016.ExactMaximumSupport.SmallCyclicInterval

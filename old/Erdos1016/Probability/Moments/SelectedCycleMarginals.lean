import Erdos1016.Cycles.Geometry.SelectedComplementClassification

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.SelectedCycleMarginals
open BoundaryDecay CycleSupply SafeCore FewBranchSelectedCycles
open SelectedComplementClassification SelectedComplementGeometry CutoffLimits

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Two or fewer disjoint selected cycles leave a connected original
complement: any additional component would have at least three contacts. -/
theorem eventually_small_family_complement_connected
    (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H)
      (S : Selection H p₀ c σ (n j)),
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      ∀ (F : Finset (coreApexGraph H).CycleWord), F ⊆ S.cycles →
      IsCyclePacking (coreApexGraph H) F → F.card ≤ 2 →
      (coreApexGraph H).originalExteriorComponents (F.biUnion Cycle.vertices) = 1 := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  filter_upwards [eventually_selected_complement_classification c σ hc hσ hσ20 n hn,
    hx.eventually_gt_atTop 0] with j hj hxj
  intro H p₀ S hmin hmax hExp F hF hpack htwo
  have hK : 2 ≤ momentK σ (Real.logb 2 (n j)) := by
    have ht : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (Real.logb 2 (n j))) :=
      Nat.one_le_ceil_iff.mpr (by positivity)
    dsimp [momentK]
    omega
  obtain ⟨B, hB, _, _, hsmall⟩ := hj H p₀ S hmin hmax hExp F hF hpack (htwo.trans hK)
  have hsingle : components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ = {B} := by
    apply Finset.ext
    intro R
    constructor
    · intro hR
      by_cases heq : R = B
      · simpa only [Finset.mem_singleton] using heq
      · have hbound := (hsmall R hR heq).2.2.1
        have hpos : 0 < R.card := (component_connected _ hR).1.card_pos
        omega
    · intro hR
      have heq := Finset.mem_singleton.mp hR
      subst R
      exact hB
  rw [← exteriorCount_eq_original, exteriorCount, componentCount, hsingle]
  simp

/-- The selected induced cycle's actual component probability equals its
geometric weight. Chords are excluded by the strengthened retained filter;
connected complement is obtained from the proved component classification. -/
theorem eventually_selected_cycle_marginals
    (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H)
      (S : Selection H p₀ c σ (n j)), H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      ∀ C ∈ S.cycles, Cycle.probability C = cycleWeight C := by
  filter_upwards [eventually_small_family_complement_connected c σ hc hσ hσ20 n hn] with j hj
  intro H p₀ S hH hmin hmax hExp C hC
  have hsingle : ({C} : Finset (coreApexGraph H).CycleWord) ⊆ S.cycles := by simpa
  have hpack : IsCyclePacking (coreApexGraph H) {C} := by
    intro A hA B hB hne
    simp only [Finset.mem_singleton] at hA hB
    exact (hne (hA.trans hB.symm)).elim
  have hcomp := hj H p₀ S hmin hmax hExp {C} hsingle hpack (by simp)
  simp only [Finset.singleton_biUnion] at hcomp
  exact Cycle.probability_eq_weight (coreApex_connected H hH p₀) C
    (selected_vertices_cubic S hmin hmax C hC) (S.cycle_induced C hC) hcomp

end Erdos1016.Proof.SelectedCycleMarginals

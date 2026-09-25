import Erdos1016.Cycles.Selection.ComplementCutoffs
import Erdos1016.Cycles.Filtering.SelectedReturnTransport

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.SelectedComplementClassification
open BoundaryDecay CycleSupply SafeCore Nonbacktracking ConditionalMoments
open FewBranchSelectedCycles SelectedComplementGeometry SelectedComplementParameters
open SelectedReturnTransport CutoffLimits

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform geometry of deleting a disjoint tuple from the constructed
retained family. The giant contains the protector. All other components are
ordinary trees with at most one attachment per selected cycle. Both their
order bound and the exclusion of short external returns are proved from the
original retained selection and the manuscript's explicit cutoffs. -/
theorem eventually_selected_complement_classification
    (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H)
      (S : Selection H p₀ c σ (n j)),
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      ∀ (F : Finset (coreApexGraph H).CycleWord), F ⊆ S.cycles →
      IsCyclePacking (coreApexGraph H) F → F.card ≤ momentK σ (Real.logb 2 (n j)) →
      ∃ B ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ,
        ((coreApexGraph H).vertexCount : ℝ) / 2 < (B.card : ℝ) ∧
        apexProtector H S.W ⊆ B ∧
        ∀ R ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ, R ≠ B →
          R ⊆ (apexProtector H S.W)ᶜ ∧
          ((coreApexGraph H).toSimpleGraph.induce (↑R : Set _)).IsTree ∧
          R.card + 2 ≤ F.card ∧
          (∀ v ∈ R, (coreApexGraph H).degree v = 3) ∧
          ∀ C ∈ F, ∀ e d, e ∈ crossing (coreApexGraph H) R (Cycle.vertices C) →
            d ∈ crossing (coreApexGraph H) R (Cycle.vertices C) → e = d := by
  filter_upwards [eventually_component_budgets c σ hc hσ hσ20 n hn] with j hj
  obtain ⟨hh, hh2, hM, hMbound, hD, hgap, hKD⟩ := hj
  intro H p₀ S hmin hmax hExp F hF hpack hcard
  obtain ⟨B, hB, hbig, hWB, hsmall⟩ := selected_complement_giant S hmin hmax hh hh2 hExp F hF hpack hcard
  refine ⟨B, hB, hbig, hWB, ?_⟩
  intro R hR hRB
  obtain ⟨hout, horder, hno, hreg, hcut⟩ := hsmall R hR hRB
  have hRM : R.card ≤ componentOrderBound c σ (n j) := by exact_mod_cast horder.trans hMbound
  have htree := ConditionalComplementGeometry.small_complement_component_isTree F id R
    (componentOrderBound c σ (n j))
    (momentK σ (Real.logb 2 (n j)) * cutoffL σ (Real.logb 2 (n j)))
    (cutoffD (Real.logb 2 (n j))) (cutoffRc σ (Real.logb 2 (n j))) (cutoffQ σ (Real.logb 2 (n j)))
    hR hreg hno hM hRM hcut
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using cutoff_radius_bound σ (Real.logb 2 (n j))) hD hgap
    ((Nat.mul_le_mul_left 4 hcard).trans hKD)
    (fun C hC => selected_vertices_cubic S hmin hmax C (hF hC))
    (selected_noReturnThrough S F hF R hR hout) (by
      dsimp [cutoffQ]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcard) 2)
  exact ⟨hout, htree.1, htree.2.1, hreg, htree.2.2⟩

end Erdos1016.Proof.SelectedComplementClassification

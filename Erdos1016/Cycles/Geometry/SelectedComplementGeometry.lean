import Erdos1016.Cycles.Selection.RetainedSelection
import Erdos1016.Cycles.Geometry.BoundaryContactGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # Complement geometry of the constructed selected cycles

The protector and the cycle budget are furnished by `Selection`. The giant
component is constructed by expansion. No distance in the apex graph is
used: all subsequent return hypotheses are localized to an actual ordinary
complementary component, disjoint from the apex-containing protector.
-/

noncomputable section
namespace Erdos1016.Proof.SelectedComplementGeometry
open SafeCore CycleSupply BoundaryDecay Nonbacktracking
open FewBranchSelectedCycles CutoffLimits
open CutoffAvoidance ConditionalMoments
open CycleDeletionComponents
open scoped BigOperators

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {H : PhysicalGraph} {p₀ : CorePin H} {c σ n : ℝ}

theorem selected_vertices_cubic (S : Selection H p₀ c σ n)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (C : (coreApexGraph H).CycleWord) (hC : C ∈ S.cycles)
    (v : (coreApexGraph H).Vertex) (hv : v ∈ Cycle.vertices C) :
    (coreApexGraph H).degree v = 3 := by
  have hout := S.cycle_avoids_protector C hC hv
  have hvz : v ≠ coreApexVertex H := by
    intro heq
    exact (Finset.mem_compl.mp hout) (heq ▸ Finset.mem_insert_self _ _)
  rcases apex_vertex_cases H v with ⟨u, rfl⟩ | heq
  · exact coreApex_ordinary_cubic H hmin hmax _ (by
      simp [coreApexInterior, physicalShore, coreOrdinary, coreVertexLift])
  · exact (hvz heq).elim

theorem selected_union_card_cut_le (S : Selection H p₀ c σ n)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (F : Finset (coreApexGraph H).CycleWord) (hF : F ⊆ S.cycles)
    (hpack : IsCyclePacking (coreApexGraph H) F)
    (hcard : F.card ≤ momentK σ (Real.logb 2 n)) :
    (F.biUnion Cycle.vertices).card ≤ momentK σ (Real.logb 2 n) * cutoffL σ (Real.logb 2 n) ∧
      cutSize (coreApexGraph H) (F.biUnion Cycle.vertices) ≤
        momentK σ (Real.logb 2 n) * cutoffL σ (Real.logb 2 n) := by
  have hsum : (∑ C ∈ F, BoundaryDecay.Cycle.length C) ≤
      momentK σ (Real.logb 2 n) * cutoffL σ (Real.logb 2 n) := by
    calc
      _ ≤ ∑ _C ∈ F, cutoffL σ (Real.logb 2 n) :=
        Finset.sum_le_sum fun C hC => (S.cycle_length_bounds C (hF hC)).2
      _ = F.card * cutoffL σ (Real.logb 2 n) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  constructor
  · calc
      _ ≤ ∑ C ∈ F, (Cycle.vertices C).card := Finset.card_biUnion_le
      _ = ∑ C ∈ F, BoundaryDecay.Cycle.length C := by
        simp only [BoundaryDecay.Cycle.length_eq_vertices_card]
      _ ≤ _ := hsum
  · exact (cycleFamily_cut_le_sum_lengths F hpack
      (fun C hC => selected_vertices_cubic S hmin hmax C (hF hC))).trans hsum

/-- Deleting any disjoint subfamily through the moment order has a giant
containing the constructed protector. Every other component has order at most
`KL/κ`, lies wholly outside the protector, is cubic, and inherits girth `D`.
The cut-size bounds used in the expansion argument are derived internally. -/
theorem selected_complement_giant (S : Selection H p₀ c σ n)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (hh : 0 < c * n ^ (-(1 / 8 : ℝ))) (hh2 : c * n ^ (-(1 / 8 : ℝ)) ≤ 2)
    (hExp : HasExpansion H Finset.univ (c * n ^ (-(1 / 8 : ℝ))))
    (F : Finset (coreApexGraph H).CycleWord) (hF : F ⊆ S.cycles)
    (hpack : IsCyclePacking (coreApexGraph H) F)
    (hcard : F.card ≤ momentK σ (Real.logb 2 n)) :
    ∃ B ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ,
      ((coreApexGraph H).vertexCount : ℝ) / 2 < (B.card : ℝ) ∧
      apexProtector H S.W ⊆ B ∧
      ∀ R ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ, R ≠ B →
        R ⊆ (apexProtector H S.W)ᶜ ∧
        (R.card : ℝ) ≤ ((momentK σ (Real.logb 2 n) * cutoffL σ (Real.logb 2 n) : ℕ) : ℝ) /
          ((c * n ^ (-(1 / 8 : ℝ))) / 2) ∧
        NoShortCycles (coreApexGraph H) R (cutoffD (Real.logb 2 n)) ∧
        (∀ v ∈ R, (coreApexGraph H).degree v = 3) ∧
        cutSize (coreApexGraph H) R ≤
          momentK σ (Real.logb 2 n) * cutoffL σ (Real.logb 2 n) := by
  have hb := selected_union_card_cut_le S hmin hmax F hF hpack hcard
  have hsize : ((F.biUnion Cycle.vertices).card : ℝ) ≤
      (momentK σ (Real.logb 2 n) : ℝ) * cutoffL σ (Real.logb 2 n) := by exact_mod_cast hb.1
  have hcut : (cutSize (coreApexGraph H) (F.biUnion Cycle.vertices) : ℝ) ≤
      (momentK σ (Real.logb 2 n) : ℝ) * cutoffL σ (Real.logb 2 n) := by exact_mod_cast hb.2
  have hdiv := div_le_div_of_nonneg_right hcut (by positivity :
    0 ≤ (c * n ^ (-(1 / 8 : ℝ))) / 2)
  have hg := ApexGirthPacking.apex_noShortCycles_of_core_noShortCycles
    H S.W (cutoffD (Real.logb 2 n)) S.no_short
  obtain ⟨B, hB, hbig, hWB, hsmall⟩ := ProtectedApexComponents.two_scale_moment_component_bound
    H _ hh hh2 hExp hmin hmax p₀ (momentK σ (Real.logb 2 n)) (cutoffL σ (Real.logb 2 n))
    (cutoffD (Real.logb 2 n)) (cutoffD (Real.logb 2 n)) (apexProtector H S.W)
    S.protector_connected (Finset.mem_insert_self _ _) hg le_rfl F hpack hcard
    (fun C hC => (S.cycle_length_bounds C (hF hC)).2)
    (fun C hC => S.cycle_avoids_protector C (hF hC))
    (by rw [apexProtector_card]; push_cast; linarith [S.large])
    (by linarith [S.room])
  refine ⟨B, hB, hbig, hWB, ?_⟩
  intro R hR hRB
  obtain hsame | ⟨_, horder, hno, _, hreg⟩ := hsmall R hR
  · exact (hRB hsame).elim
  have hout : R ⊆ (apexProtector H S.W)ᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr fun hvW =>
      (Finset.disjoint_left.mp (components_disjoint _ hR hB hRB)) hv (hWB hvW)
  exact ⟨hout, horder, hno, hreg, (component_cut_le_removed_cut _ hR).trans hb.2⟩



end Erdos1016.Proof.SelectedComplementGeometry

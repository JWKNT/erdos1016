import Erdos1016.Nonbacktracking.Trace.EvenHarmonicMass
import Erdos1016.Cycles.Filtering.InducedTraceSurvival
import Erdos1016.Cycles.Selection.WeightedSubfamily
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Quantitative retained cycle supply from the proved even trace estimate

The even trace estimate suffices for an absolute positive decay constant.
Keeping only half of each of the two survival factors gives an explicit
logarithmic supply, without assuming a paired trace estimate.
-/

noncomputable section
namespace Erdos1016.Proof.QuantitativeRetainedSupply
open scoped BigOperators
open Erdos1016.Nonbacktracking Erdos1016.BoundaryDecay
open Erdos1016.Proof.RejectedCycleEncoding
open Erdos1016.Proof.ExternalReturnFilter
open Erdos1016.Proof.EvenHarmonicMass
open Erdos1016.Proof.InducedRetainedCycleFilter Erdos1016.Proof.InducedRetainedTraceSupply

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem log_ratio_le_reciprocal_interval (M K : ℕ) (hM : 0 < M)
    (hMK : M ≤ K + 1) :
    Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      ∑ k ∈ Finset.Icc M K, (1 : ℝ) / (k : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMKR : (M : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast hMK
  calc
    _ = ∫ t in (M : ℝ)..((K + 1 : ℕ) : ℝ), t⁻¹ := by
      rw [integral_inv (by
        have hh : (M : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast hMK
        simp [Set.uIcc_of_le hh, not_le.mpr hMR])]
    _ ≤ ∑ k ∈ Finset.Ico M (K + 1), (k : ℝ)⁻¹ :=
      (inv_antitoneOn_Icc_right hMR).integral_le_sum_Ico hMK
    _ = _ := by simp only [Nat.add_one, Nat.Ico_succ_right, one_div]

theorem traceMass_mono (G : PhysicalGraph) {L L' : ℕ} (hL : L ≤ L') :
    nonbacktrackingTraceMass (G := G) L ≤
      nonbacktrackingTraceMass (G := G) L' := by
  unfold nonbacktrackingTraceMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hL⟩
  · intro k hk hk'
    positivity

theorem traceMass_nonneg (G : PhysicalGraph) (L : ℕ) :
    0 ≤ nonbacktrackingTraceMass (G := G) L := by
  unfold nonbacktrackingTraceMass
  exact Finset.sum_nonneg fun k hk => by positivity

/-- A concrete finite estimate on the actual filtered physical cycle family.
All error premises are numerical; there is no trace-mass or cycle-supply
premise. The girth is the usual simple closed-walk girth. -/
theorem retained_weight_ge_log_ratio
    (G : PhysicalGraph) (M K L s D q : ℕ) (V : Finset G.Vertex)
    (hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hKL : 2 * K ≤ L)
    (hmain : (degreeTwoCount G : ℝ) * (2 * (K : ℝ)) / G.vertexCount ≤ 1)
    (herr : 2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(M : ℝ)) ≤ 1 / 4)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) (hq : 1 ≤ q) (hqL : q ≤ L)
    (hcollision : (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s ≤ 1 / 2)
    (hreturn : (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 2) :
    (1 / 64 : ℝ) * Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      cycleWeightSum (inducedAcceptedCycles G V (shortCycleWords G L) q) := by
  have htrace := (normalized_even_trace_lower_sum_ge_reciprocal_interval
    G M K hM hn hmain herr).trans
    ((normalized_even_trace_sum_lower G hmin hmax hn M K hM).trans
      ((normalized_even_terms_le_traceMass G M K hM).trans (traceMass_mono G hKL)))
  have hlog := log_ratio_le_reciprocal_interval M K hM hMK
  have htraceLog : (1 / 16 : ℝ) * Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      nonbacktrackingTraceMass (G := G) L := by linarith
  have hproduct := induced_retained_weight_ge_trace_product G L s D q V
    hmin hmax hg hshort hs hq hqL (hreturn.trans (by norm_num))
  have hfactor : (1 / 4 : ℝ) ≤
      (1 - (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) *
      (1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) := by
    have hh := mul_le_mul (show (1 / 2 : ℝ) ≤
      1 - (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s by linarith)
      (show (1 / 2 : ℝ) ≤ 1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ s by linarith) (by norm_num) (by linarith [hreturn])
    norm_num at hh ⊢
    exact hh
  have hsurvive := mul_le_mul_of_nonneg_right hfactor (traceMass_nonneg G L)
  rw [mul_assoc] at hsurvive
  linarith

theorem cycle_length_gt_of_girth (G : PhysicalGraph) (D : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) (C : G.CycleWord) :
    D < BoundaryDecay.Cycle.length C := by
  obtain ⟨u, p, hp, rfl⟩ := exists_cycle_walk_of_cycleWord G C
  rw [cycleWordOfWalk_length]
  exact hg u p hp

/-- Deterministic selection from the concrete retained family, with the
single-cycle overshoot derived from ordinary graph girth. -/
theorem exists_selected_retained_family
    (G : PhysicalGraph) (M K L s D q : ℕ) (V : Finset G.Vertex) (τ : ℝ)
    (hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hKL : 2 * K ≤ L)
    (hmain : (degreeTwoCount G : ℝ) * (2 * (K : ℝ)) / G.vertexCount ≤ 1)
    (herr : 2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(M : ℝ)) ≤ 1 / 4)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) (hq : 1 ≤ q) (hqL : q ≤ L)
    (hcollision : (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s ≤ 1 / 2)
    (hreturn : (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 2)
    (hτ : 0 ≤ τ)
    (hτmax : τ ≤ (1 / 64 : ℝ) * Real.log ((K + 1 : ℕ) / (M : ℝ))) :
    ∃ F ⊆ inducedAcceptedCycles G V (shortCycleWords G L) q,
      τ ≤ cycleWeightSum F ∧ cycleWeightSum F ≤ τ + 1 / (2 : ℝ) ^ (D + 1) := by
  apply CycleSupply.exists_cycleWeight_subfamily_between_threshold _ D τ hτ
  · intro C hC
    exact cycle_length_gt_of_girth G D hg C
  · exact hτmax.trans (retained_weight_ge_log_ratio G M K L s D q V
      hmin hmax hn hM hMK hKL hmain herr hg hshort hs hq hqL hcollision hreturn)

end Erdos1016.Proof.QuantitativeRetainedSupply

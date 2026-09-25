import Erdos1016.Probability.Conditional.SelectedCycleLoad
import Erdos1016.Probability.Moments.SelectedCycleMarginals
import Erdos1016.Probability.Avoidance.RetainedCycleBound

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology BigOperators
namespace Erdos1016.Proof.SelectedForestDecay
open BoundaryDecay CycleSupply SafeCore FewBranchSelectedCycles
open CutoffLimits CutoffAvoidance SelectedLoadParameters
open SelectedComplementClassification SelectedComplementGeometry SelectedCycleMarginals
open SelectedConditionalLoad CycleExtensionProbability

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual selected retained family implies the stated forest decay.
The finite avoidance bound is instantiated with exact marginal laws,
complement geometry, and the proved conditional neighbor row. -/
theorem eventually_selected_forest_decay
    (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H)
      (S : Selection H p₀ c σ (n j)), H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      coreBoundaryAverage H ≤ (2 : ℝ) ^ (-(σ / 128) * Real.sqrt (Real.logb 2 (n j))) := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  filter_upwards [eventually_selected_complement_classification c σ hc hσ hσ20 n hn,
    eventually_selected_cycle_marginals c σ hc hσ hσ20 n hn,
    eventually_selected_conditional_load c σ hc hσ hσ20 n hn,
    EvenTraceParameters.even_trace_cutoffs_avoidance_rate σ hσ hσ20 _ hx,
    (evenTraceTarget_tendsto_atTop σ hσ _ hx).eventually_gt_atTop 0,
    hx.eventually_gt_atTop 0] with j hgeom hmarg hload hrate hmean hxj
  intro H p₀ S hH hmin hmax hExp
  let x := Real.logb 2 (n j)
  let G := coreApexGraph H
  let J := (apexProtector H S.W)ᶜ
  let K := momentK σ x
  let q := cutoffQ σ x
  let d := cutoffLoad σ x
  let lam := cycleWeightSum S.cycles
  have hparams := cutoff_load_discrete_conditions hσ hxj
  have hq : 1 ≤ q := by dsimp [q, cutoffQ]; omega
  have hKq : K ≤ q + 1 := by
    have ht : K ≤ K * (2 * cutoffRc σ x + 1) := Nat.le_mul_of_pos_right K (by omega)
    dsimp [q, cutoffQ, K] at *
    omega
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hpositive : 0 < lam := hmean.trans_le S.mean_bounds.1
  have hgeometry : ∀ F ⊆ S.cycles, IsCyclePacking G F → F.card ≤ K →
      ∃ B ∈ components G (tupleVertices F)ᶜ,
        ∀ R ∈ components G (tupleVertices F)ᶜ, R ≠ B →
          R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
          (∀ v ∈ R, G.degree v = 3) ∧ R.card + 2 ≤ K ∧
          ∀ C ∈ F, ∀ e f, e ∈ crossing G R (Cycle.vertices C) →
            f ∈ crossing G R (Cycle.vertices C) → e = f := by
    intro F hF hp hcard
    obtain ⟨B, hB, _, _, hsmall⟩ := hgeom H p₀ S hmin hmax hExp F hF hp hcard
    refine ⟨B, hB, ?_⟩
    intro R hR hRB
    obtain ⟨hRJ, htree, hsize, hreg, hcontact⟩ := hsmall R hR hRB
    exact ⟨hRJ, htree.2, hreg, hsize.trans hcard, hcontact⟩
  have hv₀ : ∀ C ∈ S.cycles, coreApexVertex H ∉ Cycle.vertices C := by
    intro C hC hv
    exact (Finset.mem_compl.mp (S.cycle_avoids_protector C hC hv)) (Finset.mem_insert_self _ _)
  have hav := RetainedCycleAvoidance.finite_avoidance_le (coreApex_connected H hH p₀)
    J S.cycles K q hparams.1 hparams.2.1 hq hKq d hd S.cycle_avoids_protector
    (fun C hC => selected_vertices_cubic S hmin hmax C hC) S.cycle_induced
    (hmarg H p₀ S hH hmin hmax hExp) (coreApexVertex H) hv₀ hpositive hgeometry
    (hload H p₀ S hmin hmax hExp)
  have hforest : coreBoundaryAverage H ≤
      Finite.density (fun z : G.CycleSpace => ∀ C ∈ S.cycles, ¬ Cycle.Event C z) := by
    rw [coreBoundaryAverage_eq_physical_fraction]
    apply forest_fraction_le_no_cycle_events
    intro C hC v hv
    obtain ⟨u, rfl⟩ | heq := apex_vertex_cases H v
    · simp [coreApexInterior, physicalShore, coreOrdinary, coreVertexLift]
    · exact (hv₀ C hC (heq ▸ hv)).elim
  exact hrate _ lam d S.mean_bounds.1 S.mean_bounds.2 hd le_rfl (hforest.trans hav)

end Erdos1016.Proof.SelectedForestDecay

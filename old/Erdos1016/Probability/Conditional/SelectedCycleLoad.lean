import Erdos1016.Probability.Conditional.ResidualCoreLoad
import Erdos1016.Probability.Conditional.OrdinaryNeighborhood
import Erdos1016.Cycles.Geometry.SelectedComplementClassification
import Erdos1016.Cycles.Selection.ConditionalLoadCutoffs

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Erdos1016.Proof.SelectedConditionalLoad

open BoundaryDecay CycleSupply SafeCore FewBranchSelectedCycles
open SelectedComplementClassification SelectedComplementGeometry SelectedReturnTransport
open CutoffLimits CutoffAvoidance SelectedLoadParameters
open CycleExtensionProbability CycleProximity

local instance selectedLoadDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The conditional neighbor row for the family actually selected from the
trace supply. Every geometric input to the residual-core count is discharged
by the protector, return filter, and complement classification. -/
theorem eventually_selected_conditional_load
    (c σ : ℝ) (hc : 0 < c) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H)
      (S : Selection H p₀ c σ (n j)),
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      ∀ (F : Finset (coreApexGraph H).CycleWord), F ⊆ S.cycles →
      IsCyclePacking (coreApexGraph H) F → F.card < momentK σ (Real.logb 2 (n j)) →
      ∀ C ∈ S.cycles,
      (∑ D ∈ eligible (coreApexGraph H) S.cycles F,
        if Near (coreApexGraph H) (apexProtector H S.W)ᶜ (cutoffQ σ (Real.logb 2 (n j))) C D
        then conditionalDensity (tupleEvent F) (Cycle.Event D) else 0) ≤
        cutoffLoad σ (Real.logb 2 (n j)) := by
  have hx := (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  filter_upwards [eventually_selected_complement_classification c σ hc hσ hσ20 n hn,
    hx.eventually_ge_atTop 8] with j hj hxj
  intro H p₀ S hmin hmax hExp F hF hpack hcard C hC
  let G := coreApexGraph H
  let J := (apexProtector H S.W)ᶜ
  let x := Real.logb 2 (n j)
  let K := momentK σ x
  let E := eligible G S.cycles F
  change 8 ≤ x at hxj
  change F.card < momentK σ x at hcard
  have hparams := cutoff_load_discrete_conditions hσ (show 0 < x by linarith)
  have hs : 0 < cutoffS x := by
    have hd : 4 ≤ cutoffD x := by
      apply Nat.le_floor
      linarith
    dsimp [cutoffS]
    omega
  have hshort : 2 * cutoffS x ≤ cutoffD x := by dsimp [cutoffS]; omega
  have hdegree : ∀ v ∈ J, G.degree v = 3 := by
    intro v hv
    have hnz : v ≠ coreApexVertex H := by
      intro heq
      exact (Finset.mem_compl.mp hv) (heq ▸ Finset.mem_insert_self _ _)
    rcases apex_vertex_cases H v with ⟨u, rfl⟩ | heq
    · exact coreApex_ordinary_cubic H hmin hmax _ (by
        simp [coreApexInterior, physicalShore, coreOrdinary, coreVertexLift])
    · exact (hnz heq).elim
  have hE : ∀ D ∈ E, D ∈ S.cycles ∧ Disjoint (tupleVertices F) (Cycle.vertices D) := by
    intro D hD
    exact Finset.mem_filter.mp hD
  have hcomp : ∀ D ∈ E, ∃ B ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ,
      ∀ R ∈ components G (tupleVertices F ∪ Cycle.vertices D)ᶜ, R ≠ B →
        R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
        (∀ v ∈ R, G.degree v = 3) ∧ R.card + 2 ≤ K ∧
        (∀ e f, e ∈ crossing G R (Cycle.vertices D) →
          f ∈ crossing G R (Cycle.vertices D) → e = f) := by
    intro D hD
    have hDF := (hE D hD).2
    have hFD : ∀ A ∈ F, Disjoint (Cycle.vertices A) (Cycle.vertices D) := by
      intro A hA
      exact hDF.mono_left (by intro v hv; exact Finset.mem_biUnion.mpr ⟨A, hA, hv⟩)
    have hpack' : IsCyclePacking G (insert D F) := by
      intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hAF
      · rcases Finset.mem_insert.mp hB with rfl | hBF
        · exact (hne rfl).elim
        · exact (hFD B hBF).symm
      · rcases Finset.mem_insert.mp hB with rfl | hBF
        · exact hFD A hAF
        · exact hpack A hAF B hBF hne
    have hsub : insert D F ⊆ S.cycles := Finset.insert_subset_iff.mpr ⟨(hE D hD).1, hF⟩
    have hcard' : (insert D F).card ≤ momentK σ x := (Finset.card_insert_le _ _).trans (by omega)
    obtain ⟨B, hB, _, _, hsmall⟩ := hj H p₀ S hmin hmax hExp (insert D F) hsub hpack' hcard'
    have hset : (insert D F).biUnion Cycle.vertices = tupleVertices F ∪ Cycle.vertices D := by
      simp only [Finset.biUnion_insert, tupleVertices, Finset.union_comm]
    rw [hset] at hB hsmall
    refine ⟨B, hB, ?_⟩
    intro R hR hRB
    obtain ⟨hRJ, htree, hsize, hcub, hcontact⟩ := hsmall R hR hRB
    exact ⟨hRJ, htree.2, hcub, hsize.trans hcard', hcontact D (Finset.mem_insert_self _ _)⟩
  have hload := ResidualCoreCycleLoad.vertexLoad_le G J F E K (cutoffQ σ x)
    (cutoffDelta σ x) (cutoffD x) (cutoffS x) (cutoffL σ x)
    hparams.2.1 hparams.2.2.1 hparams.2.2.2 hs hshort hdegree
    (ApexGirthPacking.apex_noShortCycles_of_core_noShortCycles
      H S.W (cutoffD x) S.no_short)
    (fun A hA => S.cycle_avoids_protector A (hF hA)) hpack
    (fun A hA => selected_noReturnWithin S A (hF hA))
    (fun D hD => S.cycle_avoids_protector D (hE D hD).1)
    (fun D hD => (hE D hD).2) (fun D hD => S.cycle_induced D (hE D hD).1)
    (by
      intro D hD
      have hh := S.cycle_length_bounds D (hE D hD).1
      change cutoffD x < BoundaryDecay.Cycle.length D ∧ BoundaryDecay.Cycle.length D ≤ cutoffL σ x at hh
      exact ⟨lt_of_le_of_lt (by dsimp [cutoffS]; omega) hh.1, hh.2⟩) hcomp
  have hnear := OrdinaryCycleNeighborhood.neighbor_mass_le_conditional_bound G J E
    (fun D => conditionalDensity (tupleEvent F) (Cycle.Event D))
    (cutoffQ σ x) (cutoffL σ x) (cutoffS x)
    (F.card * Nat.ceil (((cutoffS x - 1 : ℕ) : ℝ) / cutoffDelta σ x))
    (fun v hv => (hdegree v hv).le) hload
    (fun D _ => div_nonneg (Finite.density_nonneg _) (Finite.density_nonneg _))
    C (S.cycle_length_bounds C hC).2
  exact hnear.trans (conditional_neighbor_bound_le_cutoffLoad σ x F.card (Nat.le_of_lt hcard))

end Erdos1016.Proof.SelectedConditionalLoad

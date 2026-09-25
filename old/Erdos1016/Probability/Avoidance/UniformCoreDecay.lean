import Erdos1016.Probability.Avoidance.SelectedForestBound
import Erdos1016.Probability.Avoidance.ClosedCubicRate
import Erdos1016.Probability.Avoidance.UniformCoreBound

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.UniformCoreDecayProof
open BoundaryDecay CycleSupply SafeCore FewBranchSelectedCycles SelectedForestDecay

/-- Uniform forest decay for all connected physical graphs of minimum
degree two and maximum degree three at the manuscript's expansion scale.
The closed cubic case and both branches of the packing dichotomy are included. -/
theorem eventually_core_decay
    (c B σ : ℝ) (hc : 0 < c) (hB : 0 < B) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    ∀ᶠ j in atTop, ∀ H : PhysicalGraph,
      (H.vertexCount : ℝ) = n j → H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      (Nonbacktracking.degreeTwoCount H : ℝ) ≤ B * (n j) ^ (7 / 8 : ℝ) →
      coreBoundaryAverage H ≤ (2 : ℝ) ^ (-(σ / 128) * Real.sqrt (Real.logb 2 (n j))) := by
  classical
  filter_upwards [eventually_decay_or_selection c B σ hc hB hσ hσ20 n hn hnge,
    eventually_selected_forest_decay c σ hc hσ hσ20 n hn,
    ClosedCubicDecay.closed_cubic_stretched_eventually (σ / 128) n hn]
    with j hcases hfew hclosed
  intro H horder hH hmin hmax hExp hb
  by_cases hp : Nonempty (CorePin H)
  · let p₀ := Classical.choice hp
    rcases hcases H p₀ horder hH hmin hmax hExp hb with hdecay | hsel
    · exact hdecay
    · exact hfew H p₀ (Classical.choice hsel) hH hmin hmax hExp
  · exact hclosed H (not_nonempty_iff.mp hp) horder hH hmin hmax

/-- A concrete universal positive coefficient and one uniform finite onset
for the normalized physical cores used by the final descent. -/
theorem exists_uniform_core_decay :
    ∃ N₀ : ℕ, UniformCoreDecay.Estimate N₀ (1 / 12800) := by
  let c := coreExpansion canonicalParameters
  let B := coreBudget canonicalParameters
  let n : ℕ → ℝ := fun j => (j : ℝ) + 1
  have hn : Tendsto n atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hgood := eventually_core_decay c B (1 / 100)
    (coreExpansion_pos canonicalParameters) (coreBudget_pos canonicalParameters)
    (by norm_num) (by norm_num) n hn (fun j => by dsimp [n]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hgood
  refine ⟨j₀ + 1, ?_⟩
  intro H hH hdeg hExp hb hlarge
  have hN : 1 ≤ H.vertexCount := by omega
  have hnj : n (H.vertexCount - 1) = (H.vertexCount : ℝ) := by
    dsimp [n]
    rw [Nat.cast_sub hN]
    push_cast
    ring
  have h := hj₀ (H.vertexCount - 1) (by omega) H hnj.symm hH
    (fun v => (hdeg v).1) (fun v => (hdeg v).2)
    (by simpa only [hnj, c, canonicalParameters, show (7 / 8 : ℝ) - 1 = -(1 / 8 : ℝ) by norm_num] using hExp)
    (by simpa only [hnj, B, canonicalParameters] using hb)
  norm_num only [show (1 / 100 : ℝ) / 128 = 1 / 12800 by norm_num] at h
  simpa only [hnj] using h

end Erdos1016.Proof.UniformCoreDecayProof

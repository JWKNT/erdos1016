import Erdos1016.Decomposition.Descent.NormalizedStopping
import Erdos1016.Decomposition.Descent.HighRankRootContradiction
import Erdos1016.Cleanup.Support.ConnectedHubInput
import Erdos1016.Cleanup.Support.CanonicalWitnessInput
import Erdos1016.Cleanup.CleanupConstruction

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Erdos1016.Proof.UniformDecayReduction

open Erdos1016 Extremal CleanupSpecification
open AnalyticStoppingThreshold FiniteForestDescent HighRankRootContradiction

/-- One extra unit in the quartic exponent absorbs the `R+1` difference
between the capacity parameter and the realizing graph's actual cycle rank. -/
theorem actual_rank_scale (R C s r : ℕ) (hR : 1 ≤ R) (hC : 1 ≤ C)
    (hscale : 2 ^ ((C + 1) * R ^ 4) ≤ s) (hnear : s ≤ r + (R + 1)) :
    2 ^ (C * R ^ 4) ≤ r := by
  have hRp : R ≤ R ^ 4 := by
    calc R = R ^ 1 := by simp
         _ ≤ R ^ 4 := Nat.pow_le_pow_right hR (by omega)
  have he : R ≤ C * R ^ 4 := hRp.trans (by nlinarith)
  have hlin : R + 1 ≤ 2 ^ (C * R ^ 4) :=
    (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := R))).trans
      (Nat.pow_le_pow_right (by decide) he)
  have hpow : 2 ^ (C * R ^ 4 + 1) ≤ 2 ^ ((C + 1) * R ^ 4) := by
    apply Nat.pow_le_pow_right (by decide)
    have : 1 ≤ R ^ 4 := one_le_pow₀ hR
    nlinarith
  rw [pow_succ] at hpow
  omega

/-- The complete Section 10 probability estimate, for arbitrary possibly
disconnected owners, follows from the single uniform normalized-core decay
estimate. Cleanup, exact witness transport, finite descent and all choices
of constants are constructed here. -/
theorem forestProbabilityBound {N₀ : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hdecay : UniformCoreDecay.Estimate N₀ γ) :
    ForestProbabilityReduction.WitnessForestProbabilityBound := by
  classical
  let T := stoppingThreshold N₀ γ
  let A := quadraticExponent N₀ γ
  let m := packingCoefficient T
  let C := A * (1487 + m) ^ 2 + 8
  let Rmin := max 3926 (1487 + 2 * m)
  refine ⟨C + 1, Rmin, by dsimp [C]; omega, by dsimp [Rmin]; omega, ?_⟩
  intro R s hR hscale G hGr _ _ hcov hcount
  by_contra hnot
  have hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability
        (witnessSupportEdges G (Capacity.canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)) :=
    lt_of_not_ge hnot
  have hRbig : 3926 ≤ R := (le_max_left _ _).trans hR
  obtain ⟨D, hDR, hDr, _⟩ := CanonicalWitnessInput.canonical_cleanupWitnessData
    G R (C + 1) s (by omega) (by dsimp [C]; omega) hscale hGr hcov hcount hprob
  let I := ConnectedHubInput.input G D
  have hIR : I.R = R := hDR
  have hir : I.r = G.cycleRank := hDr
  obtain ⟨O, hext⟩ := CleanupConstruction.exists_cleanup_output (PhysicalGraph.connectByHub G)
    I (by omega)
  have hrank : 2 ^ (C * I.R ^ 4) ≤ I.r := by
    rw [hIR, hir]
    exact actual_rank_scale R C s G.cycleRank (by omega) (by dsimp [C]; omega)
      hscale (HighCycleOutsideRank.rank_ge_of_high_cycle_count G R s (by omega) hcount)
  have hadd := NormalizedAnalyticStopping.cleanup_root_additive_bound hγ hdecay O (by omega)
  apply ExponentialRootComparison.contradict_additive_root_bound
    I.R C A 1487 m I.r O.root.card (cutEdges O.Γ O.root).card
    (exteriorComponentCount O.Γ O.root) (leafPackingThreshold T I.R) T
    (by omega) (by rw [hIR]; exact (le_max_right _ _).trans hR)
    (by dsimp [C]; nlinarith) hrank O.root_order O.root_cut_bound hext
    (leafPackingThreshold_le_quadratic T I.R (by omega))
    (stoppingThreshold_le_two_pow N₀ γ)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hadd

/-- The manuscript's final theorem now depends on precisely the uniform
analytic core decay estimate; no cleanup or forest descent certificates remain. -/
theorem mainTheorem {N₀ : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hdecay : UniformCoreDecay.Estimate N₀ γ) : Problem1016.MainTheorem :=
  ForestProbabilityReduction.mainTheorem_of_forestProbabilityBound
    (forestProbabilityBound hγ hdecay)

end Erdos1016.Proof.UniformDecayReduction

end

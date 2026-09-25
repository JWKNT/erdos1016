import Erdos1016.Graph.Cubicization.MarkedReduction
import Erdos1016.Extremal.Recurrence.WitnessReduction
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-! Transfer a uniform bound for the constructed marked multigraph back to
the precise forest estimate used by the extremal recurrence. -/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ShortProof

/-- The remaining estimate can be proved in the logarithmic rank parameter
on marked cubic multigraphs. All changes of graph and of parameter are
discharged here. -/
theorem fewComponentForestEstimate_of_marked_bound
    (hforest : ∀ᶠ x : ℝ in atTop, ∀ (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex),
      Γ.toSimpleGraph.Connected → (∀ v, Γ.degree v ≤ 3) →
      (∀ v, v ∉ P → Γ.degree v = 3) →
      (Γ.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) →
      100 * (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤ x →
      Γ.regionForestProbability Pᶜ ≤
        (1 / 2 : ℝ) + 20 / Real.logb 2 (Real.logb 2 x)) :
    FewComponentForestEstimate := by
  have ht : Tendsto (fun r : ℕ => Real.logb 2 (r : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨rmin, hrmin⟩ := (eventually_atTop.mp (ht.eventually hforest))
  refine ⟨max rmin 1, ?_⟩
  intro G hG hr F hF hsize hcomponents
  have hrpos : 0 < G.cycleRank := by omega
  have hrR : (0 : ℝ) < G.cycleRank := by exact_mod_cast hrpos
  let x := Real.logb 2 (G.cycleRank : ℝ)
  have hpow : (2 : ℝ) ^ x = G.cycleRank :=
    Real.rpow_logb (by norm_num) (by norm_num) hrR
  have hhalf : (2 : ℝ) ^ (x / 2) = Real.sqrt (G.cycleRank : ℝ) := by
    rw [show x / 2 = x * (1 / 2) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hpow, Real.sqrt_eq_rpow]
  obtain ⟨Γ, P, hconn, hrank, hdeg, hcubic, _, hcard, hcomp, hprob⟩ :=
    exists_marked_subcubic_reduction G hG F hF
  have hmark : (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat, hhalf]
    have hs : ((witnessSupportEdges G F).card : ℝ) ^ 2 ≤ G.cycleRank := by
      exact_mod_cast hsize
    have hroot := Real.sq_sqrt hrR.le
    nlinarith [Real.sqrt_nonneg (G.cycleRank : ℝ),
      show (0 : ℝ) ≤ (witnessSupportEdges G F).card by positivity]
  have hc : 100 *
      (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤ x := by
    have hcompR :
        (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤
          Nat.card (cycleUnionGraph G F).ConnectedComponent := by exact_mod_cast hcomp
    dsimp [x]
    linarith
  have hbound := hrmin G.cycleRank (by omega) Γ P hconn (fun v => (hdeg v).2)
    hcubic (by rw [hrank]; exact hpow.symm) hmark hc
  exact hprob.trans hbound

end Erdos1016.ShortProof

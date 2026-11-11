import Erdos1016.Probability.Avoidance.MarkedForestReduction

set_option autoImplicit false

/-!
# The polynomial forest estimate: statements and the reduction to marked graphs

This file states the forest estimate with a polynomial error term. The first
statement is for physical graphs and witness families. The second statement is
for marked multigraphs with all degrees at most three. The reduction from the
second statement to the first is proved here. It is the reduction of
`Erdos1016.ShortProof.fewComponentForestEstimate_of_marked_bound` with another
error term.

Neither statement is proved in this file. Each is a proposition, not an axiom.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.PolynomialBound
open PhysicalGraph ShortProof

/-- The forest estimate with a polynomial error. The hypotheses are those of
`ShortProof.FewComponentForestEstimate`. The error term is a negative power of
the cycle rank. -/
def PolynomialForestEstimate : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ rmin : ℕ, ∀ (G : PhysicalGraph), G.IsConnected →
    rmin ≤ G.cycleRank →
    ∀ F : Finset G.CycleWord, F.Nonempty →
      (witnessSupportEdges G F).card ^ 2 ≤ G.cycleRank →
      100 * (Nat.card (cycleUnionGraph G F).ConnectedComponent : ℝ) ≤
        Real.logb 2 (G.cycleRank : ℝ) →
      outsideForestProbability G (witnessSupportEdges G F) ≤
        (1 / 2 : ℝ) + (G.cycleRank : ℝ) ^ (-κ)

/-- The same estimate for marked multigraphs. The cycle rank is `2 ^ x`. Every
vertex has degree at most three, and every vertex outside the marked set `P`
has degree three. The marked set has at most `2 * 2 ^ (x / 2)` vertices and
induces at most `x / 100` components. -/
def PolynomialMarkedBound : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex),
      Γ.toSimpleGraph.Connected → (∀ v, Γ.degree v ≤ 3) →
      (∀ v, v ∉ P → Γ.degree v = 3) →
      (Γ.cycleRank : ℝ) = (2 : ℝ) ^ x →
      (P.card : ℝ) ≤ 2 * (2 : ℝ) ^ (x / 2) →
      100 * (Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent : ℝ) ≤ x →
      Γ.regionForestProbability Pᶜ ≤ (1 / 2 : ℝ) + (2 : ℝ) ^ (-(κ * x))

/-- The bound for marked multigraphs implies the estimate for physical graphs. -/
theorem polynomialForestEstimate_of_marked_bound (h : PolynomialMarkedBound) :
    PolynomialForestEstimate := by
  obtain ⟨κ, hκ, hforest⟩ := h
  have ht : Tendsto (fun r : ℕ => Real.logb 2 (r : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨rmin, hrmin⟩ := (eventually_atTop.mp (ht.eventually hforest))
  refine ⟨κ, hκ, max rmin 1, ?_⟩
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
  have hexp : (2 : ℝ) ^ (-(κ * x)) = (G.cycleRank : ℝ) ^ (-κ) := by
    rw [show -(κ * x) = x * (-κ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hpow]
  have hbound' : Γ.regionForestProbability Pᶜ ≤
      (1 / 2 : ℝ) + (G.cycleRank : ℝ) ^ (-κ) := by
    rw [← hexp]
    exact hbound
  exact hprob.trans hbound'

end Erdos1016.PolynomialBound

import Erdos1016.Cycles.Selection.ConditionalPenaltyBounds

set_option autoImplicit false

/-!
# Section 7 conditional-load decay on the logarithmic scale

This module isolates the final analytic implication in the paper's estimate
for `d_*`: once the chosen parameters have their displayed first-order
asymptotics, the conditional-load error decays exponentially in `x=log₂ n`.
The floor/ceiling estimates establishing those parameter asymptotics remain
separate inputs.
-/

noncomputable section
open Filter
open scoped Topology

namespace Erdos1016.Proof.ConditionalLoadDecay

/-- The logarithm of the paper's `d_*` majorant after applying
`K ceil((s-1)/Δ) ≤ K + (s-1)/(2r-1)`. -/
def loadLogScale (q s K r L : ℕ) : ℝ :=
  Real.log 18 +
    (((q : ℝ) - (s : ℝ) + (K : ℝ) +
      ((s - 1 : ℕ) : ℝ) / (2 * r - 1 : ℕ)) * Real.log 2) +
    2 * Real.log (L : ℝ)

/-- Logarithmic representation of the paper's exact conditional-load
expression, before simplifying its ceiling penalty. -/
def exactDstarLogScale (q s K r Δ L : ℕ) : ℝ :=
  Real.log 18 +
    (((q : ℝ) - (s : ℝ) +
      (K * Nat.ceil (((s - 1 : ℕ) : ℝ) / (Δ : ℝ)) : ℕ)) * Real.log 2) +
    2 * Real.log (L : ℝ)

theorem exactDstarLogScale_le_loadLogScale
    (q s K r Δ L : ℕ) (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hΔ : K * (2 * r - 1) ≤ Δ) :
    exactDstarLogScale q s K r Δ L ≤ loadLogScale q s K r L := by
  unfold exactDstarLogScale loadLogScale
  have hpen :=
    _root_.Erdos1016.Proof.ConditionalPenaltyBounds.conditional_port_exponent_le
      K r s Δ hK hr hΔ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hpen hlog2.le
  linarith

/-- Given the parameter limits used in the paper, the normalized logarithm
of the simplified `d_*` bound tends to `(Q-S) log 2`. `P` is the normalized
degree-two conditioning penalty. -/
theorem normalized_loadLogScale_tendsto
    (x : ℕ → ℝ) (q s K r L : ℕ → ℕ)
    (Q S : ℝ)
    (hx : Tendsto x atTop atTop)
    (hq : Tendsto (fun j => (q j : ℝ) / x j) atTop (𝓝 Q))
    (hs : Tendsto (fun j => (s j : ℝ) / x j) atTop (𝓝 S))
    (hK : Tendsto (fun j => (K j : ℝ) / x j) atTop (𝓝 0))
    (hP : Tendsto (fun j => ((s j - 1 : ℕ) : ℝ) /
      (2 * r j - 1 : ℕ) / x j) atTop (𝓝 0))
    (hL : Tendsto (fun j => Real.log (L j : ℝ) / x j) atTop (𝓝 0)) :
    Tendsto (fun j => loadLogScale (q j) (s j) (K j) (r j) (L j) / x j)
      atTop (𝓝 ((Q - S) * Real.log 2)) := by
  have hconstant : Tendsto (fun j => Real.log 18 / x j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  have hmain : Tendsto
      (fun j => ((q j : ℝ) / x j - (s j : ℝ) / x j +
        (K j : ℝ) / x j +
        ((s j - 1 : ℕ) : ℝ) / (2 * r j - 1 : ℕ) / x j) * Real.log 2)
      atTop (𝓝 ((Q - S) * Real.log 2)) := by
    have hsum := (((hq.sub hs).add hK).add hP).const_mul (Real.log 2)
    convert hsum using 1
    · ext j
      ring
    · ring
  have hlast : Tendsto (fun j => 2 * (Real.log (L j : ℝ) / x j))
      atTop (𝓝 0) := by simpa using hL.const_mul (2 : ℝ)
  have htotal := (hconstant.add hmain).add hlast
  have heq : (fun j => loadLogScale (q j) (s j) (K j) (r j) (L j) / x j) =
      fun j => Real.log 18 / x j +
        ((q j : ℝ) / x j - (s j : ℝ) / x j +
          (K j : ℝ) / x j +
          ((s j - 1 : ℕ) : ℝ) / (2 * r j - 1 : ℕ) / x j) * Real.log 2 +
        2 * (Real.log (L j : ℝ) / x j) := by
    funext j
    unfold loadLogScale
    ring_nf
  rw [heq]
  simpa using htotal







end Erdos1016.Proof.ConditionalLoadDecay

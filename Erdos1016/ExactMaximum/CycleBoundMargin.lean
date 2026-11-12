import Erdos1016.Main
import Erdos1016.ExactMaximum.NetSubdivide
import Erdos1016.ExactMaximum.NetRealization

set_option autoImplicit false

/-!
# The cycle bound for networks, with a margin

Corollary 3.11 of the paper "The maximum number of cycles in a graph of large rank" says that a
graph of large rank `r` has at most `(1/2 + o(1)) 2^r` cycles. `PoleCycleBound.lean` moves the
bound `(9/16) 2^r` to networks. The proof of Theorem 7.1 needs the bound with a small margin. This
file proves it in the same way: for every `m`, a network of large rank `b` has at most
`(1/2 + 2^(-m-1)) 2^b` cycles (`numCycles_le_of_large_rank_margin`).
-/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance cycleBoundMarginDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **A network of large rank `b` has at most `(1/2 + 2^(-m-1)) 2^b` cycles.** -/
theorem numCycles_le_of_large_rank_margin (m : ℕ) :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B ≤ networkRank N →
      2 ^ (m + 1) * N.numCycles ≤ (2 ^ m + 1) * 2 ^ networkRank N := by
  obtain ⟨r₁, h₁⟩ := Erdos1016.cycleCountTheorem
  -- the triple logarithm is large
  have htl : Tendsto
      (fun r : ℕ => Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp
      ((Real.tendsto_logb_atTop one_lt_two).comp
        ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop))
  obtain ⟨r₂, h₂⟩ := Filter.eventually_atTop.1 (htl.eventually_ge_atTop (21 * 2 ^ (m + 1)))
  refine ⟨max r₁ r₂, ?_⟩
  intro V E _ _ N hB
  -- the simple graph of the subdivision
  obtain ⟨n, G, hG, hc⟩ := N.subdivide.exists_simpleGraph_of_network N.subdivide_simple
  rw [N.networkRank_subdivide] at hG
  rw [N.numCycles_subdivide] at hc
  have hb := h₁ n G (networkRank N) hG (le_trans (le_max_left _ _) hB)
  have hL : (21 * 2 ^ (m + 1) : ℝ) ≤
      Real.logb 2 (Real.logb 2 (Real.logb 2 ((networkRank N : ℕ) : ℝ))) :=
    h₂ (networkRank N) (le_trans (le_max_right _ _) hB)
  -- arithmetic in the real numbers
  have hpos2 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
  have hLpos : (0 : ℝ) < Real.logb 2 (Real.logb 2 (Real.logb 2 ((networkRank N : ℕ) : ℝ))) :=
    lt_of_lt_of_le (by positivity) hL
  have hfrac : (21 : ℝ) / Real.logb 2 (Real.logb 2 (Real.logb 2 ((networkRank N : ℕ) : ℝ))) ≤
      1 / 2 ^ (m + 1) := by
    rw [div_le_div_iff₀ hLpos hpos2]
    linarith
  have hpow : (0 : ℝ) < 2 ^ networkRank N := by positivity
  have hle : ((CycleCount.numCycles G : ℕ) : ℝ) ≤
      (1 / 2 + 1 / 2 ^ (m + 1)) * 2 ^ networkRank N :=
    le_trans hb (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hpow))
  rw [hc] at hle
  have e1 : (2 : ℝ) ^ (m + 1) * ((1 / 2 + 1 / 2 ^ (m + 1)) * 2 ^ networkRank N) =
      (2 ^ m + 1) * 2 ^ networkRank N := by
    rw [pow_succ]
    field_simp
  have hreal : (2 : ℝ) ^ (m + 1) * (N.numCycles : ℝ) ≤ (2 ^ m + 1) * 2 ^ networkRank N := by
    rw [← e1]
    exact mul_le_mul_of_nonneg_left hle hpos2.le
  exact_mod_cast hreal

end Erdos1016.ExactMaximum

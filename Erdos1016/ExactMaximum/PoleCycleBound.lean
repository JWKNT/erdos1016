import Erdos1016.Main
import Erdos1016.ExactMaximum.NetSubdivide
import Erdos1016.ExactMaximum.NetRealization
import Erdos1016.ExactMaximum.TwoCut

set_option autoImplicit false

/-!
# The cycle bound for networks of large rank

Corollary 3.11 of the paper "The maximum number of cycles in a graph of large rank" says that a
graph of large rank `r` has at most `(1/2 + o(1)) 2^r` cycles. The repository proves it for simple
graphs (`Erdos1016.cycleCountTheorem`). This file moves it to networks, which can have parallel
edges: subdivide every edge once (`NetSubdivide.lean`), and take the simple graph of the result
(`NetRealization.lean`). The rank and the number of cycles do not change.

The result is `poleCycleBoundStatement : PoleCycleBoundStatement`: a network of large rank `b`
has at most `(9/16) 2^b` cycles. It does not use the hypothesis that the network is a pole.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleCycleBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **A network of large rank has at most `(9/16) 2^b` cycles.** -/
theorem numCycles_le_of_large_rank :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B ≤ networkRank N →
      16 * N.numCycles ≤ 9 * 2 ^ networkRank N := by
  obtain ⟨r₁, h₁⟩ := Erdos1016.cycleCountTheorem
  -- the triple logarithm is large
  have htl : Tendsto
      (fun r : ℕ => Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp
      ((Real.tendsto_logb_atTop one_lt_two).comp
        ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop))
  obtain ⟨r₂, h₂⟩ := Filter.eventually_atTop.1 (htl.eventually_ge_atTop 336)
  refine ⟨max r₁ r₂, ?_⟩
  intro V E _ _ N hB
  -- the simple graph of the subdivision
  obtain ⟨n, G, hG, hc⟩ := N.subdivide.exists_simpleGraph_of_network N.subdivide_simple
  rw [N.networkRank_subdivide] at hG
  rw [N.numCycles_subdivide] at hc
  have hb := h₁ n G (networkRank N) hG (le_trans (le_max_left _ _) hB)
  have hL : (336 : ℝ) ≤ Real.logb 2 (Real.logb 2 (Real.logb 2 ((networkRank N : ℕ) : ℝ))) :=
    h₂ (networkRank N) (le_trans (le_max_right _ _) hB)
  -- arithmetic in the real numbers
  have hfrac : (21 : ℝ) / Real.logb 2 (Real.logb 2 (Real.logb 2 ((networkRank N : ℕ) : ℝ))) ≤
      1 / 16 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hpow : (0 : ℝ) < 2 ^ networkRank N := by positivity
  have hle : ((CycleCount.numCycles G : ℕ) : ℝ) ≤ (1 / 2 + 1 / 16) * 2 ^ networkRank N :=
    le_trans hb (mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hpow))
  rw [hc] at hle
  have hreal : (16 : ℝ) * (N.numCycles : ℝ) ≤ 9 * 2 ^ networkRank N := by linarith
  exact_mod_cast hreal

/-- **Corollary 3.11 of the paper for poles.** -/
theorem poleCycleBoundStatement : PoleCycleBoundStatement := by
  obtain ⟨B, hB⟩ := numCycles_le_of_large_rank
  exact ⟨B, fun V E _ _ N _ h => hB V E N h⟩

end Erdos1016.ExactMaximum

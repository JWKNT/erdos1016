import Erdos1016.ExactMaximum.RingRank
import Erdos1016.ExactMaximum.NetRealization
import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximumSupport.CubicReduction.Statement

set_option autoImplicit false

/-!
# The lower bound of the exact maximum

For every `r ≥ 3` some simple graph of cyclomatic number `r` has at least `H(r)` cycles
(`lowerBoundStatement`). The graph is the ring of the paper "The maximum number of cycles in a
graph of large rank": for `r = 2k + 4` the network `Ring.ring k`, and for `r = 2k + 3` the same
network without its rung.

With the reduction to cubic multigraphs (`ExactMaximumSupport.CubicReduction`, by Astra), the
exact maximum now follows from the four statements about connected cubic multigraphs without
loops (`exactMaximumStatement_of_four`).
-/

noncomputable section

namespace Erdos1016.ExactMaximum

open CycleCount BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance lowerBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Corollary 6.2 of the paper, the lower bound.** For every `r ≥ 3` there is a simple graph
with cyclomatic number `r` and at least `H(r)` cycles. -/
theorem lowerBoundStatement : LowerBoundStatement := by
  refine ⟨3, fun r hr => ?_⟩
  rcases Nat.even_or_odd r with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- `r = 2k + 4`: the ring with the rung
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hr' : r = 2 * (k + 1) + 2 := by omega
    obtain ⟨n, G, hG, hc⟩ := exists_simpleGraph_of_network (Ring.ring k) Ring.ring_simple
    refine ⟨n, G, ?_, ?_⟩
    · rw [Ring.networkRank_ring] at hG
      rw [← hG]
      omega
    · rw [hc, hr']
      exact Ring.horakKim_le_numCycles_ring k
  · -- `r = 2k + 3`: the ring without the rung
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hr' : r = 2 * (k + 1) + 1 := by omega
    have hsimple : ∀ e f : {e : Ring.Edge k // Ring.noRung e},
        ((Ring.ring k).sub Ring.noRung).Joins e (((Ring.ring k).sub Ring.noRung).src f)
          (((Ring.ring k).sub Ring.noRung).dst f) → e = f :=
      fun e f h => Subtype.ext (Ring.ring_simple e.1 f.1 h)
    obtain ⟨n, G, hG, hc⟩ :=
      exists_simpleGraph_of_network ((Ring.ring k).sub Ring.noRung) hsimple
    refine ⟨n, G, ?_, ?_⟩
    · rw [Ring.networkRank_ring_noRung] at hG
      rw [← hG]
      omega
    · rw [hc, hr', numCycles_sub]
      exact Ring.horakKim_le_numCyclesNoRung k

/-- **Theorem 1.1 from the four statements about cubic multigraphs.** The reduction to cubic
multigraphs and the lower bound are proved. So the exact maximum follows from the statements for
a cyclic cut of size at most three, for a cyclic cut of size four, for a short cycle, and for
large girth. -/
theorem exactMaximumStatement_of_four (h3 : ThreeCutStatement) (h4 : FourCutStatement)
    (hS : ShortCycleStatement) (hL : LargeGirthStatement) : ExactMaximumStatement :=
  exactMaximumStatement_of_parts ExactMaximumSupport.CubicReduction.cubicReductionStatement h3
    h4 hS hL lowerBoundStatement

end Erdos1016.ExactMaximum

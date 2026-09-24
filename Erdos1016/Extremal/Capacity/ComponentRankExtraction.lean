import Erdos1016.Extremal.Capacity.ComponentWitnessCoverage

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016
open Erdos1016.Proof.ActiveOutsideProbabilityBridge
open Erdos1016.Proof.ActiveComponentRankSum
open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.Proof.VertexSupportedWitness



/-- A component screen bounding the number of edge-bearing active components
forces one component to carry at least the average cycle rank. -/
theorem exists_activeComponent_large_rank_of_screen
    (G : PhysicalGraph) (R : ℕ)
    (hcount : (nonemptyActiveComponents G).card < 5 * R)
    (hrank : 0 < G.cycleRank) :
    ∃ c ∈ nonemptyActiveComponents G,
      G.cycleRank ≤ (5 * R) *
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
  classical
  have hnonempty : (nonemptyActiveComponents G).Nonempty := by
    by_contra h
    have hempty : nonemptyActiveComponents G = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    have hsum := cycleRank_eq_sum_nonemptyActiveComponentRanks G
    rw [hempty] at hsum
    simp at hsum
    omega
  have hcount' : (nonemptyActiveComponents G).card ≤ 5 * R := Nat.le_of_lt hcount
  have htotal : G.cycleRank ≤
      ∑ c ∈ nonemptyActiveComponents G,
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
    rw [cycleRank_eq_sum_nonemptyActiveComponentRanks]
  exact ActiveComponentRankSum.exists_mem_large_rank
    (nonemptyActiveComponents G) hnonempty
    (fun c => ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank)
    (5 * R) G.cycleRank hcount' htotal




end Erdos1016.Proof.ActivePhysicalComponents
end

import Erdos1016.Cycles.Filtering.InducedReturnFilter
import Erdos1016.Cycles.Counting.LengthPartition

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Erdos1016.Proof.InducedRetainedTraceSupply
open scoped BigOperators
open BoundaryDecay Nonbacktracking InducedRetainedCycleFilter
open RejectedCycleEncoding ReturnMassLoss
open LengthPartition

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Rejecting chords and all other short external returns retains the same
two relative survival factors in the trace-to-cycle estimate. -/
theorem induced_retained_weight_ge_trace_product
    (G : PhysicalGraph) (L s D q : ℕ) (V : Finset G.Vertex)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) (hq : 1 ≤ q) (hqL : q ≤ L)
    (hbudget : (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s ≤ 1) :
    (1 - (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) *
      ((1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) *
        nonbacktrackingTraceMass (G := G) L) ≤
      cycleWeightSum (inducedAcceptedCycles G V (shortCycleWords G L) q) := by
  have hphysical := shortCycleMass_ge_trace_after_collision G L s D hmin hmax hg hshort hs
  have hloss := rejected_induced_mass_le_suffix_budget G D s q L V hmin hmax hg hs hshort hq hqL
  have hsub : inducedAcceptedCycles G V (shortCycleWords G L) q ⊆ shortCycleWords G L := by
    intro C hC
    exact (mem_inducedAcceptedCycles G V (shortCycleWords G L) q C).mp hC |>.1
  have hpartition := Finset.sum_sdiff hsub (f := cycleWordMass G)
  have hsum : (∑ C ∈ inducedAcceptedCycles G V (shortCycleWords G L) q, cycleWordMass G C) =
      cycleWeightSum (inducedAcceptedCycles G V (shortCycleWords G L) q) := by
    unfold cycleWeightSum cycleWordMass cycleWeight
    apply Finset.sum_congr rfl
    intro C hC
    rw [one_div_pow]
  rw [hsum] at hpartition
  have hfactor : 0 ≤ 1 - (9 / 2 : ℝ) * (2 : ℝ) ^ q * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s := by linarith
  have hmul := mul_le_mul_of_nonneg_left hphysical hfactor
  change _ = shortCycleMass G L at hpartition
  nlinarith

end Erdos1016.Proof.InducedRetainedTraceSupply

import Erdos1016.Probability.Cylinders.CutParity
import Erdos1016.Probability.Conditional.RegionRevealLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Probability bounds for disjoint regions with two-edge cuts

For a physical region with at most two outgoing edges, cycle-space parity
makes the zero-cut event have probability at least one half. This directly
gives the ordinary pair-cylinder bound with no exceptional pairs. The
remaining inputs to the many-region estimate are the geometric region family
and the conditional local-product bound.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.PhysicalTwoCutRegionBridge

open Erdos1016
open Erdos1016.Proof.ActualCutCycleCylinder
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge
open Erdos1016.Proof.PhysicalManyRegionReveal

local notation "𝔽" => ZMod 2

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → Finset G.Vertex)

/-- The project's normalized outside-forest probability is the uniform
event probability on its cycle space. -/
theorem outsideLinearForestProbability_eq_eventProbability
    (E : Finset G.Edge) :
    G.outsideLinearForestProbability E = eventProbability
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E) := by
  classical
  letI : Nonempty G.CycleSpace := ⟨0⟩
  have hspaceNat : Fintype.card G.CycleSpace = 2 ^ G.cycleRank := by
    rw [← Nat.card_eq_fintype_card]
    simpa [PhysicalGraph.cycleRank] using
      (Module.natCard_eq_pow_finrank (K := 𝔽) (V := G.CycleSpace))
  have hspace : (Fintype.card G.CycleSpace : ℝ) =
      (2 : ℝ) ^ G.cycleRank := by exact_mod_cast hspaceNat
  unfold PhysicalGraph.outsideLinearForestProbability
    eventProbability Erdos1016.Proof.FinitePaleyZygmund.probability
  rw [hspace]
  simp [PhysicalGraph.outsideLinearForestStates]















end Erdos1016.Proof.PhysicalTwoCutRegionBridge

end

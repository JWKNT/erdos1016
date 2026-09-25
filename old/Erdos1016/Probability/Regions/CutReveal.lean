import Erdos1016.Probability.Cylinders.CutPairProbabilities
import Erdos1016.Probability.Conditional.RegionRevealLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Actual cut-coordinate events under a physical reveal

The Section 10 cylinders constrain every coordinate on an actual host cut.
Those coordinates are visible in the outside reveal.  This module connects
those events to the already formalized conditional product argument, which
uses the weaker zero boundary-demand condition on the fixed reveal target.
-/

noncomputable section

namespace Erdos1016.Proof.PhysicalActualCutRevealBridge

open Erdos1016
open Erdos1016.Proof.ActualCutCycleCylinder
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.PhysicalManyRegionReveal
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge
open Erdos1016.Proof.RevealedFiberProbability


local notation "𝔽" => ZMod 2

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → Finset G.Vertex)

private theorem cutEdge_not_in_allRegionEdges
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) {e : G.Edge} (he : e ∈ G.cutEdges (S i)) :
    e ∉ allRegionEdges G S := by
  intro hall
  obtain ⟨j, _, hregion⟩ := Finset.mem_biUnion.mp hall
  have hsrcj : G.src e ∈ S j := (Finset.mem_filter.mp hregion).2.1
  have hdstj : G.dst e ∈ S j := (Finset.mem_filter.mp hregion).2.2
  rcases (Finset.mem_filter.mp he).2 with ⟨hsrci, hdstOut⟩ | ⟨hsrcOut, hdsti⟩
  · by_cases hij : i = j
    · subst j
      exact hdstOut hdstj
    · exact (Finset.disjoint_left.mp (hdisj i j hij)) hsrci hsrcj
  · by_cases hij : i = j
    · subst j
      exact hsrcOut hsrcj
    · exact (Finset.disjoint_left.mp (hdisj i j hij)) hdsti hdstj

/-- The actual cut edges of one region, viewed as coordinates in the outside
edge type used by the reveal. -/
def outsideCutEdge
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (e : {e : G.Edge // e ∈ G.cutEdges (S i)}) : OutsideEdge G S :=
  ⟨e.1, cutEdge_not_in_allRegionEdges G S hdisj i e.2⟩

/-- The event on a revealed target that every actual cut coordinate is zero. -/
def actualCutZeroRevealEvent
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (y : RevealTarget G S hdisj) : Prop :=
  ∀ e : {e : G.Edge // e ∈ G.cutEdges (S i)},
    y.1 (outsideCutEdge G S hdisj i e) = 0

/-- Actual cut coordinates are exactly the cut coordinates read from the
outside reveal. -/
theorem actualCutZero_iff_revealed
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (x : G.CycleSpace) :
    cutCoordinatesZero G (S i) x ↔
      actualCutZeroRevealEvent G S hdisj i (reveal G S hdisj x) := by
  constructor
  · intro h e
    change revealValue G S hdisj x
      (outsideCutEdge G S hdisj i e) = 0
    rw [revealValue_eq_outsideRevealLinear G S hdisj x]
    exact h e.1 e.2
  · intro h e he
    have hz := h ⟨e, he⟩
    change revealValue G S hdisj x
      (outsideCutEdge G S hdisj i ⟨e, he⟩) = 0 at hz
    rw [revealValue_eq_outsideRevealLinear G S hdisj x] at hz
    exact hz

/-- If a revealed target has zero actual cut coordinates, its regional
boundary demand also vanishes. -/
theorem actualCutZeroRevealEvent_implies_zeroCutRevealEvent
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (y : RevealTarget G S hdisj)
    (hzero : actualCutZeroRevealEvent G S hdisj i y) :
    zeroCutRevealEvent G S hdisj i y := by
  obtain ⟨x, hx⟩ := y.2
  have hEq : reveal G S hdisj x = y := by
    apply Subtype.ext
    exact hx
  have hbar : actualCutZeroRevealEvent G S hdisj i
      (reveal G S hdisj x) := by
    simpa [hEq] using hzero
  have hcoords : cutCoordinatesZero G (S i) x :=
    (actualCutZero_iff_revealed G S hdisj i x).2 hbar
  have hzeroCut : zeroCutEvent G S hdisj i x :=
    cutCoordinates_zero_implies_zeroCutEvent G S hdisj i x
      (fun e he => hcoords e he)
  have hrevealed := (zeroCutEvent_iff_revealed G S hdisj i x).1 hzeroCut
  simpa [hEq] using hrevealed





end Erdos1016.Proof.PhysicalActualCutRevealBridge

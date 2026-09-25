import Erdos1016.Probability.Regions.CutReveal
import Erdos1016.Probability.Regions.ForestThreshold

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# General-cut actual-event Section 10 bridge

This packages the actual cut-coordinate cylinders, the physical reveal, and
the arbitrary exceptional-partner second-moment threshold. The graph-specific
ordinary-pair input is precisely the rank-one overlap of the two actual-cut
constraint spaces.
-/

noncomputable section

namespace Erdos1016.Proof.PhysicalActualCutGeneralPartnerBridge

open Erdos1016
open Erdos1016.Proof.ActualCutCycleCylinder
open Erdos1016.Proof.ActualCutPairProbability
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.ManyCyclicRegionCutCylinders
open Erdos1016.Proof.PhysicalManyRegionReveal
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge
open Erdos1016.Proof.PhysicalActualCutRevealBridge
open Erdos1016.Proof.RevealedFiberProbability
open Erdos1016.Proof.ManyCyclicRegionsGeneralPartnerThreshold

local notation "𝔽" => ZMod 2

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → Finset G.Vertex)

private theorem actualCut_probability_ge
    (i : ι) (d : ℕ) (hcut : G.actualCut (S i) ≤ d) :
    (1 / 2 : ℝ) ^ d ≤ eventProbability (cutCoordinatesZero G (S i)) := by
  rw [cutCoordinatesZero_probability G (S i)]
  have hrank : Module.finrank 𝔽 (cutConstraintSpace G (S i)) ≤ d := by
    unfold cutConstraintSpace
    have hspan : Module.finrank 𝔽
        (outgoingCutConstraintSpace G (G.cutEdges (S i))) ≤
          ((G.cutEdges (S i)).image
            (Erdos1016.Proof.GraphicalCommonInformation.edgeCoordinate G)).card := by
      unfold outgoingCutConstraintSpace
      exact constraintSpan_finrank_le_card _
    calc
      Module.finrank 𝔽 (outgoingCutConstraintSpace G (G.cutEdges (S i))) ≤
          (G.cutEdges (S i)).card := hspan.trans Finset.card_image_le
      _ ≤ d := by simpa [PhysicalGraph.actualCut] using hcut
  have hpow : (2 : ℝ) ^ Module.finrank 𝔽 (cutConstraintSpace G (S i)) ≤
      (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hrank
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by norm_num) hpow

/-- General-`d` physical bridge. Every event is zero on the actual physical
cut coordinates. The first/second moments, reveal conditioning, and
near-half cutoff are all derived from the listed hypotheses. -/
theorem physical_many_actualCut_regions_forest_lt_cutoff
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (Eedges : Finset G.Edge)
    (hregionsOutside : ∀ i,
      PhysicalManyRegionConditionalProduct.regionInternalEdges G S i ⊆ Eedgesᶜ)
    (hcyclic : ∀ i, G.IsCyclicRegion (S i))
    (exceptional : ι → ι → Prop) [DecidableRel exceptional]
    (R a K d : ℕ) (hR : 5 ≤ R) (ha_pos : 1 ≤ a)
    (hcut : ∀ i, G.actualCut (S i) ≤ d)
    (hrank : ∀ i j, i ≠ j → ¬ exceptional i j →
      Module.finrank 𝔽
        ↥(cutConstraintSpace G (S i) ⊓ cutConstraintSpace G (S j)) ≤ 1)
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ K)
    (hcount : 8 * R * 2 ^ d * (K + a) ≤ Fintype.card ι)
    (hpow : (1 / 2 : ℝ) ^ a ≤ 1 / (4 * (R : ℝ))) :
    eventProbability
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates Eedges) <
      (1 / 2 : ℝ) + 1 / (R : ℝ) := by
  classical
  letI : Nonempty G.CycleSpace := ⟨0⟩
  let Eevent : ι → G.CycleSpace → Prop := fun i x =>
    cutCoordinatesZero G (S i) x
  let Ebar : ι → RevealTarget G S hdisj → Prop :=
    actualCutZeroRevealEvent G S hdisj
  have hE : ∀ i x, Eevent i x ↔ Ebar i (reveal G S hdisj x) := by
    intro i x
    exact actualCutZero_iff_revealed G S hdisj i x
  have hmarginal : ∀ i,
      (1 / 2 : ℝ) ^ d ≤ eventProbability (Eevent i) := by
    intro i
    exact actualCut_probability_ge G S i d (hcut i)
  have hdiag : ∀ i,
      eventProbability (fun x : G.CycleSpace => Eevent i x ∧ Eevent i x) ≤
        eventProbability (Eevent i) := by
    intro i
    exact Erdos1016.Proof.BadVertexCylinderCount.eventProbability_mono
      (fun x => Eevent i x ∧ Eevent i x) (Eevent i) (fun _ h => h.1)
  have hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x : G.CycleSpace => Eevent i x ∧ Eevent j x) ≤
        2 * eventProbability (Eevent i) * eventProbability (Eevent j) := by
    intro i j hij hex
    simpa [Eevent] using
      (cutCoordinatesZero_pair_le_twice_product G (S i) (S j)
        (hrank i j hij hex))
  have hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x : G.CycleSpace => Eevent i x ∧ Eevent j x) ≤
        eventProbability (Eevent i) := by
    intro i j _
    exact Erdos1016.Proof.BadVertexCylinderCount.eventProbability_mono
      (fun x => Eevent i x ∧ Eevent j x) (Eevent i) (fun _ h => h.1)
  have hmean : (∑ i, eventProbability (Eevent i)) ≥
      8 * (R : ℝ) * ((K : ℝ) + (a : ℝ)) := by
    have hsum : ((Fintype.card ι : ℝ) * (1 / 2 : ℝ) ^ d) ≤
        ∑ i, eventProbability (Eevent i) := by
      calc
        ((Fintype.card ι : ℝ) * (1 / 2 : ℝ) ^ d) =
            ∑ _i : ι, (1 / 2 : ℝ) ^ d := by simp [Finset.mul_sum]
        _ ≤ ∑ i, eventProbability (Eevent i) := by
          apply Finset.sum_le_sum
          intro i _
          exact hmarginal i
    have hcountReal :
        8 * (R : ℝ) * (2 : ℝ) ^ d * ((K : ℝ) + (a : ℝ)) ≤
          (Fintype.card ι : ℝ) := by
      exact_mod_cast hcount
    have htwoPos : 0 < (2 : ℝ) ^ d := by positivity
    have hpowInv : (1 / 2 : ℝ) ^ d = 1 / (2 : ℝ) ^ d := one_div_pow _ _
    rw [hpowInv] at hsum
    have hmul := mul_le_mul_of_nonneg_right hcountReal (by positivity :
      0 ≤ 1 / (2 : ℝ) ^ d)
    have hcancel :
        (8 * (R : ℝ) * (2 : ℝ) ^ d * ((K : ℝ) + (a : ℝ))) *
          (1 / (2 : ℝ) ^ d) =
        8 * (R : ℝ) * ((K : ℝ) + (a : ℝ)) := by
      field_simp
      <;> ring
    rw [hcancel] at hmul
    exact le_trans hmul hsum
  have hconditional : ∀ y : RevealTarget G S hdisj,
      a ≤ eventCountNat Ebar y →
        Finite.density (fun x : fiber (reveal G S hdisj) y =>
          x.1 ∈ G.outsideLinearForestStates Eedges) ≤ (1 / 2 : ℝ) ^ a := by
    intro y hy
    have hcountBoundary : a ≤ eventCountNat
        (zeroCutRevealEvent G S hdisj) y := by
      have hsubset : eventCountNat Ebar y ≤
          eventCountNat (zeroCutRevealEvent G S hdisj) y := by
        unfold eventCountNat
        apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hi).1,
            actualCutZeroRevealEvent_implies_zeroCutRevealEvent
              G S hdisj i y (Finset.mem_filter.mp hi).2⟩
      exact le_trans hy hsubset
    exact outsideForest_conditional_bound G S hdisj Eedges
      hregionsOutside hcyclic a y hcountBoundary
  have hproduct :=
    eventProbability_le_complement_eventCount_add
      (reveal G S hdisj) (reveal_surjective G S hdisj)
      (Fintype.card (LinearMap.ker (outsideRevealLinear G S hdisj)))
      (reveal_fiber_card G S hdisj) Eevent Ebar hE
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates Eedges)
      a hconditional
  have hbound := ManyCyclicRegionsGeneralPartnerThreshold.forest_probability_le_half_add
      Eevent exceptional (fun x : G.CycleSpace =>
        x ∈ G.outsideLinearForestStates Eedges) R a K hR ha_pos
      (by simpa [Eevent] using hdiag)
      (by simpa [Eevent] using hordinary)
      (by simpa [Eevent] using hexceptional) hpartners
      (by simpa [Eevent] using hmean) hpow hproduct
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hgap : 1 / (2 * (R : ℝ)) < 1 / (R : ℝ) := by
    have hx := div_lt_div_of_pos_right (by norm_num : (1 / 2 : ℝ) < 1) hRpos
    have hre : 1 / (2 * (R : ℝ)) = (1 / 2 : ℝ) / (R : ℝ) := by
      field_simp [ne_of_gt hRpos]
      <;> ring
    rw [hre]
    exact hx
  linarith

end Erdos1016.Proof.PhysicalActualCutGeneralPartnerBridge

end

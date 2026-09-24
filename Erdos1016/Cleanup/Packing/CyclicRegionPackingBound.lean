import Erdos1016.Probability.Regions.GeneralCutForestBound
import Erdos1016.Probability.Cylinders.RegionPartnerCount
import Erdos1016.Probability.Regions.TwoCutForestLaw

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# A high forest probability bounds fixed-cut cyclic-region packings

The Section 10 many-region estimate bounds any supplied family of regions
whose internal edges avoid a fixed tested-edge set. The graph-specific input
is the triple-intersection rank estimate for the physical cut-coordinate
spaces. Constructing the particular region family required by the finite
forest descent remains a separate Section 10 obligation.
-/

noncomputable section

namespace Erdos1016.Proof.CyclicRegionPackingBound

open Erdos1016
open Erdos1016.Proof.ActualCutPairProbability
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.ManyCyclicRegionsExceptionalPartners
open Erdos1016.Proof.ManyCyclicRegionCutCylinders
open Erdos1016.Proof.PartnerCounting
open Erdos1016.Proof.PhysicalActualCutGeneralPartnerBridge
open Erdos1016.Proof.PhysicalManyRegionConditionalProduct
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge
open Erdos1016.Proof.PhysicalTwoCutRegionBridge
open Erdos1016.SafeCore

local notation "𝔽" => ZMod 2

private theorem cutConstraintSpace_finrank_le_actualCut
    (G : PhysicalGraph) (U : Finset G.Vertex) :
    Module.finrank 𝔽 (cutConstraintSpace G U) ≤ G.actualCut U := by
  unfold cutConstraintSpace
  have hspan := constraintSpan_finrank_le_card
    ((G.cutEdges U).image (Erdos1016.Proof.GraphicalCommonInformation.edgeCoordinate G))
  calc
    Module.finrank 𝔽
        (outgoingCutConstraintSpace G (G.cutEdges U)) ≤
        ((G.cutEdges U).image
          (Erdos1016.Proof.GraphicalCommonInformation.edgeCoordinate G)).card := by
          simpa [outgoingCutConstraintSpace, constraintSpan] using hspan
    _ ≤ (G.cutEdges U).card := Finset.card_image_le
    _ = G.actualCut U := by rfl

private def isExceptionalPartner (G : PhysicalGraph) (F : Finset (Finset G.Vertex))
    (i j : {U : Finset G.Vertex // U ∈ F}) : Prop :=
  i ≠ j ∧ 2 ≤ Module.finrank 𝔽
    (PairIntersection (cutConstraintSpace G i.1) (cutConstraintSpace G j.1))

/-- If the outside-forest probability is above the paper's cutoff, there
cannot be as many as the many-region threshold pairwise disjoint connected
cyclic regions of cut size at most `d`, provided distinct triples of their
actual cut spaces have common rank at most one. -/
theorem card_lt_manyRegionThreshold_of_high_probability
    (G : PhysicalGraph) (Eedges : Finset G.Edge) (R d : ℕ)
    (hR : 5 ≤ R)
    (F : Finset (Finset G.Vertex))
    (htriple : ∀ U V W : Finset G.Vertex,
      U ∈ F → V ∈ F → W ∈ F →
      U ≠ V → U ≠ W → V ≠ W →
      Module.finrank 𝔽
        (TripleIntersection (cutConstraintSpace G U)
          (cutConstraintSpace G V) (cutConstraintSpace G W)) ≤ 1)
    (hregionsOutside : ∀ U ∈ F,
      internalEdges G U ⊆ Eedgesᶜ)
    (hregions : ∀ U ∈ F,
      G.IsCyclicRegion U ∧ G.actualCut U ≤ d)
    (hdisj : (F : Set (Finset G.Vertex)).Pairwise Disjoint)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability Eedges) :
    F.card < 8 * R * 2 ^ d * (2 ^ (2 * d) + dyadicRegionCutoffExponent R) := by
  classical
  let ι := {U : Finset G.Vertex // U ∈ F}
  let S : ι → Finset G.Vertex := fun i => i.1
  let exceptional : ι → ι → Prop := isExceptionalPartner G F
  letI : DecidableRel exceptional := Classical.decRel _
  letI : Fintype ι := Fintype.ofFinite ι
  have hFcard : Fintype.card ι = F.card := by
    simp [ι]
  by_contra hnot
  have hcount : 8 * R * 2 ^ d * (2 ^ (2 * d) + dyadicRegionCutoffExponent R) ≤
      Fintype.card ι := by
    rw [hFcard]
    omega
  have hdisj' : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    apply hdisj
    · exact i.2
    · exact j.2
    · intro heq
      apply hij
      exact Subtype.ext heq
  have hcut : ∀ i, G.actualCut (S i) ≤ d := fun i => (hregions i.1 i.2).2
  have hcyclic : ∀ i, G.IsCyclicRegion (S i) := fun i => (hregions i.1 i.2).1
  have houtside : ∀ i,
      regionInternalEdges G S i ⊆ Eedgesᶜ := by
    intro i
    have h := hregionsOutside i.1 i.2
    simpa [regionInternalEdges, S, Erdos1016.Proof.PhysicalManyRegionReveal.regionEdges,
      internalEdges] using h
  have hdim : ∀ i, Module.finrank 𝔽 (cutConstraintSpace G (S i)) ≤ d := by
    intro i
    exact (cutConstraintSpace_finrank_le_actualCut G (S i)).trans (hcut i)
  have hpair : ∀ i j, exceptional i j →
      2 ≤ Module.finrank 𝔽
        (PairIntersection (cutConstraintSpace G (S i)) (cutConstraintSpace G (S j))) := by
    intro i j hexc
    exact hexc.2
  have htriple' : ∀ i j k, exceptional i j → exceptional i k → j ≠ k →
      Module.finrank 𝔽
        (TripleIntersection (cutConstraintSpace G (S i))
          (cutConstraintSpace G (S j)) (cutConstraintSpace G (S k))) ≤ 1 := by
    intro i j k hij hik hjk
    apply htriple (S i) (S j) (S k) i.2 j.2 k.2
    · intro heq
      exact hij.1 (Subtype.ext heq)
    · intro heq
      exact hik.1 (Subtype.ext heq)
    · intro heq
      exact hjk (Subtype.ext heq)
  have hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤
        (2 ^ (2 * d) : ℕ) := by
    intro i
    let T : ι → Submodule 𝔽 (Module.Dual 𝔽 G.CycleSpace) :=
      fun j => cutConstraintSpace G (S j)
    have hcountSub := exceptional_card_le_two_pow_two_mul_of_dim
      (cutConstraintSpace G (S i)) T (exceptional i) d (hdim i)
      (by intro j hj; exact hpair i j hj)
      (by
        intro j k hj hk hjk
        exact htriple' i j k hj hk hjk)
    have hfilter :
        (Finset.univ.filter (fun j => exceptional i j)).card =
          Fintype.card {j : ι // exceptional i j} := by
      rw [Fintype.card_subtype]
    rw [hfilter]
    exact_mod_cast hcountSub
  have hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      Module.finrank 𝔽
        ↥(cutConstraintSpace G (S i) ⊓ cutConstraintSpace G (S j)) ≤ 1 := by
    intro i j hij hex
    have hlt : Module.finrank 𝔽
        (PairIntersection (cutConstraintSpace G (S i))
          (cutConstraintSpace G (S j))) < 2 := by
      by_contra hn
      exact hex ⟨hij, Nat.le_of_not_gt hn⟩
    simpa [PairIntersection] using (show
      Module.finrank 𝔽
        (PairIntersection (cutConstraintSpace G (S i))
          (cutConstraintSpace G (S j))) ≤ 1 by omega)
  have houtsideProb : eventProbability
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates Eedges) ≤
        (1 / 2 : ℝ) + 1 / (R : ℝ) := by
    exact le_of_lt (physical_many_actualCut_regions_forest_lt_cutoff
      G S hdisj' Eedges houtside hcyclic exceptional R
      (dyadicRegionCutoffExponent R) (2 ^ (2 * d)) d hR
      (by
        have hpos : 0 < dyadicRegionCutoffExponent R := by
          by_contra hzero
          have hz : dyadicRegionCutoffExponent R = 0 :=
            Nat.eq_zero_of_not_pos hzero
          have hpow := dyadicRegionCutoffExponent_pow_ge R
          rw [hz] at hpow
          norm_num at hpow
          omega
        omega)
      hcut hordinary hpartners hcount
      (dyadicRegionCutoffExponent_tail_bound R hR))
  have hprob' : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      eventProbability
        (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates Eedges) := by
    rw [← outsideLinearForestProbability_eq_eventProbability]
    exact hprob
  linarith

end Erdos1016.Proof.CyclicRegionPackingBound

end

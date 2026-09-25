import Erdos1016.CycleSpace.Graphical.ThreeRegionQuotient
import Erdos1016.Cleanup.Packing.CyclicRegionPackingBound

set_option autoImplicit false

/-!
# Adapter from quotient cut-star bounds to the packing interface

The quotient package records triple intersections as explicit set-theoretic
subspace intersections.  The many-region packing theorem uses Mathlib's
submodule lattice intersections.  They have the same carriers; this module
keeps that final interface conversion separate from the quotient construction.
-/

noncomputable section

namespace Erdos1016.Proof.PhysicalActualCutTriplePackingAdapter

open Erdos1016
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalActualCutMultigraphBridge
open Erdos1016.Proof.PhysicalActualCutTripleQuotientPackage
open Erdos1016.Proof.ThreeRegionCrossingQuotientGeometry
open Erdos1016.Proof.PartnerCounting
open Erdos1016.Proof.ActualCutPairProbability
open Erdos1016.Proof.PhysicalActualCutGeneralPartnerBridge
open Erdos1016.Proof.PhysicalManyRegionConditionalProduct
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.CyclicRegionPackingBound
open Erdos1016.SafeCore

local notation "𝔽" => ZMod 2

private theorem subspaceInter_eq_inf
    {W : Type*} [AddCommGroup W] [Module 𝔽 W]
    (A B : Submodule 𝔽 W) : subspaceInter A B = A ⊓ B := by
  ext x
  simp [subspaceInter]





/-- In a connected host, the concrete three-region/singleton-outside
quotient supplies the triple-rank hypothesis required by the many-region
packing estimate. Thus callers need only give pairwise disjoint connected
cyclic regions; they no longer need to construct abstract quotient data. -/
theorem card_lt_manyRegionThreshold_of_connectedRegions
    (G : PhysicalGraph) (Eedges : Finset G.Edge) (R d : ℕ)
    (hR : 5 ≤ R) (F : Finset (Finset G.Vertex))
    (hG : G.IsConnected)
    (hregionsOutside : ∀ U ∈ F,
      internalEdges G U ⊆ Eedgesᶜ)
    (hregions : ∀ U ∈ F,
      G.IsCyclicRegion U ∧ G.actualCut U ≤ d)
    (hdisj : (F : Set (Finset G.Vertex)).Pairwise Disjoint)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability Eedges) :
    F.card < 8 * R * 2 ^ d * (2 ^ (2 * d) + dyadicRegionCutoffExponent R) := by
  classical
  apply card_lt_manyRegionThreshold_of_high_probability G Eedges R d hR F
    (htriple := ?_) hregionsOutside hregions hdisj hprob
  intro U V W hU hV hW hUV hUW hVW
  have hUc := (hregions U hU).1
  have hVc := (hregions V hV).1
  have hWc := (hregions W hW).1
  have hUVd : Disjoint U V := hdisj hU hV hUV
  have hUWd : Disjoint U W := hdisj hU hW hUW
  have hVWd : Disjoint V W := hdisj hV hW hVW
  have hneU : U.Nonempty := by
    obtain ⟨x⟩ := hUc.1.nonempty
    exact ⟨x.1, by simpa using x.2⟩
  have hneV : V.Nonempty := by
    obtain ⟨x⟩ := hVc.1.nonempty
    exact ⟨x.1, by simpa using x.2⟩
  have hneW : W.Nonempty := by
    obtain ⟨x⟩ := hWc.1.nonempty
    exact ⟨x.1, by simpa using x.2⟩
  have hG' : G.toSimpleGraph.Connected := hG
  obtain ⟨_, hrank⟩ := threeRegionQuotientData_and_rank_bound
    G U V W hUVd hUWd hVWd hneU hneV hneW hUc.1 hVc.1 hWc.1 hG'
  have hEq : subspaceInter (subspaceInter (cutConstraintSpace G U)
      (cutConstraintSpace G V)) (cutConstraintSpace G W) =
      TripleIntersection (cutConstraintSpace G U)
        (cutConstraintSpace G V) (cutConstraintSpace G W) := by
    simp [TripleIntersection, PairIntersection, subspaceInter_eq_inf]
  rw [← hEq]
  exact hrank

end Erdos1016.Proof.PhysicalActualCutTriplePackingAdapter

end

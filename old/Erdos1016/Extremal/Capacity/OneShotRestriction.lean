import Erdos1016.Extremal.Capacity.CycleLengthComposition
import Erdos1016.Extremal.Capacity.PureCycleBound
import Erdos1016.Extremal.Capacity.LocalCapacityBound
import Erdos1016.Extremal.Capacity.WitnessAlpha
import Erdos1016.Extremal.Capacity.CycleWitnessSelection

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.PhysicalGraph

open Erdos1016.Proof.Capacity

/-! A one-sided cycle-length restriction estimate, grouped by the outside
cycle-space projection. -/

private def oneShotOutsideImage (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset (G.OutsideWord E) :=
  Erdos1016.Proof.CapacityBridge.outsideParityImage G E 0

private def oneShotNonzeroOutsideImage (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset (G.OutsideWord E) := by
  classical
  exact (G.oneShotOutsideImage E).filter fun q => q ≠ 0

private theorem zero_mem_oneShotOutsideImage (G : PhysicalGraph) (E : Finset G.Edge) :
    (0 : G.OutsideWord E) ∈ G.oneShotOutsideImage E := by
  classical
  unfold oneShotOutsideImage Erdos1016.Proof.CapacityBridge.outsideParityImage
  apply Finset.mem_image.mpr
  refine ⟨⟨0, ?_⟩, Finset.mem_univ _, ?_⟩
  · change G.boundary (0 : G.Word) = 0
    simp
  · funext e
    rfl

private theorem nonzeroOutside_card_le (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.oneShotNonzeroOutsideImage E).card ≤
      2 ^ (G.cycleRank - G.restrictedCycleRank E) - 1 := by
  classical
  let Q := G.oneShotOutsideImage E
  have hz : (0 : G.OutsideWord E) ∈ Q := G.zero_mem_oneShotOutsideImage E
  have hfilter : G.oneShotNonzeroOutsideImage E = Q.erase 0 := by
    ext q
    simp [oneShotNonzeroOutsideImage, Q, Finset.mem_erase, and_comm]
  rw [hfilter, Finset.card_erase_of_mem hz]
  have hq := Erdos1016.Proof.CapacityBridge.outsideParityImage_card_le
    G E 0 ⟨0, by change G.boundary (0 : G.Word) = 0; simp⟩
  change Q.card ≤ 2 ^ (G.cycleRank - G.restrictedCycleRank E) at hq
  omega

private theorem cycle_length_mem_oneShot_sets (G : PhysicalGraph)
    (E : Finset G.Edge) {C : G.CycleWord} :
    G.wordLength C.1 ∈ G.pureCycleLengths E ∪
      (G.oneShotNonzeroOutsideImage E).biUnion (fun q =>
        Erdos1016.Capacity.naturalSumset
          (G.restrictedLinearForestLengths E (G.outsideBoundary E q))
          {G.outsideWordLength E q}) := by
  classical
  by_cases hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0
  · apply Finset.mem_union.mpr
    right
    let q := G.restrictOutsideWord E C.1
    have hq : q ∈ G.oneShotOutsideImage E := by
      unfold oneShotOutsideImage Erdos1016.Proof.CapacityBridge.outsideParityImage
      apply Finset.mem_image.mpr
      refine ⟨⟨C.1, ?_⟩, Finset.mem_univ _, rfl⟩
      exact C.2.2.1
    have hqnz : q ≠ 0 := by
      exact G.restrictCycle_outside_ne_zero C E hout
    have hq' : q ∈ G.oneShotNonzeroOutsideImage E := by
      exact Finset.mem_filter.mpr ⟨hq, hqnz⟩
    have hforest := G.restrictCycle_isLinearForest C E hout
    have hboundary : G.restrictedBoundary E (G.restrictWord E C.1) =
        G.outsideBoundary E q := by
      exact G.restrictCycle_boundary_eq C E
    have hinside : G.restrictedWordLength E (G.restrictWord E C.1) ∈
        G.restrictedLinearForestLengths E (G.outsideBoundary E q) := by
      unfold restrictedLinearForestLengths
      apply Finset.mem_image.mpr
      refine ⟨⟨G.restrictWord E C.1, ?_⟩, Finset.mem_univ _, rfl⟩
      exact ⟨hboundary, hforest⟩
    have hsum : G.wordLength C.1 =
        G.restrictedWordLength E (G.restrictWord E C.1) +
          G.outsideWordLength E q := by
      exact G.wordLength_partition E C.1
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq', ?_⟩
    unfold Erdos1016.Capacity.naturalSumset
    apply Finset.mem_image.mpr
    refine ⟨(G.restrictedWordLength E (G.restrictWord E C.1),
      G.outsideWordLength E q), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hinside, Finset.mem_singleton.mpr rfl⟩
    · exact hsum.symm
  · apply Finset.mem_union.mpr
    left
    have houtzero : ∀ e, e ∉ E → C.1 e = 0 := by
      intro e he
      by_contra hne
      exact hout ⟨e, he, hne⟩
    let C' : G.PureCycleWord E := ⟨C, houtzero⟩
    unfold pureCycleLengths
    exact Finset.mem_image.mpr ⟨C', Finset.mem_univ _, rfl⟩

/-- Distinct host cycle lengths are bounded by the pure restricted lengths
plus one maximum restricted linear-forest multiplicity for every nonzero
outside cycle projection. -/
theorem cycleLengths_card_le_oneShot_pure
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.cycleLengths.card ≤
      (2 ^ (G.cycleRank - G.restrictedCycleRank E) - 1) *
          G.maxRestrictedLinearForestMultiplicity E +
        (G.pureCycleLengths E).card := by
  classical
  let Q := G.oneShotNonzeroOutsideImage E
  let X := Q.biUnion (fun q =>
    Erdos1016.Capacity.naturalSumset
      (G.restrictedLinearForestLengths E (G.outsideBoundary E q))
      {G.outsideWordLength E q})
  have hsub : G.cycleLengths ⊆ G.pureCycleLengths E ∪ X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨C, -, rfl⟩
    simpa [Q, X] using cycle_length_mem_oneShot_sets G E
  have hterm : ∀ q ∈ Q,
      (G.restrictedLinearForestLengths E (G.outsideBoundary E q)).card ≤
        G.maxRestrictedLinearForestMultiplicity E := by
    intro q hq
    unfold maxRestrictedLinearForestMultiplicity
    exact Finset.le_sup (f := G.restrictedLinearForestMultiplicity E)
      (Finset.mem_univ _)
  have hX : X.card ≤ Q.card * G.maxRestrictedLinearForestMultiplicity E := by
    have hunion := Erdos1016.Capacity.card_biUnion_naturalSumsets_le Q
      (fun q => G.restrictedLinearForestLengths E (G.outsideBoundary E q))
      (fun q => {G.outsideWordLength E q})
    calc
      X.card ≤ ∑ q ∈ Q,
          (G.restrictedLinearForestLengths E (G.outsideBoundary E q)).card := by
        dsimp [X]
        simpa using (le_trans hunion (by
          apply Finset.sum_le_sum
          intro q hq
          simp))
      _ ≤ ∑ q ∈ Q, G.maxRestrictedLinearForestMultiplicity E := by
        apply Finset.sum_le_sum
        intro q hq
        exact hterm q hq
      _ = Q.card * G.maxRestrictedLinearForestMultiplicity E := by simp [Q]
  have hQcard : Q.card ≤ 2 ^ (G.cycleRank - G.restrictedCycleRank E) - 1 :=
    nonzeroOutside_card_le G E
  calc
    G.cycleLengths.card ≤ (G.pureCycleLengths E ∪ X).card := Finset.card_le_card hsub
    _ ≤ (G.pureCycleLengths E).card + X.card := Finset.card_union_le _ _
    _ ≤ (G.pureCycleLengths E).card +
        Q.card * G.maxRestrictedLinearForestMultiplicity E := Nat.add_le_add_left hX _
    _ ≤ (G.pureCycleLengths E).card +
        (2 ^ (G.cycleRank - G.restrictedCycleRank E) - 1) *
          G.maxRestrictedLinearForestMultiplicity E :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hQcard) _
    _ = _ := Nat.add_comm _ _

private theorem pureCycleLengths_subset_restrictPhysical
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.pureCycleLengths E ⊆ (G.restrictPhysical E).cycleLengths := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨C, -, rfl⟩
  have hsupport : G.edgeSupport C.1.1 ⊆ E := by
    intro e he
    have hval : C.1.1 e ≠ 0 := (Finset.mem_filter.mp he).2
    by_contra hnot
    exact hval (C.2 e hnot)
  obtain ⟨D, hD⟩ := Erdos1016.Proof.FiniteAlphaBridge.restrictCycleWord_isCycle
    G E C.1 hsupport
  apply Finset.mem_image.mpr
  refine ⟨D, Finset.mem_univ _, ?_⟩
  rw [hD]
  exact Erdos1016.Proof.FiniteAlphaBridge.restrictCycleWord_length G E C.1 hsupport

/-- The restriction bound with the pure term expressed as the cycle spectrum
of the physical edge restriction. -/
theorem cycleLengths_card_le_oneShot_physical
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.cycleLengths.card ≤
      (2 ^ (G.cycleRank - G.restrictedCycleRank E) - 1) *
          G.maxRestrictedLinearForestMultiplicity E +
        (G.restrictPhysical E).cycleLengths.card := by
  have hpure := Finset.card_le_card (pureCycleLengths_subset_restrictPhysical G E)
  exact (G.cycleLengths_card_le_oneShot_pure E).trans
    (Nat.add_le_add_left hpure _)

private theorem cycleLengths_card_le_edgeCount (G : PhysicalGraph) :
    G.cycleLengths.card ≤ G.edgeCount := by
  classical
  have hsubset : G.cycleLengths ⊆ Finset.Icc 1 G.edgeCount := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨C, -, rfl⟩
    have hpos : 0 < G.wordLength C.1 := by
      by_contra hnot
      have hcard : (G.edgeSupport C.1).card = 0 := by
        unfold PhysicalGraph.wordLength at hnot
        omega
      have hzero : G.edgeSupport C.1 = ∅ := Finset.card_eq_zero.mp hcard
      apply C.2.1
      funext e
      by_cases he : C.1 e = 0
      · exact he
      · have hm : e ∈ G.edgeSupport C.1 := by
          simp [PhysicalGraph.edgeSupport, he]
        rw [hzero] at hm
        simp at hm
    exact Finset.mem_Icc.mpr ⟨hpos, G.wordLength_le C.1⟩
  have hcard : (Finset.Icc 1 G.edgeCount).card = G.edgeCount := by
    simp [Nat.card_Icc]
  calc
    G.cycleLengths.card ≤ (Finset.Icc 1 G.edgeCount).card := Finset.card_le_card hsubset
    _ = G.edgeCount := hcard

/-- The one-shot estimate gives the graph-specific composition inequality
used by the canonical witness rank screen. -/
theorem normalized_cycleLengths_card_le_oneShot_edgeCount
    (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      ((E.card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
  have hsplit := G.outsideProjection_rank_add_restrictedCycleRank E
  let d := G.cycleRank - G.restrictedCycleRank E
  have hd : d + G.restrictedCycleRank E = G.cycleRank := by
    dsimp [d]
    omega
  have hmax : G.maxRestrictedLinearForestMultiplicity E ≤ E.card + 1 := by
    unfold maxRestrictedLinearForestMultiplicity
    apply Finset.sup_le
    intro t ht
    exact restrictedLinearForestMultiplicity_le_edgeSetCard_add_one G E t
  have hphysical := cycleLengths_card_le_edgeCount (G.restrictPhysical E)
  have hbound := G.cycleLengths_card_le_oneShot_physical E
  have hmulNat :
      G.cycleLengths.card ≤
        (2 ^ d - 1) * (E.card + 1) + E.card := by
    have hphysical' : (G.restrictPhysical E).cycleLengths.card ≤ E.card := by
      change (G.restrictPhysical E).cycleLengths.card ≤
        (G.restrictPhysical E).edgeCount
      simpa [PhysicalGraph.restrictPhysical] using hphysical
    have hbound' := hbound
    change G.cycleLengths.card ≤
      (2 ^ d - 1) * G.maxRestrictedLinearForestMultiplicity E +
        (G.restrictPhysical E).cycleLengths.card at hbound'
    exact le_trans hbound' (add_le_add
      (Nat.mul_le_mul_left _ hmax) hphysical')
  have hmul :
      (G.cycleLengths.card : ℝ) ≤
        ((2 ^ d - 1 : ℕ) : ℝ) * ((E.card + 1 : ℕ) : ℝ) + (E.card : ℝ) := by
    exact_mod_cast hmulNat
  have hdenG : (0 : ℝ) < (2 : ℝ) ^ G.cycleRank := by positivity
  have hdenE : (0 : ℝ) < (2 : ℝ) ^ G.restrictedCycleRank E := by positivity
  have hpow : (2 : ℝ) ^ G.cycleRank =
      (2 : ℝ) ^ d * (2 : ℝ) ^ G.restrictedCycleRank E := by
    rw [← pow_add, hd]
  have hfac : ((2 ^ d - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (Nat.sub_le (2 ^ d) 1)
  apply (div_le_iff₀ hdenG).2
  calc
    (G.cycleLengths.card : ℝ) ≤
        ((2 ^ d - 1 : ℕ) : ℝ) * ((E.card + 1 : ℕ) : ℝ) + (E.card : ℝ) := hmul
    _ ≤ (2 : ℝ) ^ d * ((E.card + 1 : ℕ) : ℝ) + (E.card : ℝ) := by
      gcongr
    _ = (((E.card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank) * (2 : ℝ) ^ G.cycleRank := by
      rw [hpow]
      field_simp
      ring

/-- Instantiation of the one-shot composition estimate for the canonical
short-cycle support used in the `<5R` witness screen. -/
theorem canonicalWitness_oneShot_composition
    (G : PhysicalGraph) (R : ℕ)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      (((witnessSupportEdges G
          (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).card + 1 : ℕ) : ℝ) /
          (2 : ℝ) ^ (witnessSupportGraph G
            (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).cycleRank +
        (((witnessSupportEdges G
          (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).card : ℝ) /
          (2 : ℝ) ^ G.cycleRank) := by
  let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
  let E := witnessSupportEdges G F
  let W := witnessSupportGraph G F
  have h := G.normalized_cycleLengths_card_le_oneShot_edgeCount E
  have hrank : W.cycleRank = G.restrictedCycleRank E := by
    change (witnessSupportGraph G F).cycleRank = G.restrictedCycleRank E
    rw [witnessSupportGraph_eq_restrictPhysical]
    exact G.restrictPhysical_cycleRank E
  simpa [E, F, W, hrank] using h

end Erdos1016.PhysicalGraph

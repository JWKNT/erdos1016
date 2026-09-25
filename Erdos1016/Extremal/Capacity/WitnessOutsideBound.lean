import Erdos1016.Extremal.Capacity.ActualRankTail
import Erdos1016.Graph.CycleRestrictionForest

set_option autoImplicit false

/-!
# Cycle-length counting through the actual outside projection

A cycle meeting the witness and its complement restricts to a forest outside.
For each outside word there are at most `m+1` possible inside lengths. Pure
outside cycles contribute at most one length per word, and pure inside cycles
at most `m` lengths. The uniformity of projection fibers supplies the factor
`2^(-t)` exactly.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ShortProof
open PhysicalGraph

/-- Acyclicity of an outside word, extended by zero on the witness edges. -/
def IsOutsideForest (G : PhysicalGraph) (E : Finset G.Edge)
    (q : G.OutsideWord E) : Prop :=
  (G.selectedGraph (G.extendOutsideWord E q)).IsAcyclic

/-- Probability that the complement of `E` is a forest in a uniform cycle-space word. -/
def outsideForestProbability (G : PhysicalGraph) (E : Finset G.Edge) : ℝ := by
  classical
  exact ((Finset.univ.filter fun x : G.CycleSpace =>
    IsOutsideForest G E (G.outsideCycleProjection E x)).card : ℝ) /
      (2 : ℝ) ^ G.cycleRank

theorem outsideForestProbability_bounds (G : PhysicalGraph) (E : Finset G.Edge) :
    0 ≤ outsideForestProbability G E ∧ outsideForestProbability G E ≤ 1 := by
  classical
  constructor
  · unfold outsideForestProbability
    positivity
  · unfold outsideForestProbability
    apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ G.cycleRank)).2
    have h := Finset.card_le_univ (Finset.univ.filter fun x : G.CycleSpace =>
      IsOutsideForest G E (G.outsideCycleProjection E x))
    rw [G.cycleSpace_card] at h
    exact_mod_cast h

abbrev OutsideImage (G : PhysicalGraph) (E : Finset G.Edge) :=
  LinearMap.range (G.outsideCycleProjection E)

noncomputable instance outsideImageFintype (G : PhysicalGraph) (E : Finset G.Edge) :
    Fintype (OutsideImage G E) := Fintype.ofFinite _

private def outsideImageMap (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.CycleSpace) : OutsideImage G E :=
  ⟨G.outsideCycleProjection E x, ⟨x, rfl⟩⟩

private def outsideRepresentative (G : PhysicalGraph) (E : Finset G.Edge)
    (q : OutsideImage G E) : G.CycleSpace := q.2.choose

private theorem outsideRepresentative_spec (G : PhysicalGraph) (E : Finset G.Edge)
    (q : OutsideImage G E) :
    G.outsideCycleProjection E (outsideRepresentative G E q) = q.1 := q.2.choose_spec

private def outsideDecomposition (G : PhysicalGraph) (E : Finset G.Edge) :
    G.CycleSpace ≃ OutsideImage G E × LinearMap.ker (G.outsideCycleProjection E) where
  toFun x := (outsideImageMap G E x,
    ⟨x - outsideRepresentative G E (outsideImageMap G E x), by
      change G.outsideCycleProjection E (x - outsideRepresentative G E _) = 0
      rw [map_sub, outsideRepresentative_spec]
      exact sub_self _⟩)
  invFun q := q.2.1 + outsideRepresentative G E q.1
  left_inv x := sub_add_cancel _ _
  right_inv q := by
    have hq : outsideImageMap G E (q.2.1 + outsideRepresentative G E q.1) = q.1 := by
      apply Subtype.ext
      change G.outsideCycleProjection E (q.2.1 + outsideRepresentative G E q.1) = q.1.1
      rw [map_add, outsideRepresentative_spec, q.2.2, zero_add]
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      change q.2.1 + outsideRepresentative G E q.1 -
        outsideRepresentative G E (outsideImageMap G E _) = q.2.1
      rw [hq, add_sub_cancel_right]

private theorem outside_kernel_card (G : PhysicalGraph) (E : Finset G.Edge) :
    Nat.card (LinearMap.ker (G.outsideCycleProjection E)) =
      2 ^ G.restrictedCycleRank E := by
  rw [← Nat.card_congr (G.restrictedCycleSpaceEquivOutsideKernel E).toEquiv]
  simpa [F₂, restrictedCycleRank] using
    (Module.natCard_eq_pow_finrank (K := F₂) (V := G.RestrictedCycleSpace E))

theorem outsideImage_card (G : PhysicalGraph) (E : Finset G.Edge) :
    Fintype.card (OutsideImage G E) = 2 ^ (G.cycleRank - G.restrictedCycleRank E) := by
  have hdim := G.outsideProjection_rank_add_restrictedCycleRank E
  have hdim' : Module.finrank F₂ (OutsideImage G E) =
      G.cycleRank - G.restrictedCycleRank E := by
    change Module.finrank F₂ (LinearMap.range (G.outsideCycleProjection E)) = _
    omega
  simpa [F₂, hdim'] using
    (Module.card_eq_pow_finrank (K := F₂) (V := OutsideImage G E))

/-- The forest-bearing outside images, counted once each. -/
def forestOutsideImages (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset (OutsideImage G E) := by
  classical
  exact Finset.univ.filter fun q => IsOutsideForest G E q.1

private def outsideForestDecomposition (G : PhysicalGraph) (E : Finset G.Edge) :
    {x : G.CycleSpace // IsOutsideForest G E (G.outsideCycleProjection E x)} ≃
      {q : OutsideImage G E // IsOutsideForest G E q.1} ×
        LinearMap.ker (G.outsideCycleProjection E) where
  toFun x := (⟨(outsideDecomposition G E x.1).1, x.2⟩,
    (outsideDecomposition G E x.1).2)
  invFun q := ⟨(outsideDecomposition G E).symm (q.1.1, q.2), by
    have h := congrArg Prod.fst ((outsideDecomposition G E).apply_symm_apply (q.1.1, q.2))
    have hval := congrArg Subtype.val h
    change G.outsideCycleProjection E ((outsideDecomposition G E).symm (q.1.1, q.2)) =
      q.1.1.1 at hval
    rw [hval]
    exact q.1.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (outsideDecomposition G E).symm_apply_apply x.1
  right_inv q := by
    have h := (outsideDecomposition G E).apply_symm_apply (q.1.1, q.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change ((outsideDecomposition G E)
        ((outsideDecomposition G E).symm (q.1.1, q.2))).2 = q.2
      exact congrArg Prod.snd h

/-- Projection fibers all have size `2^t`, including those satisfying the forest event. -/
theorem forestOutsideImages_card_mul (G : PhysicalGraph) (E : Finset G.Edge) :
    ((forestOutsideImages G E).card : ℝ) * (2 : ℝ) ^ G.restrictedCycleRank E =
      outsideForestProbability G E * (2 : ℝ) ^ G.cycleRank := by
  classical
  have h := Nat.card_congr (outsideForestDecomposition G E)
  rw [Nat.card_prod, outside_kernel_card] at h
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  have hr : (((Finset.univ.filter fun x : G.CycleSpace =>
      IsOutsideForest G E (G.outsideCycleProjection E x)).card : ℕ) : ℝ) =
      ((forestOutsideImages G E).card : ℝ) * (2 : ℝ) ^ G.restrictedCycleRank E := by
    exact_mod_cast h
  rw [← hr]
  unfold outsideForestProbability
  exact (div_mul_cancel₀ _ (by positivity)).symm

private theorem outside_selectedGraph_eq (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.Word) :
    G.selectedGraph (G.extendOutsideWord E (G.restrictOutsideWord E x)) =
      G.restrictedSelectedGraph Eᶜ (G.restrictWord Eᶜ x) := by
  classical
  ext u v
  constructor
  · rintro ⟨e, he, h⟩
    have hout : e ∉ E := by
      intro hm
      simp [extendOutsideWord, hm] at he
    exact ⟨⟨e, Finset.mem_compl.mpr hout⟩,
      by simpa [restrictWord, extendOutsideWord, restrictOutsideWord, hout] using he, h⟩
  · rintro ⟨e, he, h⟩
    have hout : e.1 ∉ E := Finset.mem_compl.mp e.2
    exact ⟨e.1,
      by simpa [restrictWord, extendOutsideWord, restrictOutsideWord, hout] using he, h⟩

/-- A cycle meeting the witness restricts to an acyclic outside word. -/
theorem cycle_outside_isForest (G : PhysicalGraph) (E : Finset G.Edge)
    (C : G.CycleWord) (hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0) :
    IsOutsideForest G E (G.restrictOutsideWord E C.1) := by
  unfold IsOutsideForest
  rw [outside_selectedGraph_eq]
  obtain ⟨e, he, hx⟩ := hin
  exact CycleRestrictionForest.restrictedCycle_isAcyclic G C Eᶜ
    ⟨e, by simpa using he, hx⟩

private def mixedLengthCandidates (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset ℕ := by
  classical
  exact (forestOutsideImages G E).biUnion fun q =>
    (Finset.range (E.card + 1)).image fun a => a + G.outsideWordLength E q.1

private theorem cycle_length_mem_candidates (G : PhysicalGraph) (E : Finset G.Edge)
    (C : G.CycleWord) :
    G.wordLength C.1 ∈ Finset.Icc 1 E.card ∪
      ((Finset.univ.image fun q : OutsideImage G E => G.outsideWordLength E q.1) ∪
        mixedLengthCandidates G E) := by
  classical
  let q : OutsideImage G E := outsideImageMap G E ⟨C.1, C.2.2.1⟩
  have hpart := G.wordLength_partition E C.1
  by_cases hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0
  · by_cases hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨q, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cycle_outside_isForest G E C hin⟩
      · apply Finset.mem_image.mpr
        refine ⟨G.restrictedWordLength E (G.restrictWord E C.1), ?_, hpart.symm⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le
          (G.restrictedWordLength_le_edgeSetCard E _))
    · have hz : G.restrictWord E C.1 = 0 := by
        funext e
        by_contra h
        exact hin ⟨e.1, e.2, h⟩
      have hzero : G.restrictedWordLength E (G.restrictWord E C.1) = 0 := by
        rw [hz]
        simp [restrictedWordLength]
      rw [hzero, zero_add] at hpart
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hpart.symm⟩))))
  · have hz : G.restrictOutsideWord E C.1 = 0 := by
      funext e
      by_contra h
      exact hout ⟨e.1, e.2, h⟩
    have hzero : G.outsideWordLength E (G.restrictOutsideWord E C.1) = 0 := by
      rw [hz]
      simp [outsideWordLength]
    rw [hzero, add_zero] at hpart
    have hpos : 0 < G.wordLength C.1 := by
      apply Finset.card_pos.mpr
      have he : ∃ e, C.1 e ≠ 0 := by
        by_contra h
        push_neg at h
        exact C.2.1 (funext h)
      obtain ⟨e, he⟩ := he
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr
      ⟨hpos, hpart.trans_le (G.restrictedWordLength_le_edgeSetCard E _)⟩))

/-- Finite counting before normalization: mixed, outside, and inside contributions. -/
theorem cycleLengths_card_le_outside (G : PhysicalGraph) (E : Finset G.Edge) :
    G.cycleLengths.card ≤ (E.card + 1) * (forestOutsideImages G E).card +
      2 ^ (G.cycleRank - G.restrictedCycleRank E) + E.card := by
  classical
  have hsub : G.cycleLengths ⊆ Finset.Icc 1 E.card ∪
      ((Finset.univ.image fun q : OutsideImage G E => G.outsideWordLength E q.1) ∪
        mixedLengthCandidates G E) := by
    intro l hl
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hl
    exact cycle_length_mem_candidates G E C
  have hmix : (mixedLengthCandidates G E).card ≤
      (forestOutsideImages G E).card * (E.card + 1) := by
    unfold mixedLengthCandidates
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _q ∈ forestOutsideImages G E, (E.card + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        exact (Finset.card_image_le).trans (by rw [Finset.card_range])
      _ = _ := by simp
  have hpure : (Finset.univ.image fun q : OutsideImage G E =>
      G.outsideWordLength E q.1).card ≤ 2 ^ (G.cycleRank - G.restrictedCycleRank E) := by
    exact Finset.card_image_le.trans (by rw [Finset.card_univ, outsideImage_card])
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h' := Finset.card_union_le
    (Finset.univ.image fun q : OutsideImage G E => G.outsideWordLength E q.1)
    (mixedLengthCandidates G E)
  have hicc : (Finset.Icc 1 E.card).card = E.card := by simp
  rw [hicc] at h
  rw [Nat.mul_comm] at hmix
  omega

/-- The exact normalized outside-forest bound for any witness edge set. -/
theorem normalized_cycleLengths_card_le_outside (G : PhysicalGraph) (E : Finset G.Edge) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank ≤
      ((E.card : ℝ) + 1) / (2 : ℝ) ^ G.restrictedCycleRank E *
          outsideForestProbability G E +
        1 / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
  have hcount : (G.cycleLengths.card : ℝ) ≤
      ((E.card : ℝ) + 1) * (forestOutsideImages G E).card +
      (2 : ℝ) ^ (G.cycleRank - G.restrictedCycleRank E) + E.card := by
    exact_mod_cast cycleLengths_card_le_outside G E
  have hpowG : (0 : ℝ) < 2 ^ G.cycleRank := by positivity
  have hpowE : (0 : ℝ) < 2 ^ G.restrictedCycleRank E := by positivity
  have hsplit : (2 : ℝ) ^ (G.cycleRank - G.restrictedCycleRank E) *
      (2 : ℝ) ^ G.restrictedCycleRank E = (2 : ℝ) ^ G.cycleRank := by
    rw [← pow_add, Nat.sub_add_cancel (G.restrictedCycleRank_le E)]
  have hforest := forestOutsideImages_card_mul G E
  have hid :
      (((E.card : ℝ) + 1) / (2 : ℝ) ^ G.restrictedCycleRank E *
        outsideForestProbability G E + 1 / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank) * (2 : ℝ) ^ G.cycleRank =
      ((E.card : ℝ) + 1) * (forestOutsideImages G E).card +
        (2 : ℝ) ^ (G.cycleRank - G.restrictedCycleRank E) + E.card := by
    have hf : outsideForestProbability G E * (2 : ℝ) ^ G.cycleRank /
        (2 : ℝ) ^ G.restrictedCycleRank E = (forestOutsideImages G E).card :=
      (div_eq_iff hpowE.ne').2 hforest.symm
    have hd : (2 : ℝ) ^ G.cycleRank / (2 : ℝ) ^ G.restrictedCycleRank E =
        (2 : ℝ) ^ (G.cycleRank - G.restrictedCycleRank E) :=
      (div_eq_iff hpowE.ne').2 hsplit.symm
    calc
      _ = ((E.card : ℝ) + 1) *
          (outsideForestProbability G E * (2 : ℝ) ^ G.cycleRank /
            (2 : ℝ) ^ G.restrictedCycleRank E) +
          (2 : ℝ) ^ G.cycleRank / (2 : ℝ) ^ G.restrictedCycleRank E + E.card := by
        field_simp
        ring
      _ = _ := by rw [hf, hd]
  exact (div_le_iff₀ hpowG).2 (by rw [hid]; exact hcount)

/-- Initial coverage through `L` satisfies the outside-forest inequality of
Section 3, with the actual witness rank and actual host cycle rank. -/
theorem coverageDensity_le_outsideForest (G : PhysicalGraph) (E : Finset G.Edge)
    {L : ℕ} (hL : G.InitialCoverage L) :
    coverageDensity G L ≤
      ((E.card : ℝ) + 1) / (2 : ℝ) ^ G.restrictedCycleRank E *
          outsideForestProbability G E +
        1 / (2 : ℝ) ^ G.restrictedCycleRank E +
        (E.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
  have hcard := Finset.card_le_card hL
  have hnat : L ≤ G.cycleLengths.card + 2 := by
    simp only [Nat.card_Icc] at hcard
    omega
  have hreal : (L : ℝ) - 2 ≤ G.cycleLengths.card := by
    have hcast : (L : ℝ) ≤ (G.cycleLengths.card : ℝ) + 2 := by exact_mod_cast hnat
    linarith
  exact (div_le_div_of_nonneg_right hreal (by positivity)).trans
    (normalized_cycleLengths_card_le_outside G E)

end Erdos1016.ShortProof

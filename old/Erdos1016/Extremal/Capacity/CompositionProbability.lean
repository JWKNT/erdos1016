import Erdos1016.Extremal.Capacity.CycleLengthCount
import Erdos1016.Extremal.Capacity.ComplementRank

set_option autoImplicit false

/-!
# Probability that one edge piece is a linear forest

The probability space is the uniform finite host cycle space. This module
records the event and the complete-boundary-fiber counting interface used to
compare its mass with local linear-forest multiplicities.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PhysicalGraph

/-- Host cycle states whose outside edge restriction is a linear forest. -/
def outsideLinearForestStates (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset G.CycleSpace := by
  classical
  exact Finset.univ.filter fun x =>
    G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ x.1)

/-- Uniform cycle-space probability of an outside linear forest. -/
def outsideLinearForestProbability (G : PhysicalGraph) (E : Finset G.Edge) : ℝ :=
  (G.outsideLinearForestStates E).card / (2 : ℝ) ^ G.cycleRank



/-- Reindexing the outside restriction gives the ordinary complement
restriction of the same host word. -/
theorem outsideWordEquivRestrictedComplement_apply
    (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.outsideWordEquivRestrictedComplement E (G.restrictOutsideWord E x) =
      G.restrictWord Eᶜ x := by
  funext e
  rfl





/-- The number of distinct local forest lengths never exceeds the number of
actual forest words in that complete boundary fiber. -/
theorem restrictedMultiplicity_le_linearForestWordCard
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand) :
    G.restrictedLinearForestMultiplicity E t ≤
      Fintype.card (G.RestrictedLinearForestWord E t) := by
  unfold restrictedLinearForestMultiplicity restrictedLinearForestLengths
  simpa only [Fintype.card_coe] using
    (Finset.card_image_le :
    (Finset.univ.image
        (fun x : G.RestrictedLinearForestWord E t =>
          G.restrictedWordLength E x.1)).card ≤ Finset.univ.card)

/-- A feasible inside boundary fiber has exactly `2^restrictedRank E` words. -/
theorem restrictedBoundaryFiber_card_of_commonBoundary
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand)
    (ht : t ∈ LinearMap.range (G.commonBoundaryMap E)) :
    Fintype.card (G.RestrictedBoundaryFiber E t) =
      2 ^ G.restrictedCycleRank E := by
  obtain ⟨x, hx⟩ := ht
  let z : G.CommonBoundaryFiber E t := ⟨x, hx⟩
  let p := (G.commonBoundaryFiberEquiv E t) z
  have hnat := Parity.fiber_natCard (G.restrictedBoundary E) p.1
  calc
    Fintype.card (G.RestrictedBoundaryFiber E t) =
        Nat.card (G.RestrictedBoundaryFiber E t) := by simp
    _ = Nat.card (Parity.Fiber (G.restrictedBoundary E) t) := rfl
    _ = 2 ^ Module.finrank F₂ (LinearMap.ker (G.restrictedBoundary E)) := hnat
    _ = 2 ^ G.restrictedCycleRank E := by simp [restrictedCycleRank]

/-- Outside boundary words that are linear forests, reindexed as words on the
complement edge set. -/
abbrev OutsideLinearForestFiber (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.OutsideBoundaryFiber E t //
    G.IsRestrictedLinearForest Eᶜ
      (G.outsideWordEquivRestrictedComplement E x.1)}

noncomputable instance outsideLinearForestFiberFintype (G : PhysicalGraph)
    (E : Finset G.Edge) (t : G.Demand) :
    Fintype (G.OutsideLinearForestFiber E t) := Fintype.ofFinite _

/-- The outside linear-forest fiber is the restricted complement forest
fiber with its edge labels reindexed. -/
def outsideLinearForestFiberEquiv (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :
    G.OutsideLinearForestFiber E t ≃
      G.RestrictedLinearForestWord Eᶜ t where
  toFun x := by
    refine ⟨G.outsideWordEquivRestrictedComplement E x.1.1, ?_, x.2⟩
    have h := G.outsideBoundary_eq_restrictedComplement E x.1.1
    rw [x.1.2] at h
    exact h.symm
  invFun x := by
    refine ⟨⟨(G.outsideWordEquivRestrictedComplement E).symm x.1,
      ?_⟩, ?_⟩
    · have h := G.outsideBoundary_eq_restrictedComplement E
        ((G.outsideWordEquivRestrictedComplement E).symm x.1)
      simpa using h.trans x.2.1
    · simpa using x.2.2
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- Distinct complement-forest lengths are bounded by the number of
complement linear-forest words in the outside boundary fiber. -/
theorem complementMultiplicity_le_outsideForestFiber_card
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand) :
    G.restrictedLinearForestMultiplicity Eᶜ t ≤
      Fintype.card (G.OutsideLinearForestFiber E t) := by
  rw [Fintype.card_congr (G.outsideLinearForestFiberEquiv E t)]
  exact G.restrictedMultiplicity_le_linearForestWordCard Eᶜ t

/-- A fixed common-boundary fiber, restricted to the desired event, is exactly
the product of the complete inside parity fiber and the outside linear-forest
fiber. -/
def commonBoundaryForestFiberEquiv (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :
    {x : G.CommonBoundaryFiber E t //
      G.IsRestrictedLinearForest Eᶜ
        (G.restrictWord Eᶜ x.1.1)} ≃
      G.RestrictedBoundaryFiber E t × G.OutsideLinearForestFiber E t where
  toFun x := by
    let p := G.commonBoundaryFiberEquiv E t x.1
    have hforest : G.IsRestrictedLinearForest Eᶜ
        (G.outsideWordEquivRestrictedComplement E p.2.1) := by
      have houtside : (p.2).1 = G.restrictOutsideWord E x.1.1 := rfl
      rw [houtside, G.outsideWordEquivRestrictedComplement_apply]
      exact x.2
    exact (p.1, ⟨p.2, hforest⟩)
  invFun p := by
    let z := (G.commonBoundaryFiberEquiv E t).symm (p.1, p.2.1)
    refine ⟨z, ?_⟩
    have hz := congrArg Prod.snd
      ((G.commonBoundaryFiberEquiv E t).apply_symm_apply (p.1, p.2.1))
    have hout := congrArg Subtype.val hz
    have hreindex := G.outsideWordEquivRestrictedComplement_apply E z.1.1
    have hout' : G.restrictOutsideWord E z.1.1 = p.2.1.1 := by
      simpa [z, commonBoundaryFiberEquiv] using hout
    have htransport :
        G.outsideWordEquivRestrictedComplement E p.2.1.1 =
          G.restrictWord Eᶜ z.1.1 := by
      rw [← hout']
      exact hreindex
    have hp : G.IsRestrictedLinearForest Eᶜ
        (G.outsideWordEquivRestrictedComplement E
          (G.restrictOutsideWord E z.1.1)) := by
      simpa [hout'] using p.2.2
    exact hreindex ▸ hp
  left_inv := by
    intro x
    apply Subtype.ext
    change (G.commonBoundaryFiberEquiv E t).symm
      (G.commonBoundaryFiberEquiv E t x.1) = x.1
    exact Equiv.symm_apply_apply _ _
  right_inv := by
    intro p
    apply Prod.ext
    · change ((G.commonBoundaryFiberEquiv E t).symm
        (p.1, p.2.1) |> G.commonBoundaryFiberEquiv E t).1 = p.1
      exact congrArg Prod.fst (Equiv.apply_symm_apply _ _)
    · apply Subtype.ext
      have hpair := (G.commonBoundaryFiberEquiv E t).apply_symm_apply
        (p.1, p.2.1)
      exact congrArg (fun q : G.RestrictedBoundaryFiber E t ×
        G.OutsideBoundaryFiber E t => q.2) hpair

/-- The event is the disjoint union of its complete common-boundary fibers. -/
abbrev OutsideForestDemandFiber (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) :=
  {x : G.CommonBoundaryFiber E t //
    G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ x.1.1)}

def outsideLinearForestDemandDecomposition (G : PhysicalGraph)
    (E : Finset G.Edge) :
    {x : G.CycleSpace // x ∈ G.outsideLinearForestStates E} ≃
      Σ t : G.Demand, G.OutsideForestDemandFiber E t where
  toFun x := by
    classical
    let t := G.commonBoundaryMap E x.1
    have hevent : G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ x.1.1) := by
      have hx := x.2
      change x.1 ∈ Finset.univ.filter
        (fun z : G.CycleSpace =>
          G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ z.1)) at hx
      exact (Finset.mem_filter.mp hx).2
    exact ⟨t, ⟨⟨x.1, rfl⟩, hevent⟩⟩
  invFun y := by
    classical
    refine ⟨y.2.1.1, ?_⟩
    simp only [outsideLinearForestStates, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact y.2.2
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨t, ⟨⟨x, hx⟩, hforest⟩⟩
    cases hx
    rfl

/-- Count the event exactly by its common-boundary demand. Each fiber factors
into its inside boundary choices and outside linear-forest choices. -/
theorem outsideLinearForestStates_card_eq_sum (G : PhysicalGraph)
    (E : Finset G.Edge) :
    (G.outsideLinearForestStates E).card =
      ∑ t : G.Demand,
        Fintype.card (G.RestrictedBoundaryFiber E t) *
          Fintype.card (G.OutsideLinearForestFiber E t) := by
  classical
  calc
    (G.outsideLinearForestStates E).card =
        Fintype.card {x : G.CycleSpace // x ∈ G.outsideLinearForestStates E} := by
      simp only [Fintype.card_coe]
    _ = Fintype.card (Σ t : G.Demand, G.OutsideForestDemandFiber E t) :=
      Fintype.card_congr (G.outsideLinearForestDemandDecomposition E)
    _ = ∑ t : G.Demand, Fintype.card (G.OutsideForestDemandFiber E t) :=
      Fintype.card_sigma
    _ = ∑ t : G.Demand,
        Fintype.card (G.RestrictedBoundaryFiber E t ×
          G.OutsideLinearForestFiber E t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact Fintype.card_congr (G.commonBoundaryForestFiberEquiv E t)
    _ = _ := by simp [Fintype.card_prod]

/-- Each active nonzero demand contributes at least one inside parity fiber
for every distinct outside forest length. Demand zero contributes the empty
outside forest, giving the additive baseline. -/
theorem outsideLinearForestStates_card_lower_bound (G : PhysicalGraph)
    (E : Finset G.Edge) :
    2 ^ G.restrictedCycleRank E *
        (1 + ∑ t ∈ G.activeCommonBoundaryDemands E,
          G.restrictedLinearForestMultiplicity Eᶜ t) ≤
      (G.outsideLinearForestStates E).card := by
  classical
  let U := G.activeCommonBoundaryDemands E
  let N := 2 ^ G.restrictedCycleRank E
  let g : G.Demand → ℕ := fun t =>
    Fintype.card (G.RestrictedBoundaryFiber E t) *
      Fintype.card (G.OutsideLinearForestFiber E t)
  have hzrange : (0 : G.Demand) ∈ LinearMap.range (G.commonBoundaryMap E) := by
    exact ⟨0, by simp [commonBoundaryMap]⟩
  have hinside0 := G.restrictedBoundaryFiber_card_of_commonBoundary E 0 hzrange
  have houtzero : Nonempty (G.OutsideLinearForestFiber E 0) := by
    refine ⟨⟨⟨0, ?_⟩, ?_⟩⟩
    · simp [outsideBoundary]
    · have hlf := G.restrictWord_linearForest Eᶜ 0 G.zero_isLinearForest
      simpa using hlf
  have houtzero_card : 1 ≤ Fintype.card (G.OutsideLinearForestFiber E 0) := by
    have hpos := Fintype.card_pos_iff.mpr houtzero
    omega
  have hzterm : N ≤ g 0 := by
    dsimp [g, N]
    rw [hinside0]
    calc
      2 ^ G.restrictedCycleRank E = 2 ^ G.restrictedCycleRank E * 1 := by simp
      _ ≤ 2 ^ G.restrictedCycleRank E *
          Fintype.card (G.OutsideLinearForestFiber E 0) :=
        Nat.mul_le_mul_left _ houtzero_card
  have hterm : ∀ t ∈ U,
      N * G.restrictedLinearForestMultiplicity Eᶜ t ≤ g t := by
    intro t ht
    have hin := G.restrictedBoundaryFiber_card_of_commonBoundary E t
      ((G.mem_activeCommonBoundaryDemands E t).1 (by simpa [U] using ht)).2
    have hout := G.complementMultiplicity_le_outsideForestFiber_card E t
    dsimp [g, N]
    rw [hin]
    exact Nat.mul_le_mul_left _ hout
  have hznot : (0 : G.Demand) ∉ U := by
    intro h
    have hnz := (G.mem_activeCommonBoundaryDemands E 0).1 (by simpa [U] using h)
    exact hnz.1 rfl
  have hdisj : Disjoint U {0} := Finset.disjoint_singleton_right.mpr hznot
  have hsubset : U ∪ {0} ⊆ Finset.univ := by intro t ht; simp
  have hsumSubset := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun t _ _ => Nat.zero_le (g t))
  have hsumU :
      ∑ t ∈ U, N * G.restrictedLinearForestMultiplicity Eᶜ t ≤
        ∑ t ∈ U, g t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hterm t ht
  have hsumUnion :
      ∑ t ∈ U ∪ {0}, g t = (∑ t ∈ U, g t) + g 0 := by
    rw [Finset.sum_union hdisj]
    simp
  have htarget : N * (1 +
      ∑ t ∈ U, G.restrictedLinearForestMultiplicity Eᶜ t) ≤
        ∑ t ∈ U ∪ {0}, g t := by
    rw [hsumUnion]
    calc
      N * (1 + ∑ t ∈ U, G.restrictedLinearForestMultiplicity Eᶜ t) =
          N + ∑ t ∈ U, N * G.restrictedLinearForestMultiplicity Eᶜ t := by
        simp [Nat.mul_add, Finset.mul_sum]
      _ ≤ g 0 + ∑ t ∈ U, g t := add_le_add hzterm hsumU
      _ = _ := by omega
  have htotal := G.outsideLinearForestStates_card_eq_sum E
  rw [htotal]
  simpa [U] using htarget.trans hsumSubset

/-- The physical composition-probability inequality: active nonzero-demand
outside forest multiplicities, normalized by the outside rank plus the common
boundary rank, are paid for by the event probability after reserving the
zero-demand empty forest. -/
theorem complementMultiplicity_sum_normalized_le_probability_sub_baseline
    (G : PhysicalGraph) (E : Finset G.Edge) :
    (∑ t ∈ G.activeCommonBoundaryDemands E,
      (G.restrictedLinearForestMultiplicity Eᶜ t : ℝ)) /
        (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) ≤
      G.outsideLinearForestProbability E -
        1 / (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) := by
  classical
  let U := G.activeCommonBoundaryDemands E
  let N : ℝ := (2 : ℝ) ^ G.restrictedCycleRank E
  let D : ℝ := (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E)
  let μ : G.Demand → ℕ := G.restrictedLinearForestMultiplicity Eᶜ
  have hcountNat := G.outsideLinearForestStates_card_lower_bound E
  have hcountReal : N * (1 + ∑ t ∈ U, (μ t : ℝ)) ≤
      ((G.outsideLinearForestStates E).card : ℝ) := by
    dsimp [N, U, μ]
    exact_mod_cast hcountNat
  have hden : (2 : ℝ) ^ G.cycleRank = N * D := by
    dsimp [N, D]
    rw [G.cycleRank_edgePartition E]
    simp [pow_add, mul_assoc]
  have hN : 0 < N := by positivity
  have hD : 0 < D := by positivity
  have hratio :
      (1 + ∑ t ∈ U, (μ t : ℝ)) / D ≤
        G.outsideLinearForestProbability E := by
    unfold outsideLinearForestProbability
    rw [hden]
    calc
      (1 + ∑ t ∈ U, (μ t : ℝ)) / D =
          (N * (1 + ∑ t ∈ U, (μ t : ℝ))) / (N * D) := by
        field_simp [ne_of_gt hN, ne_of_gt hD]
        ring
      _ ≤ (G.outsideLinearForestStates E).card / (N * D) :=
        div_le_div_of_nonneg_right hcountReal (by positivity)
  have hsplit :
      (1 + ∑ t ∈ U, (μ t : ℝ)) / D =
        (∑ t ∈ U, (μ t : ℝ)) / D + 1 / D := by
    field_simp [ne_of_gt hD]
    ring
  rw [hsplit] at hratio
  dsimp [U, D, μ] at hratio ⊢
  linarith



end Erdos1016.PhysicalGraph

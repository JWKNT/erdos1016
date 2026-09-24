import Erdos1016.Extremal.Capacity.LinearForestRestriction
import Erdos1016.Extremal.Capacity.CompositionArithmetic

set_option autoImplicit false

noncomputable section
namespace Erdos1016
namespace Proof
namespace CapacityBridge

open Erdos1016

/-- Outside restrictions that occur in a fixed feasible parity fiber. -/
def outsideParityImage (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) : Finset (G.OutsideWord E) := by
  classical
  exact Finset.univ.image fun x : G.TJoin t => G.restrictOutsideWord E x.1

/-- The number of possible outside words in a fixed demand fiber is at most
`2^(rank G - rank (G|E))`. The image is an affine translate of the image of
the cycle-space outside projection. -/
theorem outsideParityImage_card_le (G : PhysicalGraph) (E : Finset G.Edge)
    (t : G.Demand) (x₀ : G.TJoin t) :
    (outsideParityImage G E t).card ≤
      2 ^ (G.cycleRank - G.restrictedCycleRank E) := by
  classical
  let f : G.CycleSpace →ₗ[F₂] G.OutsideWord E := G.outsideCycleProjection E
  let R := LinearMap.range f
  let q₀ : G.OutsideWord E := G.restrictOutsideWord E x₀.1
  let image := outsideParityImage G E t
  let φ : image → R := fun q => by
    let x : G.TJoin t := Classical.choose (Finset.mem_image.mp q.2)
    have hx : G.restrictOutsideWord E x.1 = q.1 :=
      (Finset.mem_image.mp q.2).choose_spec.2
    let z : G.CycleSpace := ⟨x.1 - x₀.1, by
      change G.boundary (x.1 - x₀.1) = 0
      rw [map_sub, x.2, x₀.2, sub_self]⟩
    refine ⟨f z, ?_⟩
    change f z ∈ LinearMap.range f
    exact ⟨z, rfl⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg Subtype.val hab
    change G.restrictOutsideWord E
      ((Classical.choose (Finset.mem_image.mp a.2)).1 - x₀.1) =
      G.restrictOutsideWord E
      ((Classical.choose (Finset.mem_image.mp b.2)).1 - x₀.1) at hval
    have hcancel := congrArg (fun z : G.OutsideWord E => z + q₀) hval
    have hxa : G.restrictOutsideWord E
        (Classical.choose (Finset.mem_image.mp a.2)).1 = a.1 :=
      (Finset.mem_image.mp a.2).choose_spec.2
    have hleft :
        G.restrictOutsideWord E
          (((Classical.choose (Finset.mem_image.mp a.2)).1) - x₀.1) + q₀ = a.1 := by
      have hsum :
          G.restrictOutsideWord E
            (((Classical.choose (Finset.mem_image.mp a.2)).1) - x₀.1) + q₀ =
          G.restrictOutsideWord E (Classical.choose (Finset.mem_image.mp a.2)).1 := by
        funext e
        change (((Classical.choose (Finset.mem_image.mp a.2)).1) e.1 -
          x₀.1 e.1) + x₀.1 e.1 = _
        exact sub_add_cancel _ _
      exact hsum.trans hxa
    have hxb : G.restrictOutsideWord E
        (Classical.choose (Finset.mem_image.mp b.2)).1 = b.1 :=
      (Finset.mem_image.mp b.2).choose_spec.2
    have hright :
        G.restrictOutsideWord E
          (((Classical.choose (Finset.mem_image.mp b.2)).1) - x₀.1) + q₀ = b.1 := by
      have hsum :
          G.restrictOutsideWord E
            (((Classical.choose (Finset.mem_image.mp b.2)).1) - x₀.1) + q₀ =
          G.restrictOutsideWord E (Classical.choose (Finset.mem_image.mp b.2)).1 := by
        funext e
        change (((Classical.choose (Finset.mem_image.mp b.2)).1) e.1 -
          x₀.1 e.1) + x₀.1 e.1 = _
        exact sub_add_cancel _ _
      exact hsum.trans hxb
    exact hleft.symm.trans (hcancel.trans hright)
  have hcardR : Fintype.card R =
      2 ^ Module.finrank F₂ R := by
    simpa [F₂] using (Module.card_eq_pow_finrank (K := F₂) (V := R))
  have hrank := G.outsideProjection_rank_add_restrictedCycleRank E
  have hdim : Module.finrank F₂ R = G.cycleRank - G.restrictedCycleRank E := by
    dsimp [R, f]
    omega
  calc
    image.card ≤ Fintype.card R := by
      simpa using Fintype.card_le_of_injective φ hφ
    _ = 2 ^ (G.cycleRank - G.restrictedCycleRank E) := by rw [hcardR, hdim]


/-- A local forest length splits into a restricted forest length and the fixed
length of its outside word. -/
theorem linearForestLengths_subset_restricted_sumsets
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand) :
    G.linearForestLengths t ⊆
      (outsideParityImage G E t).biUnion fun q =>
        Capacity.naturalSumset
          (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q))
          {G.outsideWordLength E q} := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
  let q := G.restrictOutsideWord E x.1
  let xT : G.TJoin t := ⟨x.1, x.2.1⟩
  have hq : q ∈ outsideParityImage G E t := by
    apply Finset.mem_image.mpr
    exact ⟨xT, Finset.mem_univ _, rfl⟩
  have hsplit := G.boundary_inside_add_outside E x.1
  rw [x.2.1] at hsplit
  have hdemand : G.restrictedBoundary E (G.restrictWord E x.1) =
      t - G.outsideBoundary E q := by
    exact (Parity.split_equation (G.restrictedBoundary E) (G.outsideBoundary E)
      (G.restrictWord E x.1) q t).1 (by simpa [q] using hsplit)
  let y : G.RestrictedLinearForestWord E (t - G.outsideBoundary E q) :=
    ⟨G.restrictWord E x.1, hdemand,
      G.restrictWord_linearForest E x.1 x.2.2⟩
  have hlen := G.wordLength_partition E x.1
  refine Finset.mem_biUnion.mpr ⟨q, hq, ?_⟩
  unfold Capacity.naturalSumset
  apply Finset.mem_image.mpr
  refine ⟨(G.restrictedWordLength E y.1, G.outsideWordLength E q), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · change G.restrictedWordLength E y.1 ∈
        Finset.univ.image (fun z : G.RestrictedLinearForestWord E
          (t - G.outsideBoundary E q) => G.restrictedWordLength E z.1)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_singleton.mpr rfl
  · change G.restrictedWordLength E y.1 + G.outsideWordLength E q = _
    rw [← hlen]



/-- For a fixed feasible host demand, distinct forest lengths are bounded by
the number of outside fibers times the maximum restricted multiplicity. -/
theorem linearForestMultiplicity_le_outside_count_mul_restricted_max
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand)
    (x₀ : G.TJoin t) :
    G.linearForestMultiplicity t ≤
      2 ^ (G.cycleRank - G.restrictedCycleRank E) *
        G.maxRestrictedLinearForestMultiplicity E := by
  classical
  let Q := outsideParityImage G E t
  have hsubset := linearForestLengths_subset_restricted_sumsets G E t
  have hunion := Capacity.card_biUnion_naturalSumsets_le Q
    (fun q => G.restrictedLinearForestLengths E (t - G.outsideBoundary E q))
    (fun q => {G.outsideWordLength E q})
  have hterm : ∀ q ∈ Q,
      (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q)).card ≤
        G.maxRestrictedLinearForestMultiplicity E := by
    intro q hq
    unfold PhysicalGraph.maxRestrictedLinearForestMultiplicity
    change G.restrictedLinearForestMultiplicity E (t - G.outsideBoundary E q) ≤
      Finset.univ.sup (G.restrictedLinearForestMultiplicity E)
    exact Finset.le_sup (f := G.restrictedLinearForestMultiplicity E)
      (Finset.mem_univ (t - G.outsideBoundary E q))
  calc
    G.linearForestMultiplicity t = (G.linearForestLengths t).card := rfl
    _ ≤ (Q.biUnion fun q => Capacity.naturalSumset
        (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q))
        {G.outsideWordLength E q}).card := Finset.card_le_card hsubset
    _ ≤ ∑ q ∈ Q,
        (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q)).card := by
      calc
        _ ≤ ∑ q ∈ Q,
          (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q)).card *
            (({G.outsideWordLength E q} : Finset ℕ)).card := hunion
        _ = ∑ q ∈ Q,
          (G.restrictedLinearForestLengths E (t - G.outsideBoundary E q)).card := by simp
    _ ≤ ∑ q ∈ Q, G.maxRestrictedLinearForestMultiplicity E := by
      apply Finset.sum_le_sum
      intro q hq
      exact hterm q hq
    _ = Q.card * G.maxRestrictedLinearForestMultiplicity E := by simp [Q]
    _ ≤ 2 ^ (G.cycleRank - G.restrictedCycleRank E) *
          G.maxRestrictedLinearForestMultiplicity E :=
      Nat.mul_le_mul_right _ (outsideParityImage_card_le G E t x₀)


/-- Maximizing over all demands preserves the same normalized counting bound. -/
theorem maxLinearForestMultiplicity_le_power_mul_restricted_max
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.maxLinearForestMultiplicity ≤
      2 ^ (G.cycleRank - G.restrictedCycleRank E) *
        G.maxRestrictedLinearForestMultiplicity E := by
  classical
  unfold PhysicalGraph.maxLinearForestMultiplicity
  apply Finset.sup_le
  intro t ht
  by_cases hne : Nonempty (G.LinearForestWord t)
  · obtain ⟨x⟩ := hne
    let x₀ : G.TJoin t := ⟨x.1, x.2.1⟩
    exact (linearForestMultiplicity_le_outside_count_mul_restricted_max
      G E t x₀)
  · haveI : IsEmpty (G.LinearForestWord t) := not_nonempty_iff.mp hne
    have hcard : Fintype.card (G.LinearForestWord t) = 0 := Fintype.card_eq_zero
    have hmult : G.linearForestMultiplicity t = 0 := by
      have hle : G.linearForestMultiplicity t ≤
          Fintype.card (G.LinearForestWord t) := by
        unfold PhysicalGraph.linearForestMultiplicity
          PhysicalGraph.linearForestLengths
        exact Finset.card_image_le
      rw [hcard] at hle
      exact Nat.eq_zero_of_le_zero hle
    rw [hmult]
    exact Nat.zero_le _

/-- Edge restriction can only increase normalized numerical capacity. This is
the paper's restriction-monotonicity lemma in the project's inherited-label
model for an edge subgraph. -/
theorem normalizedLinearForestCapacity_le_restricted
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.normalizedLinearForestCapacity ≤
      G.normalizedRestrictedLinearForestCapacity E := by
  unfold PhysicalGraph.normalizedLinearForestCapacity
    PhysicalGraph.normalizedRestrictedLinearForestCapacity
  let k := G.cycleRank - G.restrictedCycleRank E
  have hr : G.cycleRank = G.restrictedCycleRank E + k := by
    dsimp [k]
    have hle := G.restrictedCycleRank_le E
    omega
  have hpow : (2 : ℝ) ^ G.cycleRank =
      (2 : ℝ) ^ G.restrictedCycleRank E * (2 : ℝ) ^ k := by
    rw [hr, pow_add]
  have hnumNat := maxLinearForestMultiplicity_le_power_mul_restricted_max G E
  have hnum : (G.maxLinearForestMultiplicity : ℝ) ≤
      (2 : ℝ) ^ k * (G.maxRestrictedLinearForestMultiplicity E : ℝ) := by
    exact_mod_cast hnumNat
  have hposE : 0 < (2 : ℝ) ^ G.restrictedCycleRank E := by positivity
  have hposK : 0 < (2 : ℝ) ^ k := by positivity
  rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ G.cycleRank) hposE]
  rw [hpow]
  calc
    (G.maxLinearForestMultiplicity : ℝ) * (2 : ℝ) ^ G.restrictedCycleRank E ≤
        ((2 : ℝ) ^ k * (G.maxRestrictedLinearForestMultiplicity E : ℝ)) *
          (2 : ℝ) ^ G.restrictedCycleRank E :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (G.maxRestrictedLinearForestMultiplicity E : ℝ) *
          ((2 : ℝ) ^ G.restrictedCycleRank E * (2 : ℝ) ^ k) := by ring


end CapacityBridge
end Proof
end Erdos1016

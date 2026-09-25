import Erdos1016.Probability.Conditional.RegionForestProduct
import Erdos1016.Probability.Conditional.LinearImageFibers
import Erdos1016.Cleanup.Degree.LinearBadVertexBound
import Erdos1016.Probability.Cylinders.ZeroCoordinateCylinders

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.PhysicalManyRegionProbabilityBridge

open Erdos1016
open Erdos1016.Proof.PhysicalManyRegionReveal
open Erdos1016.Proof.RevealedFiberProbability
open Erdos1016.Proof.PhysicalManyRegionConditionalProduct

open Erdos1016.Proof.ManyCyclicRegionCutCylinders

local notation "𝔽" => F₂

variable (G : PhysicalGraph) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (S : ι → Finset G.Vertex)

/-- The linear map recording all coordinates that are not internal to a
packed region. -/
def outsideRevealLinear
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    G.CycleSpace →ₗ[𝔽] (OutsideEdge G S → 𝔽) where
  toFun x e := x.1 e.1
  map_add' x z := by funext e; rfl
  map_smul' a x := by funext e; rfl

noncomputable instance outsideRevealKerFintype
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    Fintype (LinearMap.ker (outsideRevealLinear G S hdisj)) :=
  Fintype.ofFinite _

theorem revealValue_eq_outsideRevealLinear
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (x : G.CycleSpace) :
    revealValue G S hdisj x = outsideRevealLinear G S hdisj x := by
  classical
  funext e
  have hpart := (edgePartition G S hdisj).right_inv (Sum.inl e)
  change edgePartition G S hdisj e.1 = Sum.inl e at hpart
  have hsymm : (edgePartition G S hdisj).symm (Sum.inl e) = e.1 :=
    (Equiv.symm_apply_eq (edgePartition G S hdisj)).2 hpart.symm
  simp [revealValue, outsideRevealLinear, splitWord,
    ManyRegionsFiberDecomposition.splitWord, hsymm]

/-- The attainable physical reveal values are exactly the range of the
outside-coordinate linear map. -/
noncomputable def revealTargetEquivRange
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    RevealTarget G S hdisj ≃ LinearMap.range (outsideRevealLinear G S hdisj) where
  toFun y := ⟨y.1, by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    rw [← revealValue_eq_outsideRevealLinear G S hdisj x]
    exact hx⟩
  invFun y := ⟨y.1, by
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    rw [revealValue_eq_outsideRevealLinear G S hdisj x]
    exact hx⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

theorem reveal_surjective
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    Function.Surjective (reveal G S hdisj) := by
  intro y
  obtain ⟨x, hx⟩ := y.2
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

theorem reveal_fiber_card
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) :
    Fintype.card (fiber (reveal G S hdisj) y) =
      Fintype.card (LinearMap.ker (outsideRevealLinear G S hdisj)) := by
  classical
  let e : fiber (reveal G S hdisj) y ≃
    fiber (Erdos1016.Proof.RangeRevealFiber.reveal
        (outsideRevealLinear G S hdisj)) (revealTargetEquivRange G S hdisj y) := {
    toFun := fun x => ⟨x.1, by
      apply Subtype.ext
      have hx : revealValue G S hdisj x.1 = y.1 :=
        congrArg Subtype.val x.2
      change outsideRevealLinear G S hdisj x.1 = y.1
      rw [← revealValue_eq_outsideRevealLinear G S hdisj x.1]
      exact hx⟩
    invFun := fun x => ⟨x.1, by
      apply Subtype.ext
      have hx : outsideRevealLinear G S hdisj x.1 = y.1 :=
        congrArg Subtype.val x.2
      change revealValue G S hdisj x.1 = y.1
      rw [revealValue_eq_outsideRevealLinear G S hdisj x.1]
      exact hx⟩
    left_inv := fun x => by apply Subtype.ext; rfl
    right_inv := fun x => by apply Subtype.ext; rfl }
  rw [Fintype.card_congr e]
  exact Erdos1016.Proof.RangeRevealFiber.fiber_card
    (outsideRevealLinear G S hdisj) (revealTargetEquivRange G S hdisj y)

def zeroCutEvent
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (x : G.CycleSpace) : Prop :=
  zeroCut G S i (revealValue G S hdisj x)

def zeroCutRevealEvent
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (y : RevealTarget G S hdisj) : Prop :=
  zeroCut G S i y.1

theorem zeroCutEvent_iff_revealed
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (x : G.CycleSpace) :
    zeroCutEvent G S hdisj i x ↔
      zeroCutRevealEvent G S hdisj i (reveal G S hdisj x) := Iff.rfl

theorem zeroCutRevealEvent_count_eq
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : RevealTarget G S hdisj) :
    eventCountNat (zeroCutRevealEvent G S hdisj) y =
      Nat.card {i : ι // zeroCut G S i y.1} := by
  classical
  unfold eventCountNat zeroCutRevealEvent
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The conditional hypothesis required by the uniform-reveal version of the
two-edge many-region estimate, derived from the physical conditional product
theorem. -/
theorem outsideForest_conditional_bound
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (E : Finset G.Edge)
    (hregionsOutside : ∀ i,
      PhysicalManyRegionConditionalProduct.regionInternalEdges G S i ⊆ Eᶜ)
    (hcyclic : ∀ i, Erdos1016.PhysicalGraph.IsCyclicRegion G (S i)) (a : ℕ) :
    ∀ y : RevealTarget G S hdisj,
      a ≤ eventCountNat (zeroCutRevealEvent G S hdisj) y →
      Finite.density
        (fun x : fiber (reveal G S hdisj) y =>
          x.1 ∈ G.outsideLinearForestStates E) ≤ (1 / 2 : ℝ) ^ a := by
  intro y hy
  have hcount := zeroCutRevealEvent_count_eq G S hdisj y
  rw [hcount] at hy
  exact outsideForest_fiber_density_le_half_pow_of_zeroCut_cyclicRegions
      G S hdisj E hregionsOutside hcyclic a y hy





/-- Integer ceiling for `log₂(4R)`: `Nat.clog` is the least exponent `a`
such that `4R ≤ 2^a`. -/
def dyadicRegionCutoffExponent (R : ℕ) : ℕ := Nat.clog 2 (4 * R)

theorem dyadicRegionCutoffExponent_pow_ge (R : ℕ) :
    4 * R ≤ 2 ^ dyadicRegionCutoffExponent R := by
  exact Nat.le_pow_clog Nat.one_lt_two (4 * R)

/-- The exponent above gives the exact tail allowance used in the paper. -/
theorem dyadicRegionCutoffExponent_tail_bound (R : ℕ) (hR : 5 ≤ R) :
    (1 / 2 : ℝ) ^ dyadicRegionCutoffExponent R ≤ 1 / (4 * (R : ℝ)) := by
  have hpowNat := dyadicRegionCutoffExponent_pow_ge R
  have hpow : (4 : ℝ) * (R : ℝ) ≤
      (2 : ℝ) ^ (dyadicRegionCutoffExponent R : ℕ) := by
    exact_mod_cast hpowNat
  have hden : (0 : ℝ) < 4 * (R : ℝ) := by positivity
  have hinv := one_div_le_one_div_of_le hden hpow
  have hrewrite : (1 / 2 : ℝ) ^ dyadicRegionCutoffExponent R =
      1 / (2 : ℝ) ^ dyadicRegionCutoffExponent R := by
    rw [div_pow]
    simp
  rw [hrewrite]
  exact hinv



/-- If all selected cut-edge coordinates vanish, then the revealed outside
boundary vanishes at every vertex of the region. Every revealed edge incident
to the region is one of the actual host cut edges. -/
theorem cutCoordinates_zero_implies_zeroCutEvent
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i : ι) (x : G.CycleSpace)
    (hcoords : ∀ e ∈ G.cutEdges (S i), x.1 e = 0) :
    zeroCutEvent G S hdisj i x := by
  classical
  intro v hv
  change G.boundary
    (G.extendOutsideWord (allRegionEdges G S)
      (revealValue G S hdisj x)) v = 0
  change (∑ e : G.Edge,
      ((if G.src e = v then
          G.extendOutsideWord (allRegionEdges G S) (revealValue G S hdisj x) e
        else 0) +
       (if G.dst e = v then
          G.extendOutsideWord (allRegionEdges G S) (revealValue G S hdisj x) e
        else 0))) = 0
  apply Finset.sum_eq_zero
  intro e _
  by_cases hregion : e ∈ allRegionEdges G S
  · simp [PhysicalGraph.extendOutsideWord, hregion]
  · have hnotInternal : e ∉ regionEdges G S i := by
        intro hi
        apply hregion
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    have hcut_of_src (hs : G.src e = v) : e ∈ G.cutEdges (S i) := by
      have hsrc : G.src e ∈ S i := hs ▸ hv
      have hdst : G.dst e ∉ S i := by
        intro hdst
        apply hnotInternal
        simp [PhysicalManyRegionReveal.regionEdges, hsrc, hdst]
      simp [PhysicalGraph.cutEdges, hsrc, hdst]
    have hcut_of_dst (ht : G.dst e = v) : e ∈ G.cutEdges (S i) := by
      have hdst : G.dst e ∈ S i := ht ▸ hv
      have hsrc : G.src e ∉ S i := by
        intro hsrc
        apply hnotInternal
        simp [PhysicalManyRegionReveal.regionEdges, hsrc, hdst]
      simp [PhysicalGraph.cutEdges, hsrc, hdst]
    have hval (hcut : e ∈ G.cutEdges (S i)) :
        revealValue G S hdisj x ⟨e, hregion⟩ = x.1 e := by
      rw [revealValue_eq_outsideRevealLinear G S hdisj]
      rfl
    by_cases hs : G.src e = v
    · have hext :
        G.extendOutsideWord (allRegionEdges G S) (revealValue G S hdisj x) e = 0 := by
        simp [PhysicalGraph.extendOutsideWord, hregion, hval (hcut_of_src hs),
          hcoords e (hcut_of_src hs)]
      simp [hs, hext]
    · by_cases ht : G.dst e = v
      · have hext :
          G.extendOutsideWord (allRegionEdges G S) (revealValue G S hdisj x) e = 0 := by
          simp [PhysicalGraph.extendOutsideWord, hregion, hval (hcut_of_dst ht),
            hcoords e (hcut_of_dst ht)]
        simp [hs, ht, hext]
      · simp [hs, ht]











end Erdos1016.Proof.PhysicalManyRegionProbabilityBridge

end

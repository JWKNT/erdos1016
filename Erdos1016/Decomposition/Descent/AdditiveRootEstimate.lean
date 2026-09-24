import Erdos1016.Decomposition.Descent.ForestDescentTree

set_option autoImplicit false

/-!
# Abstract additive root bound for finite forest descent

This packages the §9 potential bookkeeping with size and boundary data.  All
split and stopping conditions are hypotheses on the finite tree; no graph
construction or Section Ten estimate is assumed.
-/

namespace Erdos1016.Proof.AdditiveRootEstimate

noncomputable section

open Erdos1016.Proof.ForestDescentTree


local notation "B0" => (1 / 16 : ℝ)
local notation "p" => (7 / 8 : ℝ)

inductive RegionTree where
  | leaf (size boundary exterior : ℕ)
  | fork (size boundary exterior : ℕ) (left right : RegionTree)
  deriving DecidableEq

def size : RegionTree → ℕ
  | .leaf n _ _ => n
  | .fork n _ _ _ _ => n

def boundary : RegionTree → ℕ
  | .leaf _ b _ => b
  | .fork _ b _ _ _ => b

def exterior : RegionTree → ℕ
  | .leaf _ _ c => c
  | .fork _ _ c _ _ => c

noncomputable def sizePow (n : ℕ) : ℝ := Real.rpow (n : ℝ) p

def nodePotential (t : RegionTree) : ℝ :=
  (boundary t : ℝ) - B0 * sizePow (size t)

/-- The sign tree is the §9 signed-credit tree: its leaves are marked exactly
when the real deficit potential is negative. -/
def signTree : RegionTree → ForestDescentTree.SplitTree
  | .leaf n b c =>
      .leaf (if nodePotential (.leaf n b c) < 0 then -1 else 0) c
  | .fork n b c l r =>
      .fork (if nodePotential (.fork n b c l r) < 0 then -1 else 0) c
        (signTree l) (signTree r)

def hasNegativeLeaf : RegionTree → Bool
  | .leaf n b c => decide (nodePotential (.leaf n b c) < 0)
  | .fork _ _ _ l r => hasNegativeLeaf l || hasNegativeLeaf r

/-- Local assumptions are exactly the potential split estimate, the exterior
split estimate, and the two one-retained-child monotonicity cases. -/
def LocallyValid : RegionTree → Prop
  | .leaf _ _ _ => True
  | .fork n b c l r =>
      LocallyValid l ∧ LocallyValid r ∧
      nodePotential l + nodePotential r ≤ nodePotential (.fork n b c l r) ∧
      exterior l + exterior r ≤ c + 2 ∧
      ((hasNegativeLeaf l = true ∧ hasNegativeLeaf r = false) → exterior l ≤ c) ∧
      ((hasNegativeLeaf l = false ∧ hasNegativeLeaf r = true) → exterior r ≤ c)

theorem signTree_hasNegativeLeaf (t : RegionTree) :
    ForestDescentTree.hasNegativeLeaf (signTree t) = hasNegativeLeaf t := by
  induction t with
  | leaf n b c =>
      change decide ((if nodePotential (.leaf n b c) < 0 then (-1 : ℤ) else 0) < 0) =
        decide (nodePotential (.leaf n b c) < 0)
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;> simp [hneg]
  | fork n b c l r ihl ihr =>
      simp [signTree, hasNegativeLeaf, ihl, ihr,
        ForestDescentTree.hasNegativeLeaf]

theorem signTree_locallyValid (t : RegionTree) (h : LocallyValid t) :
    ForestDescentTree.LocallyValid (signTree t) := by
  induction t with
  | leaf n b c => trivial
  | fork n b c l r ihl ihr =>
      rcases h with ⟨hl, hr, hp, hc, hleft, hright⟩
      have hvl := ihl hl
      have hvr := ihr hr
      have hsign :
          (if nodePotential l < 0 then (-1 : ℤ) else 0) +
            (if nodePotential r < 0 then (-1 : ℤ) else 0) ≤
          (if nodePotential (.fork n b c l r) < 0 then (-1 : ℤ) else 0) := by
        by_cases hpl : nodePotential l < 0 <;>
          by_cases hpr : nodePotential r < 0 <;>
          by_cases hpp : nodePotential (.fork n b c l r) < 0
        all_goals
          simp [hpl, hpr, hpp]
          <;> linarith [hp]
      have hpotProjection (u : RegionTree) :
          ForestDescentTree.potential (signTree u) =
            (if nodePotential u < 0 then (-1 : ℤ) else 0) := by
        cases u <;> rfl
      have hextProjection (u : RegionTree) :
          ForestDescentTree.exterior (signTree u) = exterior u := by
        cases u <;> rfl
      have hsumSigns :
          ForestDescentTree.potential (signTree l) +
            ForestDescentTree.potential (signTree r) ≤
          ForestDescentTree.potential (signTree (.fork n b c l r)) := by
        simpa only [hpotProjection] using hsign
      refine ⟨hvl, hvr, hsumSigns, ?_, ?_, ?_⟩
      · simpa only [hextProjection] using hc
      · intro hpairs
        have hpairs' : hasNegativeLeaf l = true ∧ hasNegativeLeaf r = false := by
          simpa [signTree_hasNegativeLeaf] using hpairs
        simpa only [hextProjection] using hleft hpairs'
      · intro hpairs
        have hpairs' : hasNegativeLeaf l = false ∧ hasNegativeLeaf r = true := by
          simpa [signTree_hasNegativeLeaf] using hpairs
        simpa only [hextProjection] using hright hpairs'

def leafPotentialSum : RegionTree → ℝ
  | .leaf n b c => nodePotential (.leaf n b c)
  | .fork _ _ _ l r => leafPotentialSum l + leafPotentialSum r

theorem leafPotentialSum_le_root (t : RegionTree) (h : LocallyValid t) :
    leafPotentialSum t ≤ nodePotential t := by
  induction t with
  | leaf n b c => simp [leafPotentialSum, nodePotential]
  | fork n b c l r ihl ihr =>
      rcases h with ⟨hl, hr, hp, _, _, _⟩
      change leafPotentialSum l + leafPotentialSum r ≤ nodePotential (.fork n b c l r)
      exact (add_le_add (ihl hl) (ihr hr)).trans hp


def negativeLeafCount : RegionTree → ℕ
  | .leaf n b c => if nodePotential (.leaf n b c) < 0 then 1 else 0
  | .fork _ _ _ l r => negativeLeafCount l + negativeLeafCount r

def smallNegativeLeafCount : RegionTree → ℕ
  | .leaf n b c => if nodePotential (.leaf n b c) < 0 ∧ c ≤ 2 then 1 else 0
  | .fork _ _ _ l r => smallNegativeLeafCount l + smallNegativeLeafCount r

def largeNegativeLeafCount : RegionTree → ℕ
  | .leaf n b c => if nodePotential (.leaf n b c) < 0 ∧ 2 < c then 1 else 0
  | .fork _ _ _ l r => largeNegativeLeafCount l + largeNegativeLeafCount r

def smallNegativeCredit : RegionTree → ℤ
  | .leaf n b c =>
      if nodePotential (.leaf n b c) < 0 ∧ c ≤ 2 then (c : ℤ) - 2 else 0
  | .fork _ _ _ l r => smallNegativeCredit l + smallNegativeCredit r

def largeNegativeCredit : RegionTree → ℤ
  | .leaf n b c =>
      if nodePotential (.leaf n b c) < 0 ∧ 2 < c then (c : ℤ) - 2 else 0
  | .fork _ _ _ l r => largeNegativeCredit l + largeNegativeCredit r



def largeNegativeExteriorMax : RegionTree → ℕ
  | .leaf n b c =>
      if nodePotential (.leaf n b c) < 0 ∧ 2 < c then c else 0
  | .fork _ _ _ l r => max (largeNegativeExteriorMax l) (largeNegativeExteriorMax r)

def negativeExteriorMax : RegionTree → ℕ
  | .leaf n b c => if nodePotential (.leaf n b c) < 0 then c else 0
  | .fork _ _ _ l r => max (negativeExteriorMax l) (negativeExteriorMax r)

def negativePotentialSum : RegionTree → ℝ
  | .leaf n b c =>
      if nodePotential (.leaf n b c) < 0 then nodePotential (.leaf n b c) else 0
  | .fork _ _ _ l r => negativePotentialSum l + negativePotentialSum r

def NegativeLeavesStop (T0 : ℕ → ℕ) : RegionTree → Prop
  | .leaf n b c =>
      nodePotential (.leaf n b c) < 0 → n < T0 c
  | .fork _ _ _ l r => NegativeLeavesStop T0 l ∧ NegativeLeavesStop T0 r

def LeafExteriorsPositive : RegionTree → Prop
  | .leaf _ _ c => 1 ≤ c
  | .fork _ _ _ l r => LeafExteriorsPositive l ∧ LeafExteriorsPositive r

theorem signTree_credit_eq_split (t : RegionTree) :
    ForestDescentTree.negativeCredit (signTree t) =
      smallNegativeCredit t + largeNegativeCredit t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0
      · by_cases hsmall : c ≤ 2
        · simp [signTree, ForestDescentTree.negativeCredit,
            ForestDescentTree.potential, smallNegativeCredit,
            largeNegativeCredit, hneg, hsmall]
        · have hlarge : 2 < c := by omega
          simp [signTree, ForestDescentTree.negativeCredit,
            ForestDescentTree.potential, smallNegativeCredit,
            largeNegativeCredit, hneg, hsmall, hlarge]
      · simp [signTree, ForestDescentTree.negativeCredit,
          ForestDescentTree.potential, smallNegativeCredit,
          largeNegativeCredit, hneg]
  | fork n b c l r ihl ihr =>
      simp [signTree, ForestDescentTree.negativeCredit,
        smallNegativeCredit, largeNegativeCredit, ihl, ihr] <;> ring

theorem negative_count_eq_small_add_large (t : RegionTree) :
    negativeLeafCount t = smallNegativeLeafCount t + largeNegativeLeafCount t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0
      · by_cases hsmall : c ≤ 2
        · simp [negativeLeafCount, smallNegativeLeafCount, largeNegativeLeafCount, hneg, hsmall]
        · have hlarge : 2 < c := by omega
          simp [negativeLeafCount, smallNegativeLeafCount, largeNegativeLeafCount,
            hneg, hsmall, hlarge]
      · simp [negativeLeafCount, smallNegativeLeafCount, largeNegativeLeafCount, hneg]
  | fork n b c l r ihl ihr =>
      simp [negativeLeafCount, smallNegativeLeafCount, largeNegativeLeafCount, ihl, ihr]
      <;> omega

theorem small_credit_lower (t : RegionTree) (hpos : LeafExteriorsPositive t) :
    -(smallNegativeLeafCount t : ℤ) ≤ smallNegativeCredit t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        by_cases hsmall : c ≤ 2 <;>
        simp [smallNegativeCredit, smallNegativeLeafCount, hneg, hsmall]
      all_goals
        have hc : 1 ≤ c := hpos
        norm_num at * <;> omega
  | fork n b c l r ihl ihr =>
      rcases hpos with ⟨hl, hr⟩
      simp only [smallNegativeLeafCount, smallNegativeCredit]
      have h := add_le_add (ihl hl) (ihr hr)
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

theorem large_credit_lower (t : RegionTree) :
    (largeNegativeLeafCount t : ℤ) ≤ largeNegativeCredit t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        by_cases hlarge : 2 < c <;>
        simp [largeNegativeLeafCount, largeNegativeCredit, hneg, hlarge]
      all_goals norm_num <;> omega
  | fork n b c l r ihl ihr =>
      simp only [largeNegativeLeafCount, largeNegativeCredit, Nat.cast_add]
      exact add_le_add ihl ihr

theorem large_credit_nonneg (t : RegionTree) : 0 ≤ largeNegativeCredit t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        by_cases hlarge : 2 < c <;>
        simp [largeNegativeCredit, hneg, hlarge] <;> omega
  | fork n b c l r ihl ihr =>
      simp [largeNegativeCredit]
      omega



theorem large_exterior_max_le_credit_add_two (t : RegionTree) :
    (largeNegativeExteriorMax t : ℤ) ≤ largeNegativeCredit t + 2 := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        by_cases hlarge : 2 < c <;>
        simp [largeNegativeExteriorMax, largeNegativeCredit, hneg, hlarge] <;> omega
  | fork n b c l r ihl ihr =>
      have hnl := large_credit_nonneg l
      have hnr := large_credit_nonneg r
      simp only [largeNegativeExteriorMax, largeNegativeCredit, Nat.cast_max]
      apply max_le_iff.mpr
      constructor <;> omega

theorem negative_exterior_le_two_or_large_max (t : RegionTree) :
    negativeExteriorMax t ≤ max 2 (largeNegativeExteriorMax t) := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        by_cases hlarge : 2 < c <;>
        simp [negativeExteriorMax, largeNegativeExteriorMax, hneg, hlarge] <;> omega
  | fork n b c l r ihl ihr =>
      simp only [negativeExteriorMax, largeNegativeExteriorMax] at *
      apply max_le_iff.mpr
      constructor
      · exact ihl.trans (max_le_max le_rfl (le_max_left _ _))
      · exact ihr.trans (max_le_max le_rfl (le_max_right _ _))

theorem negative_count_and_max_exterior (t : RegionTree) (M : ℕ)
    (h : LocallyValid t) (hnegative : hasNegativeLeaf t = true)
    (hsmall : smallNegativeLeafCount t ≤ M)
    (hpositive : LeafExteriorsPositive t) (hrootExterior : 1 ≤ exterior t)
    (hM : 1 ≤ M) :
    negativeLeafCount t ≤ exterior t + 2 * M ∧
      negativeExteriorMax t ≤ exterior t + M := by
  have hcredit := negative_credit_le_root (signTree t)
    (signTree_locallyValid t h) (by simpa [signTree_hasNegativeLeaf] using hnegative)
  rw [signTree_credit_eq_split] at hcredit
  have hExt : ForestDescentTree.exterior (signTree t) = exterior t := by
    cases t <;> rfl
  rw [hExt] at hcredit
  have hsmallCredit := small_credit_lower t hpositive
  have hlargeUpper : largeNegativeCredit t ≤ (exterior t : ℤ) - 2 + M := by
    have hM : (smallNegativeLeafCount t : ℤ) ≤ M := by exact_mod_cast hsmall
    linarith
  have hlargeCount : (largeNegativeLeafCount t : ℤ) ≤
      (exterior t : ℤ) - 2 + M := (large_credit_lower t).trans hlargeUpper
  have hcountCast : (negativeLeafCount t : ℤ) ≤
      (exterior t : ℤ) + 2 * M := by
    rw [negative_count_eq_small_add_large]
    have hsmallCast : (smallNegativeLeafCount t : ℤ) ≤ M := by exact_mod_cast hsmall
    omega
  have hmaxExtLarge : largeNegativeExteriorMax t ≤ exterior t + M := by
    have h := large_exterior_max_le_credit_add_two t
    omega
  have hmaxExt : negativeExteriorMax t ≤ exterior t + M := by
    have h := negative_exterior_le_two_or_large_max t
    have harg : 2 ≤ exterior t + M := by omega
    exact h.trans (max_le_iff.mpr ⟨harg, hmaxExtLarge⟩)
  refine ⟨by exact_mod_cast hcountCast, ?_⟩
  exact hmaxExt

theorem negativePotentialSum_le_leafPotentialSum (t : RegionTree) :
    negativePotentialSum t ≤ leafPotentialSum t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0 <;>
        simp [negativePotentialSum, leafPotentialSum, hneg] <;> linarith
  | fork n b c l r ihl ihr =>
      simp [negativePotentialSum, leafPotentialSum]
      linarith

theorem negativePotentialSum_lower (t : RegionTree) (T0 : ℕ → ℕ) (C : ℕ)
    (hstop : NegativeLeavesStop T0 t)
    (hExterior : negativeExteriorMax t ≤ C)
    (hTmono : Monotone T0) (hPowMono : Monotone sizePow)
    (hPowNonneg : ∀ n, 0 ≤ sizePow n) :
    -B0 * sizePow (T0 C) * (negativeLeafCount t : ℝ) ≤ negativePotentialSum t := by
  induction t with
  | leaf n b c =>
      by_cases hneg : nodePotential (.leaf n b c) < 0
      · have hsize := hstop hneg
        have hc : c ≤ C := by simpa [negativeExteriorMax, hneg] using hExterior
        have hT : T0 c ≤ T0 C := hTmono hc
        have hsize' : n ≤ T0 C := (Nat.le_of_lt hsize).trans hT
        have hcomp : sizePow n ≤ sizePow (T0 C) := hPowMono hsize'
        have hb : 0 ≤ (b : ℝ) := by positivity
        have hB : 0 ≤ B0 := by norm_num
        have hscaled : B0 * sizePow n ≤ B0 * sizePow (T0 C) :=
          mul_le_mul_of_nonneg_left hcomp hB
        have hpot : -B0 * sizePow n ≤ nodePotential (.leaf n b c) := by
          change -B0 * sizePow n ≤ (b : ℝ) - B0 * sizePow n
          linarith
        have hgoal : -B0 * sizePow (T0 C) ≤ nodePotential (.leaf n b c) := by
          linarith
        simpa [negativePotentialSum, negativeLeafCount, hneg] using hgoal
      · simp [negativePotentialSum, negativeLeafCount, hneg]
  | fork n b c l r ihl ihr =>
      rcases hstop with ⟨hl, hr⟩
      have hLext : negativeExteriorMax l ≤ C := (max_le_iff.mp hExterior).1
      have hRext : negativeExteriorMax r ≤ C := (max_le_iff.mp hExterior).2
      have hL := ihl hl hLext
      have hR := ihr hr hRext
      simp only [negativeLeafCount, negativePotentialSum, Nat.cast_add]
      linarith

/-- The additive root inequality from §9. The hypotheses are the local split
facts, the stopping-size estimate on negative leaves, and the finite count of
small-exterior negative leaves. `T0` and the size power need only be monotone;
the statement is real-valued to avoid irrelevant casts. -/
theorem general_root_additive_inequality
    (t : RegionTree) (M : ℕ) (T0 : ℕ → ℕ)
    (hvalid : LocallyValid t)
    (hnegative : hasNegativeLeaf t = true)
    (hsmall : smallNegativeLeafCount t ≤ M)
    (hleafExteriorPositive : LeafExteriorsPositive t)
    (hrootExteriorPositive : 1 ≤ exterior t)
    (hMpositive : 1 ≤ M)
    (hstop : NegativeLeavesStop T0 t)
    (hTmono : Monotone T0)
    (hPowMono : Monotone sizePow)
    (hPowNonneg : ∀ n, 0 ≤ sizePow n) :
    sizePow (size t) ≤ (boundary t : ℝ) / B0 +
      (exterior t + 2 * M : ℝ) * sizePow (T0 (exterior t + M)) := by
  have hcounts := negative_count_and_max_exterior t M hvalid hnegative hsmall
    hleafExteriorPositive hrootExteriorPositive hMpositive
  have hcountCast : (negativeLeafCount t : ℝ) ≤ (exterior t + 2 * M : ℝ) := by
    exact_mod_cast hcounts.1
  let C := exterior t + M
  have hnegLower := negativePotentialSum_lower t T0 C hstop hcounts.2
    hTmono hPowMono hPowNonneg
  have hsumUpper := leafPotentialSum_le_root t hvalid
  have hnegUpper := negativePotentialSum_le_leafPotentialSum t
  have hB : 0 < B0 := by norm_num
  have hK : 0 ≤ sizePow (T0 C) := hPowNonneg _
  have hcoeffNonpos : -B0 * sizePow (T0 C) ≤ 0 := by
    have hprod : 0 ≤ B0 * sizePow (T0 C) := mul_nonneg hB.le hK
    linarith
  have hscaledCount :
      -B0 * sizePow (T0 C) * (exterior t + 2 * M : ℝ) ≤
        -B0 * sizePow (T0 C) * (negativeLeafCount t : ℝ) :=
    mul_le_mul_of_nonpos_left hcountCast hcoeffNonpos
  have hrootPotential :
      -B0 * sizePow (T0 C) * (exterior t + 2 * M : ℝ) ≤
        (boundary t : ℝ) - B0 * sizePow (size t) := by
    calc
      _ ≤ negativePotentialSum t := hscaledCount.trans hnegLower
      _ ≤ leafPotentialSum t := hnegUpper
      _ ≤ nodePotential t := hsumUpper
      _ = _ := rfl
  have hmultiplied :
      B0 * sizePow (size t) ≤ (boundary t : ℝ) +
        B0 * ((exterior t + 2 * M : ℕ) : ℝ) * sizePow (T0 C) := by
    calc
      B0 * sizePow (size t) ≤
          (boundary t : ℝ) + B0 * sizePow (T0 C) * (exterior t + 2 * M : ℝ) := by
        nlinarith [hrootPotential]
      _ = (boundary t : ℝ) +
          B0 * ((exterior t + 2 * M : ℕ) : ℝ) * sizePow (T0 C) := by
        push_cast
        norm_num
        ring
  have hdiv :
      sizePow (size t) ≤ (boundary t : ℝ) / B0 +
        ((exterior t + 2 * M : ℕ) : ℝ) * sizePow (T0 C) := by
    norm_num at hmultiplied ⊢
    nlinarith [hmultiplied]
  simpa [C] using hdiv

end

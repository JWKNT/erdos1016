import Erdos1016.Extremal.Capacity.LinearForestCapacity

set_option autoImplicit false

/-!
# Finite arithmetic core of the numerical composition inequality

This module proves only the finite sum and normalization calculation. It is
not yet instantiated by an actual graph partition or the corresponding
boundary fibers.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.Capacity

/-- The set of sums of one element from each finite set. -/
def naturalSumset (A B : Finset ℕ) : Finset ℕ :=
  (A.product B).image fun p => p.1 + p.2

/-- A sumset cannot have more elements than the pairs that generate it. -/
theorem card_naturalSumset_le (A B : Finset ℕ) :
    (naturalSumset A B).card ≤ A.card * B.card := by
  unfold naturalSumset
  calc
    ((A.product B).image (fun p => p.1 + p.2)).card ≤ (A.product B).card :=
      Finset.card_image_le
    _ = A.card * B.card := by simp

/-- The union of the length-sum sets over demands is bounded by the sum of
the products of the two local multiplicities. -/
theorem card_biUnion_naturalSumsets_le {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (A B : ι → Finset ℕ) :
    (U.biUnion fun t => naturalSumset (A t) (B t)).card ≤
      ∑ t ∈ U, (A t).card * (B t).card := by
  calc
    (U.biUnion fun t => naturalSumset (A t) (B t)).card ≤
        ∑ t ∈ U, (naturalSumset (A t) (B t)).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ U, (A t).card * (B t).card := by
      apply Finset.sum_le_sum
      intro t ht
      exact card_naturalSumset_le (A t) (B t)

/-- Arithmetic form of the numerical composition step. `U` is the finite
index set of nonzero demands. The graph-specific rank split, pure-side cycle
counts, and per-demand local-capacity estimates are explicit hypotheses. -/
theorem normalized_finite_composition
    {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (r rA rM d : ℕ)
    (pureA pureM : ℕ) (μA μM : ι → ℕ) (a : ℝ)
    (hrank : r = rA + rM + d)
    (hpureA : pureA ≤ 2 ^ rA - 1)
    (hpureM : pureM ≤ 2 ^ rM - 1)
    (hμA : ∀ t ∈ U, (μA t : ℝ) ≤ (2 : ℝ) ^ rA * a) :
    ((pureA : ℝ) + pureM +
        ∑ t ∈ U, (μA t : ℝ) * (μM t : ℝ)) / (2 : ℝ) ^ r ≤
      a * (∑ t ∈ U, (μM t : ℝ)) / (2 : ℝ) ^ (rM + d) +
        1 / (2 : ℝ) ^ (rM + d) + 1 / (2 : ℝ) ^ (rA + d) := by
  let pA : ℝ := (2 : ℝ) ^ rA
  let pM : ℝ := (2 : ℝ) ^ rM
  let pD : ℝ := (2 : ℝ) ^ d
  let S : ℝ := ∑ t ∈ U, (μM t : ℝ)
  have hpApos : 0 < pA := by positivity
  have hpMpos : 0 < pM := by positivity
  have hpDpos : 0 < pD := by positivity
  have hrank' : r = rA + (rM + d) := by omega
  have hden : (2 : ℝ) ^ r = pA * pM * pD := by
    rw [hrank']
    simp [pA, pM, pD, pow_add, mul_assoc]
  have hdenM : (2 : ℝ) ^ (rM + d) = pM * pD := by
    simp [pM, pD, pow_add]
  have hdenA : (2 : ℝ) ^ (rA + d) = pA * pD := by
    simp [pA, pD, pow_add]
  have hpowA : 1 ≤ 2 ^ rA := Nat.one_le_pow rA 2 (by decide)
  have hpowM : 1 ≤ 2 ^ rM := Nat.one_le_pow rM 2 (by decide)
  have hpureA' : pureA + 1 ≤ 2 ^ rA := by omega
  have hpureM' : pureM + 1 ≤ 2 ^ rM := by omega
  have hpureA_cast : ((pureA + 1 : ℕ) : ℝ) ≤ ((2 ^ rA : ℕ) : ℝ) := by
    exact_mod_cast hpureA'
  have hpureM_cast : ((pureM + 1 : ℕ) : ℝ) ≤ ((2 ^ rM : ℕ) : ℝ) := by
    exact_mod_cast hpureM'
  have hpureA_real : (pureA : ℝ) + 1 ≤ pA := by
    simpa [pA, Nat.cast_add, Nat.cast_one] using hpureA_cast
  have hpureM_real : (pureM : ℝ) + 1 ≤ pM := by
    simpa [pM, Nat.cast_add, Nat.cast_one] using hpureM_cast
  have hsumPure : (pureA : ℝ) + pureM ≤ pA + pM := by
    dsimp [pA, pM] at hpureA_real hpureM_real ⊢
    linarith
  have hsumμ : (∑ t ∈ U, (μA t : ℝ) * (μM t : ℝ)) ≤ pA * a * S := by
    calc
      (∑ t ∈ U, (μA t : ℝ) * (μM t : ℝ)) ≤
          ∑ t ∈ U, (pA * a) * (μM t : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have hμ := hμA t ht
        have hnonneg : 0 ≤ (μM t : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right hμ hnonneg
      _ = (pA * a) * S := by
        simp [S, Finset.mul_sum]
  have hnum : (pureA : ℝ) + pureM +
      ∑ t ∈ U, (μA t : ℝ) * (μM t : ℝ) ≤ pA * a * S + pA + pM := by
    calc
      _ ≤ pA + pM + pA * a * S := add_le_add hsumPure hsumμ
      _ = pA * a * S + pA + pM := by ring
  have hrhs :
      a * S / (2 : ℝ) ^ (rM + d) +
        1 / (2 : ℝ) ^ (rM + d) + 1 / (2 : ℝ) ^ (rA + d) =
      (pA * a * S + pA + pM) / (pA * pM * pD) := by
    rw [hdenM, hdenA]
    simp only [S]
    field_simp [ne_of_gt hpApos, ne_of_gt hpMpos, ne_of_gt hpDpos]
    ring
  calc
    _ ≤ (pA * a * S + pA + pM) / (2 : ℝ) ^ r :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by rw [hden, hrhs]

end Erdos1016.Capacity

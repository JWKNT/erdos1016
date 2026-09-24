import Erdos1016.Nonbacktracking.Trace.EvenTraceSum
import Erdos1016.Nonbacktracking.Trace.ClosedRunNormalization

set_option autoImplicit false

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.EvenHarmonicMass

open scoped BigOperators
open Erdos1016.Nonbacktracking

local instance traceBridgeDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The even normalized matrix-trace terms are a sub-sum of the literal
nonbacktracking trace mass. This is the finite interface needed to turn the
proved even-trace lower bound into divergence of the Section 6 trace supply. -/
theorem normalized_even_terms_le_traceMass
    (G : Erdos1016.PhysicalGraph) (M K : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.Icc M K,
      (Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) /
        (2 : ℝ) ^ (2 * k)) / (4 * (k : ℝ))) ≤
      nonbacktrackingTraceMass (G := G) (2 * K) := by
  classical
  let E := (Finset.Icc M K).image (fun k => 2 * k)
  let w : ℕ → ℝ := fun ell =>
    (closedRunCount G ell : ℝ) /
      ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)
  have hinj : ∀ a ∈ Finset.Icc M K, ∀ b ∈ Finset.Icc M K,
      2 * a = 2 * b → a = b := by
    intro a ha b hb hab
    omega
  have hsum :
      (∑ k ∈ Finset.Icc M K,
        (Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) /
          (2 : ℝ) ^ (2 * k)) / (4 * (k : ℝ))) =
      ∑ ell ∈ E, w ell := by
    calc
      _ = ∑ k ∈ Finset.Icc M K, w (2 * k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < k := hM.trans_le (Finset.mem_Icc.mp hk).1
        rw [trace_pow_eq_closedRunCount]
        have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
        change (closedRunCount G (2 * k) : ℝ) /
            (2 : ℝ) ^ (2 * k) / (4 * (k : ℝ)) =
          (closedRunCount G (2 * k) : ℝ) /
            (2 * ((2 * k : ℕ) : ℝ) * (2 : ℝ) ^ (2 * k))
        push_cast
        have hden₁ : (4 * (k : ℝ)) ≠ 0 := ne_of_gt (by positivity)
        have hden₂ : (2 * (2 * (k : ℝ)) * (2 : ℝ) ^ (2 * k)) ≠ 0 :=
          ne_of_gt (by positivity)
        field_simp [hden₁, hden₂]
        left
        ring
      _ = ∑ ell ∈ E, w ell := by
        dsimp [E]
        symm
        rw [Finset.sum_image (fun a ha b hb hab => hinj a ha b hb hab)]
  rw [hsum]
  unfold nonbacktrackingTraceMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ell hell
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hell
    have hkIcc := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro ell hell hnot
    dsimp [w]
    positivity



/-- Explicit per-interval estimate for the normalized even-trace lower sum.
The degree-two exponent keeps its main term at least 1/2, and the edge term
is at most 1/4. Thus each summand contributes at least 1/(16k). -/
theorem normalized_even_trace_lower_sum_ge_reciprocal_interval
    (G : Erdos1016.PhysicalGraph) (M K : ℕ)
    (hM : 0 < M) (hn : 0 < G.vertexCount)
    (hmain : (degreeTwoCount G : ℝ) * (2 * (K : ℝ)) /
        G.vertexCount ≤ 1)
    (herr : 2 * (G.edgeCount : ℝ) *
        (2 : ℝ) ^ (-(M : ℝ)) ≤ 1 / 4) :
    (1 / 16 : ℝ) *
        (∑ k ∈ Finset.Icc M K, (1 : ℝ) / (k : ℝ)) ≤
      ∑ k ∈ Finset.Icc M K,
        ((2 : ℝ) ^ (-(degreeTwoCount G : ℝ) *
            (2 * (k : ℝ)) / G.vertexCount) -
          2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ))) /
            (4 * (k : ℝ)) := by
  have hnR : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := hM.trans_le (Finset.mem_Icc.mp hk).1
  have hkupper : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hdegreeNonneg : 0 ≤ (degreeTwoCount G : ℝ) := by positivity
  have hexponent : (degreeTwoCount G : ℝ) * (2 * (k : ℝ)) /
      G.vertexCount ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left
      (show 2 * (k : ℝ) ≤ 2 * (K : ℝ) by exact_mod_cast Nat.mul_le_mul_left 2 hkupper)
      hdegreeNonneg
    have hmain' : (degreeTwoCount G : ℝ) * (2 * (K : ℝ)) ≤
        G.vertexCount := by
      simpa only [one_mul] using (div_le_iff₀ hnR).1 hmain
    exact (div_le_one hnR).2 (hmul.trans hmain')
  have hmainTerm : (1 / 2 : ℝ) ≤
      (2 : ℝ) ^ (-(degreeTwoCount G : ℝ) *
        (2 * (k : ℝ)) / G.vertexCount) := by
    have hexpLow : (-1 : ℝ) ≤
        -(degreeTwoCount G : ℝ) * (2 * (k : ℝ)) / G.vertexCount := by
      calc
        (-1 : ℝ) ≤ -((degreeTwoCount G : ℝ) *
            (2 * (k : ℝ)) / G.vertexCount) := neg_le_neg hexponent
        _ = -(degreeTwoCount G : ℝ) *
            (2 * (k : ℝ)) / G.vertexCount := by ring
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLow
  have hpowMono : (2 : ℝ) ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-(M : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact_mod_cast (neg_le_neg (show (M : ℝ) ≤ k by exact_mod_cast (Finset.mem_Icc.mp hk).1))
  have herrK : 2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hpowMono (by positivity)).trans herr
  have hnumerator : (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (-(degreeTwoCount G : ℝ) *
          (2 * (k : ℝ)) / G.vertexCount) -
        2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
    linarith
  have hden : 0 < 4 * (k : ℝ) := by positivity
  have hterm : (1 / 16 : ℝ) * (1 / (k : ℝ)) ≤
      ((2 : ℝ) ^ (-(degreeTwoCount G : ℝ) *
          (2 * (k : ℝ)) / G.vertexCount) -
        2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ))) /
          (4 * (k : ℝ)) := by
    calc
      (1 / 16 : ℝ) * (1 / (k : ℝ)) = (1 / 4) / (4 * (k : ℝ)) := by
        field_simp [ne_of_gt hkpos]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hnumerator hden.le
  simpa [div_eq_mul_inv, one_div, mul_assoc] using hterm



end Erdos1016.Proof.EvenHarmonicMass
end

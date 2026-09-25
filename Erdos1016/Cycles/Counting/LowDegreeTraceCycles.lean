import Erdos1016.Nonbacktracking.Spectrum.DeficitTrace
import Erdos1016.Cycles.Counting.TraceCycleMass
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

/-! Quantitative cycle-weight supply in subcubic graphs of high girth.
The graph may be disconnected and have degree-zero or degree-one vertices.
All small-error hypotheses below are explicit finite numerical inequalities. -/
noncomputable section
namespace Erdos1016.Proof.LowDegreeTraceCycles
open scoped BigOperators
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.SimpleRunWeight

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



/-- Integrating 1/x on a positive interval bounds its reciprocal sum. -/
theorem log_ratio_le_reciprocal_sum (M K : ℕ) (hM : 0 < M) (hMK : M ≤ K + 1) :
    Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      ∑ k ∈ Finset.Icc M K, (1 : ℝ) / k := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have h := (inv_antitoneOn_Icc_right hMR).integral_le_sum_Ico hMK
  have hnot : (0 : ℝ) ∉ Set.uIcc (M : ℝ) ((K + 1 : ℕ) : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hMK)]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hMR)
  rw [integral_inv hnot] at h
  simpa only [one_div, Nat.Ico_succ_right] using h

/-- Each normalized even trace in the interval is at least one half when
 the total deficit loss is at most one quarter and the spectral error is
 at most one quarter. -/
theorem traceMass_ge_reciprocal_sum (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount)
    (M K : ℕ) (hM : 0 < M)
    (hmain : degreeDeficit G * (K : ℝ) / G.vertexCount ≤ 1 / 4)
    (herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 4) :
    (1 / 8 : ℝ) * (∑ k ∈ Finset.Icc M K, (1 : ℝ) / k) ≤
      nonbacktrackingTraceMass (G := G) (2 * K) := by
  have hnR : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hd0 := degreeDeficit_nonneg G hmax
  have hδ : degreeDeficit G / (2 * G.vertexCount) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * G.vertexCount)).mpr
    nlinarith
  apply le_trans ?_ (normalized_even_terms_le_traceMass G M K hM)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := hM.trans_le (Finset.mem_Icc.mp hk).1
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hMk : M ≤ k := (Finset.mem_Icc.mp hk).1
  have hbern := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ -(degreeDeficit G / (2 * G.vertexCount)) by linarith) (2 * k)
  have hbudget : degreeDeficit G * (k : ℝ) / G.vertexCount ≤ 1 / 4 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hd0) hnR.le).trans hmain
  have hlead : (3 / 4 : ℝ) ≤
      (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) := by
    push_cast at hbern
    have heq : 1 + (2 * (k : ℝ)) * -(degreeDeficit G / (2 * G.vertexCount)) =
        1 - degreeDeficit G * (k : ℝ) / G.vertexCount := by ring
    rw [heq] at hbern
    change _ ≤ (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) at hbern
    linarith
  have herrk : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ k ≤ 1 / 4 := by
    apply le_trans ?_ herr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hMk
  have htrace := DeficitTrace.normalized_even_trace_lower G hmax hn hd k hkpos
  have hhalf : (1 / 2 : ℝ) ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) / (2 : ℝ) ^ (2 * k) := by
    linarith
  calc
    (1 / 8 : ℝ) * (1 / (k : ℝ)) = (1 / 2 : ℝ) / (4 * k) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hhalf (by positivity)

/-- Full simple-cycle weight is bounded below by a logarithmic interval
 of actual even traces. The collision estimate uses the same graph and
 requires no minimum-degree hypothesis. -/
theorem cycleWordMass_ge_log_ratio (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount)
    (M K s D : ℕ) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hmain : degreeDeficit G * (K : ℝ) / G.vertexCount ≤ 1 / 4)
    (herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 4)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (hcollision : (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 2) :
    (1 / 16 : ℝ) * Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength G ell := by
  have hlog := log_ratio_le_reciprocal_sum M K hM hMK
  have htrace := traceMass_ge_reciprocal_sum G hmax hn hd M K hM hmain herr
  have hcycle := TraceCycleMass.cycleWordMass_sum_ge_one_sub_collisionError_of_max_degree
    G (2 * K) s D hmax hg hshort hs
  have hmass0 : 0 ≤ nonbacktrackingTraceMass (G := G) (2 * K) := by
    unfold nonbacktrackingTraceMass
    positivity
  have hhalf : (1 / 2 : ℝ) * nonbacktrackingTraceMass (G := G) (2 * K) ≤
      ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength G ell := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 / 2 : ℝ) ≤ 1 - (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ s by linarith) hmass0
    exact h.trans hcycle
  linarith

end Erdos1016.Proof.LowDegreeTraceCycles

import Erdos1016.Nonbacktracking.Spectrum.AlgebraicTrace

set_option autoImplicit false

/-!
# The unconditional even nonbacktracking trace estimate

Source Lemma 5.1 for the actual graph, disconnected graphs included.
For high entropy we use the real maximizing eigenvalue (not a supplied
positive Perron vector). For low entropy the claimed right hand side is
nonpositive, so the literal nonnegative walk count proves it directly.
The trace is never evaluated on the high-degree boundary apex graph.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
local instance evenTraceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- Source (5.1), before division by 2^(2*k). There is no spectral witness,
algebraic eigenvalue list, or high-entropy condition among the hypotheses. -/
theorem actual_even_trace_lower
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (k : ℕ) (hk : 0 < k) :
    ((2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)) ^ (2 * k) -
      2 * (G.edgeCount : ℝ) * 2 ^ k ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) := by
  by_cases hb : 2 * degreeTwoCount G < G.vertexCount
  · exact actual_even_trace_lower_high_entropy G hmin hmax hn hb k hk
  · have hn' : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
    have hb' : (G.vertexCount : ℝ) ≤ 2 * degreeTwoCount G := by
      exact_mod_cast (Nat.le_of_not_gt hb)
    have hfrac : (1 / 2 : ℝ) ≤ (degreeTwoCount G : ℝ) / G.vertexCount := by
      apply (le_div_iff₀ hn').2
      linarith
    let q : ℝ := (2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)
    have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
    have hsquare : q ^ 2 ≤ 2 := by
      have heq : q ^ 2 = (2 : ℝ) ^
          ((1 - (degreeTwoCount G : ℝ) / G.vertexCount) * 2) := by
        unfold q
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [heq]
      calc
        _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one _
    have hp : q ^ (2 * k) ≤ (2 : ℝ) ^ k := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hsquare k
    have hm : 1 ≤ G.edgeCount := edgeCount_pos_of_min_two G hmin hn
    have hm' : (1 : ℝ) ≤ 2 * G.edgeCount := by exact_mod_cast (by omega : 1 ≤ 2 * G.edgeCount)
    have hc : (2 : ℝ) ^ k ≤ 2 * (G.edgeCount : ℝ) * 2 ^ k := by
      simpa using mul_le_mul_of_nonneg_right hm' (by positivity : 0 ≤ (2 : ℝ) ^ k)
    have htr := real_trace_pow_nonneg G (2 * k)
    change q ^ (2 * k) - _ ≤ _
    linarith

/-- Complete normalized even trace lower bound. All real powers in the
normalization are explicitly typed; the exponent `2*k` of the matrix is a
natural number. `degreeTwoCount` counts actual vertices, not suppressed ones. -/
theorem normalized_even_trace_lower
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (k : ℕ) (hk : 0 < k) :
    (2 : ℝ) ^ (-(degreeTwoCount G : ℝ) * (2 * (k : ℝ)) / G.vertexCount) -
      2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) / (2 : ℝ) ^ (2 * k) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
  apply (le_div_iff₀ hp).2
  have hmain := actual_even_trace_lower G hmin hmax hn k hk
  have hexp :
      (2 : ℝ) ^ (-(degreeTwoCount G : ℝ) * (2 * (k : ℝ)) / G.vertexCount) *
          (2 : ℝ) ^ (2 * k) =
      ((2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)) ^ (2 * k) := by
    have hpwr (a : ℝ) :
        ((2 : ℝ) ^ a) ^ (2 * k) = (2 : ℝ) ^ (a * (2 * (k : ℝ))) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ a) (2 * k),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_cast
    have hnat : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * (k : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * k)]
      norm_cast
    rw [hnat, hpwr, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have herr : (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k := by
    have hnat : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * (k : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * k)]
      norm_cast
    rw [hnat, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h : -(k : ℝ) + 2 * k = k := by ring
    rw [h, Real.rpow_natCast]
  calc
    _ = ((2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)) ^ (2 * k) -
          2 * (G.edgeCount : ℝ) * 2 ^ k := by
      rw [sub_mul, mul_assoc, hexp, herr]
    _ ≤ _ := hmain



end Erdos1016.Nonbacktracking

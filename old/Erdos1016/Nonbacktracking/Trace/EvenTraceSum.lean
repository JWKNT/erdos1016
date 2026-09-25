import Erdos1016.Nonbacktracking.Trace.EvenTrace

set_option autoImplicit false

/-!
# A summed consequence of the actual even-trace theorem

This records the contribution of the even powers to the paper's weighted
trace sum. Odd powers are nonnegative actual run counts, but this estimate
does not recover the paper's stronger paired-spectral coefficient.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.Nonbacktracking
local instance evenTraceSumDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- Sum the proved normalized even-trace lower bound over an arbitrary
positive interval of half-lengths. Each summand is an actual matrix trace;
the error is summed explicitly rather than hidden in an asymptotic term. -/
theorem normalized_even_trace_sum_lower
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (M L : ℕ) (hM : 0 < M) :
    (∑ k ∈ Finset.Icc M L,
      ((2 : ℝ) ^ (-(degreeTwoCount G : ℝ) * (2 * (k : ℝ)) / G.vertexCount) -
        2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ (-(k : ℝ))) / (4 * (k : ℝ))) ≤
    ∑ k ∈ Finset.Icc M L,
      (Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) /
        (2 : ℝ) ^ (2 * k)) / (4 * (k : ℝ)) := by
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := hM.trans_le (Finset.mem_Icc.mp hk).1
  have htrace := normalized_even_trace_lower G hmin hmax hn k hkpos
  have hden : 0 < 4 * (k : ℝ) := by positivity
  exact (div_le_div_of_nonneg_right htrace hden.le)







end Erdos1016.Nonbacktracking

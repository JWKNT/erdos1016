import Erdos1016.Probability.Moments.Bonferroni

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.FactorialMomentAvoidance

open scoped BigOperators
open Erdos1016.Proof.ConditionalMoments

local instance factorialAvoidanceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Assemble the finite Bonferroni estimate, the source factorial-moment
comparison, and its summed error budget into the paper's Poisson avoidance
bound. The graph-specific conditional-load argument supplies `hraw`; this
lemma handles only its finite-probability and arithmetic interface. -/
theorem finite_avoidance_le_poisson_of_factorial_moment_errors
    {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (P : ι → Ω → Prop) (K : ℕ) (hK : Even K)
    (lambdaVar budget : ℝ) (hlambda : 0 ≤ lambdaVar)
    (rawError : ℕ → ℝ)
    (hlow : ∀ j, j < 2 →
      finiteFactorialMoment s P j = lambdaVar ^ j / (j.factorial : ℝ))
    (hraw : ∀ j ∈ Finset.Icc 2 K,
      |finiteFactorialMoment s P j - lambdaVar ^ j / (j.factorial : ℝ)| ≤
        rawError j / (j.factorial : ℝ))
    (hbudget : (∑ j ∈ Finset.range (K + 1),
      if 2 ≤ j then rawError j / (j.factorial : ℝ) else 0) ≤ budget) :
    Finite.density (fun ω => finiteEventCount s P ω = 0) ≤
      Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
        ((K + 1).factorial : ℝ) + budget := by
  let err : ℕ → ℝ := fun j =>
    if 2 ≤ j then rawError j / (j.factorial : ℝ) else 0
  have hMoment : ∀ j ∈ Finset.range (K + 1),
      (-1 : ℝ) ^ j * finiteFactorialMoment s P j ≤
        (-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ) + err j := by
    intro j hj
    have hjle : j ≤ K := by
      have := Finset.mem_range.mp hj
      omega
    by_cases hjtwo : 2 ≤ j
    · have hjmem : j ∈ Finset.Icc 2 K := Finset.mem_Icc.mpr ⟨hjtwo, hjle⟩
      have hdev := hraw j hjmem
      have hfac : (0 : ℝ) < (j.factorial : ℝ) := by positivity
      have herror : 0 ≤ rawError j / (j.factorial : ℝ) := by
        exact le_trans (abs_nonneg _) hdev
      have hsign : |(-1 : ℝ) ^ j| = 1 := by
        rw [abs_neg_one_pow]
      have hscaled :
          |(-1 : ℝ) ^ j *
            (finiteFactorialMoment s P j - lambdaVar ^ j / (j.factorial : ℝ))| ≤
            rawError j / (j.factorial : ℝ) := by
        rw [abs_mul, hsign, one_mul]
        exact hdev
      have hupper := (abs_le.mp hscaled).2
      have hrewrite :
          (-1 : ℝ) ^ j * finiteFactorialMoment s P j -
            (-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ) =
          (-1 : ℝ) ^ j *
            (finiteFactorialMoment s P j - lambdaVar ^ j / (j.factorial : ℝ)) := by
        ring
      simp only [err, if_pos hjtwo]
      have hupper' :
          (-1 : ℝ) ^ j * finiteFactorialMoment s P j -
            (-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ) ≤
          rawError j / (j.factorial : ℝ) := by
        rw [hrewrite]
        exact hupper
      linarith
    · have hjlt : j < 2 := by omega
      simp only [hlow j hjlt, err, if_neg hjtwo]
      exact le_of_eq (by ring)
  have havoid := finite_avoidance_le_exp_taylor_errors s P K hK
    lambdaVar hlambda err hMoment
  calc
    Finite.density (fun ω => finiteEventCount s P ω = 0) ≤
        Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
          ((K + 1).factorial : ℝ) +
          ∑ j ∈ Finset.range (K + 1), err j := havoid
    _ ≤ Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
          ((K + 1).factorial : ℝ) + budget := by
      dsimp [err] at hbudget ⊢
      linarith

end Erdos1016.Proof.FactorialMomentAvoidance
end

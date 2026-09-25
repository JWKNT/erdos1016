import Erdos1016.Extremal.Statement

set_option autoImplicit false

/-!
# Lower bounds pass to the extremal infimum

If every pancyclic graph on `Fin n` obeys a common lower bound on its excess,
the bound also holds for the extremal value `h n`. The nonemptiness hypothesis
ensures that this natural-valued infimum is attained by a candidate.
-/

namespace Erdos1016.Problem1016



/-- The real-valued form used in the asymptotic statement. -/
theorem real_lower_bound_of_candidate_graphs (n : ℕ) (B : ℝ)
    (hne : (candidateExcesses n).Nonempty)
    (hbound : ∀ G : SimpleGraph (Fin n), IsPancyclic G → B ≤ (excess n G : ℝ)) :
    B ≤ (h n : ℝ) := by
  classical
  have hmem : h n ∈ candidateExcesses n := by
    change sInf (candidateExcesses n) ∈ candidateExcesses n
    exact Nat.sInf_mem hne
  obtain ⟨G, hG, heq⟩ := hmem
  rw [← heq]
  exact hbound G hG

end Erdos1016.Problem1016

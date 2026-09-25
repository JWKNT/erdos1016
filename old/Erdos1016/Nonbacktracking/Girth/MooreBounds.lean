import Erdos1016.Nonbacktracking.Walks.RunGeometry
import Erdos1016.Nonbacktracking.Entropy.MooreBounds

set_option autoImplicit false

/-!
# Actual high-girth Moore and excess bounds

These replace the former endpoint-injectivity input by the actual girth
condition. The graph may be disconnected. The only domain convention is
that a k-transition dart Run traverses k+1 graph edges.

These prove source Section 7's two-core entropy bound and Lemma 7.2.
The leaf/isolated-vertex deficit-shrink assembly of Lemma 7.1 and the
three-contact argument of Section 8 remain separate obligations.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
local instance girthMooreDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)



/-- Stationary entropy plus actual girth, with no connectedness hypothesis. -/
theorem entropy_bound_of_girth
    (hmin : ∀ v, 2 ≤ G.degree v) (hn : 0 < G.vertexCount)
    (D k : ℕ) (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * (k + 1) ≤ D) :
    (k : ℝ) * meanLogBranching G ≤ Real.logb 2 ((G.vertexCount : ℝ) / 2) :=
  endpoint_injective_entropy_bound G hmin hn k
    (endpoints_injective_of_girth G D k hg hshort)

/-- Deficit version of the same entropy inequality. This is the estimate
used AFTER a full two-core has been constructed in source Lemma 7.1. -/
theorem degreeTwo_entropy_bound_of_girth
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (D k : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * (k + 1) ≤ D) :
    (k : ℝ) * (1 - (degreeTwoCount G : ℝ) / G.vertexCount) ≤
      Real.logb 2 ((G.vertexCount : ℝ) / 2) := by
  exact (mul_le_mul_of_nonneg_left (meanLogBranching_lower G hmin hmax hn)
    (Nat.cast_nonneg k)).trans (entropy_bound_of_girth G hmin hn D k hg hshort)







end Erdos1016.Nonbacktracking

import Erdos1016.ExactMaximumSupport.Shortening.MarginFewCycles
import Erdos1016.ExactMaximum.SmallCutCaps

set_option autoImplicit false

/-! The small-cut and compactness cases share one arbitrary-margin cycle bound. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.UnifiedFewCycles
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum

/-- The old fixed-margin interface is a specialization of the general theorem. -/
theorem fewCyclesStatement : ExactMaximum.FewCyclesStatement := by
  obtain ⟨K,hK⟩ := MarginFewCycles.exists_bound (1/1000) (by norm_num)
  refine ⟨max K 1,le_max_right _ _,?_⟩
  intro V E _ _ N hN s t hs ht hst hrich
  have hreal : (501:ℝ)*(2:ℝ)^networkRank N≤1000*(N.numPaths s t:ℝ) := by
    exact_mod_cast hrich
  have hm : (1/2+(1/1000:ℝ))*(2:ℝ)^networkRank N≤N.numPaths s t := by
    linarith
  exact (hK V E N hN s t hs ht hst hm).trans
    (Nat.mul_le_mul_right _ (le_max_left _ _))

/-- The two/three-cut caps use the same cycle-bound proof as compactness. -/
theorem threeCutStatement : ExactMaximum.ThreeCutStatement :=
  ExactMaximum.threeCutStatement_of_caps fewCyclesStatement ExactMaximum.capStatement

end Erdos1016.ExactMaximumSupport.Shortening.UnifiedFewCycles

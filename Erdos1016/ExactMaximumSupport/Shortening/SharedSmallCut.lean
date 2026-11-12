import Erdos1016.ExactMaximumSupport.Shortening.UnifiedFewCycles
import Erdos1016.ExactMaximum.CycleBoundMargin
import Erdos1016.ExactMaximum.SmallCutCase

set_option autoImplicit false

/-! The original small-cut proof shares the same leading bound and FewCycles
proof as the remaining cases. No duplicate fixed nine-sixteenths proof is used. -/
namespace Erdos1016.ExactMaximumSupport.Shortening.SharedSmallCut
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum

/-- Nine sixteenths is the margin-three instance of the common leading bound. -/
theorem poleCycleBoundStatement : ExactMaximum.PoleCycleBoundStatement := by
  obtain ⟨B,hB⟩ := ExactMaximum.numCycles_le_of_large_rank_margin 3
  refine ⟨B,?_⟩
  intro V E _ _ N _ hr
  simpa only [show (3:ℕ)+1=4 by rfl,show (2:ℕ)^4=16 by norm_num,
    show (2:ℕ)^3+1=9 by norm_num] using hB V E N hr

/-- The original two/three-cut proof, with both global bounds shared. -/
theorem threeCutStatement : ExactMaximum.ThreeCutStatement :=
  ExactMaximum.threeCutStatement_of_poles UnifiedFewCycles.fewCyclesStatement
    poleCycleBoundStatement

end Erdos1016.ExactMaximumSupport.Shortening.SharedSmallCut

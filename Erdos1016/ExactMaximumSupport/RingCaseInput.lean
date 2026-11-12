import Erdos1016.ExactMaximumSupport.FourCutGluing
import Erdos1016.ExactMaximumSupport.MixedChainGlue
import Erdos1016.ExactMaximum.FullPairs

set_option autoImplicit false

/-! # The actual full-cross ring case -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- The full-cross ring case holds for every original network of rank at least eight. -/
theorem ringCaseStatement : ExactMaximum.RingCaseStatement := by
  classical
  refine ⟨8,?_⟩
  intro V E _ _ N _ hcubic hmin hr S e x y hcover hjoins hx hy hxinj hyinj hpole hqole hfull
  obtain ⟨k,l,T,U,twist,⟨I⟩⟩ := FourCutGluing.exists_glued N hcubic hmin S e x y
    hcover hjoins hx hy hxinj hyinj hpole hqole hfull
  have h := MixedTiles.glued_numCycles_le_horakKim_rank T U twist
    (by rwa [←I.networkRank_eq])
  rwa [←I.numCycles_eq,←I.networkRank_eq] at h

end Erdos1016.ExactMaximumSupport

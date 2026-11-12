import Erdos1016.ExactMaximumSupport.PoleTrackedSuppression
import Erdos1016.ExactMaximumSupport.PoleExtendedShoreInduction
import Erdos1016.ExactMaximum.CyclicShore

set_option autoImplicit false

/-!
# A cubic cyclic shore in every sufficiently large path-rich bounded-port pole

Actual extra-port suppressions retain rank and path count.  Marking every
suppressed thread uses at most `3*g+2` original vertices, and the marked two-pole
theorem supplies a shore which lifts unchanged through every suppression.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- Corollary 5.6 for the actual pole, with all bridge and suppression cases discharged. -/
theorem cyclicShoreStatement : ExactMaximum.CyclicShoreStatement := by
  intro m g
  obtain ⟨B,hB⟩ := PoleExtendedShore.marked_two_pole_constant m (3*g+2)
  refine ⟨B,?_⟩
  intro V E _ _ N hN hcount hrank s t hs ht hst hrich
  have hhalf := CyclicShoreMargin.strict_half m _ _ hrich
  obtain ⟨E',iE',M,Y,hred,hY,hsY,htY⟩ :=
    PoleTrackedSuppression.exists_marked_two_pole N g s t hN hs ht hst hcount hhalf
  letI := iE'
  obtain ⟨hM,hMr,hMp,_,_,hlift⟩ := hred
  have hrichM : (2^m+2)*2^networkRank M≤2^(m+1)*M.numPaths s t := by
    rw [hMr,hMp]
    exact hrich
  obtain ⟨S,hS,hcut,hdegree,havoid⟩ := hB V E' M s t hM hrichM Y hY hsY htY
    (by rw [hMr]; exact hrank)
  obtain ⟨hSN,hcutN,hdegreeN⟩ := hlift S hS hdegree havoid
  exact ⟨S,hSN,hcutN.trans_le hcut,hdegreeN⟩

end Erdos1016.ExactMaximumSupport

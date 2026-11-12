import Erdos1016.ExactMaximumSupport.FullPairAvoidance

set_option autoImplicit false

/-!
# Ordered rails obtained from an actual full two-pole

The input contains no supplied path order or matching certificate.
The graph theorems construct both rails, their orders, and the pattern avoidance.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairOrderedRails
open BoundaryTrace BoundaryTrace.Network NetworkPathOrder
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Every full bridgeless two-pole has actual ordered rails with a ladder permutation. -/
theorem exists_ordered_rails {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) :
    ∃ p q : N.Word, ∃ hp : N.IsPathWord s t p, ∃ hq : N.IsPathWord s t q,
    ∃ hedge : ∀ e,p e≠0 → q e=0,
    ∃ L : Order N s t p, ∃ R : Order N s t q,
      LadderPermutation.AvoidsLadderPatterns
        (FullPairPermutation.permutation N hN hfull hp hq hedge L R) := by
  obtain ⟨p,q,hp,hq,hedge,_,_⟩ := PoleTwoPaths.exists_two_paths N s t hN
  obtain ⟨L⟩ := NetworkPathOrder.exists_order N hp
  obtain ⟨R⟩ := NetworkPathOrder.exists_order N hq
  exact ⟨p,q,hp,hq,hedge,L,R,
    FullPairAvoidance.avoids_ladder_patterns N hN hfull hp hq hedge L R⟩

end Erdos1016.ExactMaximumSupport.FullPairOrderedRails

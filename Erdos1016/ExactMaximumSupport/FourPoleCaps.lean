import Erdos1016.ExactMaximum.NetAddVertex
import Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Two physical caps on a four-pole

The construction retains every original vertex and physical edge label.
Four full cross pairs force equality in both the path and rank bounds.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleCaps
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Cap the first pair and then the second pair by new degree-two vertices. -/
def capped (a b c d : V) : Network (Option (Option V)) ((E ⊕ Bool) ⊕ Bool) :=
  (N.addVertex a b).addVertex (some c) (some d)

/-- The first cap vertex in the double-cap network. -/
def left : Option (Option V) := some none

/-- The second cap vertex in the double-cap network. -/
def right : Option (Option V) := none

/-- Each physical cap raises rank by at most one. -/
theorem rank_le (a b c d : V) : networkRank (capped N a b c d)≤networkRank N+2 := by
  have h₁ := N.networkRank_addVertex_le a b
  have h₂ := (N.addVertex a b).networkRank_addVertex_le (some c) (some d)
  change networkRank ((N.addVertex a b).addVertex (some c) (some d))≤networkRank N+2
  omega

/-- The four cross-path families inject into paths between the new caps. -/
theorem four_paths_le (a b c d : V) :
    N.numPaths a c+N.numPaths b c+N.numPaths a d+N.numPaths b d ≤
      (capped N a b c d).numPaths left right := by
  have hc := N.numPaths_add_le_numPaths_addVertex a b c
  have hd := N.numPaths_add_le_numPaths_addVertex a b d
  have h₂ := (N.addVertex a b).numPaths_add_le_numPaths_addVertex (some c) (some d) none
  rw [ExactMaximum.numPaths_symm (N.addVertex a b) (some c) none,
    ExactMaximum.numPaths_symm (N.addVertex a b) (some d) none] at h₂
  have hs : (capped N a b c d).numPaths right left=
      (capped N a b c d).numPaths left right := ExactMaximum.numPaths_symm _ _ _
  change (N.addVertex a b).numPaths none (some c)+
    (N.addVertex a b).numPaths none (some d)≤(capped N a b c d).numPaths right left at h₂
  omega

/-- Full cross pairs give an actual full cap pair and exact rank growth two. -/
theorem full_and_rank (a b c d : V)
    (hac : N.IsFullPair a c) (hbc : N.IsFullPair b c)
    (had : N.IsFullPair a d) (hbd : N.IsFullPair b d) :
    (capped N a b c d).IsFullPair left right ∧
      networkRank (capped N a b c d)=networkRank N+2 := by
  have hlow := four_paths_le N a b c d
  rw [show N.numPaths a c=2^networkRank N from hac,
    show N.numPaths b c=2^networkRank N from hbc,
    show N.numPaths a d=2^networkRank N from had,
    show N.numPaths b d=2^networkRank N from hbd] at hlow
  have hup := (capped N a b c d).numPaths_le_two_pow left right
  have hr := rank_le N a b c d
  have hpow : 2^networkRank (capped N a b c d)≤2^(networkRank N+2) :=
    Nat.pow_le_pow_right (by omega) hr
  have he : 2^(networkRank N+2)=4*2^networkRank N := by ring
  have hfull : (capped N a b c d).IsFullPair left right := by
    change (capped N a b c d).numPaths left right=2^networkRank (capped N a b c d)
    omega
  have hpeq : 2^networkRank (capped N a b c d)=2^(networkRank N+2) := by omega
  exact ⟨hfull,(Nat.pow_right_injective (by omega : 1<(2:ℕ))) hpeq⟩

end Erdos1016.ExactMaximumSupport.FourPoleCaps

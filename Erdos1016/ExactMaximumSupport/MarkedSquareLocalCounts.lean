import Erdos1016.ExactMaximumSupport.NetworkOneCutRoutes
import Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The three-edge square remainder

After deleting one square edge, its right endpoint is a leaf in the prefix.
Deleting that leaf leaves a genuine two-edge thread at the other right vertex.
The four continuation routes therefore total exactly `4+3*A`.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MarkedSquareLocalCounts
open BoundaryTrace BoundaryTrace.Network NetworkOneCutRoutes NetworkThreadPathCounts
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

private theorem numPaths_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) :
    @Network.numPaths A B i N a b = @Network.numPaths A B j N a b := by
  rw [Subsingleton.elim i j]

/-- The four local route coefficients are literal path counts, including one empty route. -/
theorem route_sum (N : Network V E) {g : E} {a b c d : V}
    (hg : N.Joins g c b) (honly : ∀q,N.src q=c ∨ N.dst q=c → q=g)
    (hac : a≠c) (hdc : d≠c)
    {e f : {q : E // N.outside (fun v => v=c) q}}
    (T : (N.sub (N.outside (fun v => v=c))).Thread e f a d b) :
    N.numPaths a c+N.numPaths a d+1+N.numPaths c d=
      4+3*(PoleTerminalDeletion.deleted (N.sub (N.outside (fun v => v=c))) d).numPaths a b := by
  let M := N.sub (N.outside (fun v => v=c))
  have h₁ : N.numPaths a c=(PoleTerminalDeletion.deleted M d).numPaths a b+1 := by
    rw [ExactMaximum.numPaths_symm N a c,leaf_to_target N hg honly hac,
      if_neg T.huw.symm,ExactMaximum.numPaths_symm M b a,NetworkThreadPathCounts.endpoints M T]
  have h₂ : N.numPaths a d=1+(PoleTerminalDeletion.deleted M d).numPaths a b := by
    rw [delete_leaf N hg honly hac hdc,ExactMaximum.numPaths_symm M a d]
    exact NetworkThreadPathCounts.middle_left M T
  have h₃ : N.numPaths c d=1+(PoleTerminalDeletion.deleted M d).numPaths a b := by
    rw [leaf_to_target N hg honly hdc,if_neg T.v_ne_w.symm,
      ExactMaximum.numPaths_symm M b d]
    exact NetworkThreadPathCounts.middle_right M T
  rw [h₁,h₂,h₃]
  have hA : (PoleTerminalDeletion.deleted M d).numPaths a b=
      (PoleTerminalDeletion.deleted (N.sub (N.outside (fun v => v=c))) d).numPaths a b :=
    numPaths_instances _ _ _ _ _
  rw [hA]
  omega

end Erdos1016.ExactMaximumSupport.MarkedSquareLocalCounts

import Erdos1016.ExactMaximumSupport.ThirdPortDeletedEdge
import Erdos1016.ExactMaximumSupport.NetworkPositiveSubnetwork
import Erdos1016.ExactMaximumSupport.NetworkIsoSubnetwork

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Transport the restored third-port count into a concrete core

The original thread identifies the marked label. Removing isolated vertices
and relabeling the full core preserve both branches of the restored-port count.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortRestoredCore
open BoundaryTrace BoundaryTrace.Network
local instance (priority := 2000) restoredCoreDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem numPaths_fintype {A B : Type*} (M : Network A B)
    (i j : Fintype B) (s t : A) :
    @Network.numPaths A B i M s t = @Network.numPaths A B j M s t := by
  rw [Subsingleton.elim i j]

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {e f : E} {u v w : V} (T : N.Thread e f u v w)

abbrev suppressed := N.suppress e f u w T.huw
abbrev core := ThirdPortMarkedCore.positive (suppressed N T)
abbrev marked := ThirdPortMarkedCore.positiveEdge (suppressed N T) ⟨e,T.hef⟩

variable {V' E' : Type*} [Fintype V'] [Fintype E'] {K : Network V' E'}
variable (R : NetworkIso (core N T) K)

/-- The core isomorphism restricts to deletion of the exact original thread label. -/
def deletedIso :
    NetworkIso ((core N T).sub fun g => g.1.1 ≠ e)
      (K.sub fun g => g ≠ R.edges (marked N T)) :=
  R.sub (fun g => g.1.1 ≠ e) (fun g => g ≠ R.edges (marked N T)) (fun g => by
    constructor
    · intro h heq
      have hh := congrArg (fun q => q.1.1) (R.edges.injective heq)
      exact h hh
    · intro h heq
      apply h
      apply congrArg R.edges
      apply Subtype.ext
      apply Subtype.ext
      exact heq)

/-- Deleted-core path counts agree after both normalization and relabeling. -/
theorem numPaths_deleted (a b : {z : V // 0 < (suppressed N T).deg (fun _ => 1) z}) :
    (K.sub fun g => g ≠ R.edges (marked N T)).numPaths (R.vertices a) (R.vertices b) =
      (ThirdPortDeletedEdge.cutCore N T).numPaths a.1 b.1 := by
  calc
    _ = ((core N T).sub fun g => g.1.1 ≠ e).numPaths a b :=
      (deletedIso N T R).numPaths_eq a b
    _ = _ := NetworkPositiveSubnetwork.numPaths_positive_sub
      (suppressed N T) (fun g => g.1 ≠ e) a b

/-- The original third-port count is expressed in any concrete model of its full core. -/
theorem numPaths_restored_in_model (t : V)
    (hu : 0 < (suppressed N T).deg (fun _ => 1) u)
    (hw : 0 < (suppressed N T).deg (fun _ => 1) w)
    (ht : 0 < (suppressed N T).deg (fun _ => 1) t) :
    N.numPaths v t =
      (if u=t then 1 else
        (K.sub fun g => g ≠ R.edges (marked N T)).numPaths (R.vertices ⟨u,hu⟩) (R.vertices ⟨t,ht⟩)) +
      (if w=t then 1 else
        (K.sub fun g => g ≠ R.edges (marked N T)).numPaths (R.vertices ⟨w,hw⟩) (R.vertices ⟨t,ht⟩)) := by
  rw [numPaths_deleted N T R ⟨u,hu⟩ ⟨t,ht⟩,numPaths_deleted N T R ⟨w,hw⟩ ⟨t,ht⟩]
  apply (ThirdPortDeletedEdge.numPaths_restored N T t).trans
  apply congrArg₂ (fun a b : ℕ => a+b)
  · split_ifs
    · rfl
    · exact numPaths_fintype _ _ _ _ _
  · split_ifs
    · rfl
    · exact numPaths_fintype _ _ _ _ _

end Erdos1016.ExactMaximumSupport.ThirdPortRestoredCore

import Erdos1016.ExactMaximumSupport.NetworkIsoSubnetwork
import Erdos1016.ExactMaximumSupport.NetworkIsoComposition

set_option autoImplicit false

/-!
# The path count at a restored marked edge

A branch that already reaches the target contributes one empty continuation.
The sum depends only on the physical edge, not its orientation.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MarkedPathCount
open BoundaryTrace BoundaryTrace.Network
local instance markedCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

universe u v u' v'
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] (N : Network V E)

/-- The continuation after choosing one end of the subdivided edge. -/
def branch (e : E) (a t : V) : ℕ :=
  if a=t then 1 else (N.sub fun g => g≠e).numPaths a t

/-- The two continuations from a new vertex on the marked edge. -/
def count (e : E) (t : V) : ℕ := branch N e (N.src e) t + branch N e (N.dst e) t

omit [Fintype V] in
/-- Either orientation gives the same sum of continuation counts. -/
theorem count_of_joins {e : E} {a b : V} (he : N.Joins e a b) (t : V) :
    count N e t=branch N e a t+branch N e b t := by
  rcases he with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · simp only [count,ha,hb]
  · simp only [count,ha,hb,Nat.add_comm]

variable {V' : Type u'} {E' : Type v'} [Fintype V'] [Fintype E']
variable {N' : Network V' E'} (R : NetworkIso N N')

/-- Relabeling the marked edge preserves each continuation count. -/
theorem branch_iso (e : E) (a t : V) :
    branch N' (R.edges e) (R.vertices a) (R.vertices t)=branch N e a t := by
  unfold branch
  rw [R.vertices.injective.eq_iff]
  split_ifs
  · rfl
  · exact R.numPaths_deleteEdge e a t

/-- Relabeling preserves the restored count at the corresponding marked edge. -/
theorem count_iso (e : E) (t : V) :
    count N' (R.edges e) (R.vertices t)=count N e t := by
  rw [count_of_joins N' (R.joins e),branch_iso N R,branch_iso N R]
  rfl

end Erdos1016.ExactMaximumSupport.MarkedPathCount

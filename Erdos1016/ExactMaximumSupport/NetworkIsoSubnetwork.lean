import Erdos1016.ExactMaximumSupport.NetworkIso
import Erdos1016.ExactMaximum.NetSub

set_option autoImplicit false

/-!
# Physical isomorphisms after deleting labels

An isomorphism restricts to corresponding physical label sets. In particular,
deleting a marked edge preserves the path counts under the same vertex map.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkIso
open BoundaryTrace BoundaryTrace.Network
local instance subnetworkDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v u' v'
variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
variable {N : Network V E} {N' : Network V' E'} (R : NetworkIso N N')

/-- Restrict an actual physical isomorphism to corresponding label sets. -/
def sub (p : E → Prop) (q : E' → Prop) (hpq : ∀ e,p e ↔ q (R.edges e)) :
    NetworkIso (N.sub p) (N'.sub q) where
  vertices := R.vertices
  edges :=
    { toFun := fun e => ⟨R.edges e.1,(hpq e.1).mp e.2⟩
      invFun := fun e => ⟨R.edges.symm e.1,(hpq _).mpr (by
        rw [R.edges.apply_symm_apply]
        exact e.2)⟩
      left_inv := fun e => Subtype.ext (R.edges.symm_apply_apply e.1)
      right_inv := fun e => Subtype.ext (R.edges.apply_symm_apply e.1) }
  joins e := R.joins e.1

/-- Delete the marked physical label on both sides of the isomorphism. -/
def deleteEdge (e : E) :
    NetworkIso (N.sub fun g => g≠e) (N'.sub fun g => g≠R.edges e) :=
  R.sub (fun g => g≠e) (fun g => g≠R.edges e) (fun g => by
    constructor
    · intro h heq
      exact h (R.edges.injective heq)
    · intro h heq
      exact h (congrArg R.edges heq))

variable [Fintype V] [Fintype E] [Fintype V'] [Fintype E']

/-- Every path count survives deletion of corresponding physical labels. -/
theorem numPaths_deleteEdge (e : E) (s t : V) :
    (N'.sub fun g => g≠R.edges e).numPaths (R.vertices s) (R.vertices t) =
      (N.sub fun g => g≠e).numPaths s t :=
  (R.deleteEdge e).numPaths_eq s t

end Erdos1016.ExactMaximumSupport.NetworkIso

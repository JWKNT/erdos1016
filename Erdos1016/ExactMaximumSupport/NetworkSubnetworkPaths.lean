import Erdos1016.ExactMaximumSupport.NetworkIso
import Erdos1016.ExactMaximum.NetSub

set_option autoImplicit false

/-! # Removing a label outside a physical subnetwork changes no internal count -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkSubnetworkPaths
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} (N : Network V E)

/-- The same surviving physical labels, with the redundant restriction removed. -/
def deleteOutsideIso (p : E → Prop) (e : E) (hpe : ¬p e) :
    NetworkIso ((N.sub (fun g => g≠e)).sub (fun g => p g.val)) (N.sub p) where
  vertices := Equiv.refl V
  edges :=
    { toFun := fun g => ⟨g.val.val,g.property⟩
      invFun := fun g => ⟨⟨g.val,fun heq => hpe (heq ▸ g.property)⟩,g.property⟩
      left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; rfl }
  joins _ := Or.inl ⟨rfl,rfl⟩

variable [Fintype V] [Fintype E]

/-- No path count on the retained label set depends on the removed outside label. -/
theorem numPaths_delete_outside (p : E → Prop) (e : E) (hpe : ¬p e) (a b : V) :
    ((N.sub (fun g => g≠e)).sub (fun g => p g.val)).numPaths a b=(N.sub p).numPaths a b :=
  ((deleteOutsideIso N p e hpe).numPaths_eq a b).symm

/-- The same physical isomorphism preserves its exact rank. -/
theorem rank_delete_outside (p : E → Prop) (e : E) (hpe : ¬p e) :
    networkRank ((N.sub (fun g => g≠e)).sub (fun g => p g.val))=networkRank (N.sub p) :=
  (deleteOutsideIso N p e hpe).networkRank_eq.symm

end Erdos1016.ExactMaximumSupport.NetworkSubnetworkPaths

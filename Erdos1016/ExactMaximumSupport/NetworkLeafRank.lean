import Erdos1016.ExactMaximum.NetBridgeCut
import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # Removing a physical leaf preserves rank -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkLeafRank
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

theorem singleton_rank_zero (N : Network V E) (x : V) :
    networkRank (N.sub (N.inside (fun v => v=x)))=0 := by
  by_contra h
  obtain ⟨z,hz⟩ := (N.sub (N.inside (fun v => v=x))).exists_isCycleWord_of_rank_pos
    (Nat.pos_of_ne_zero h)
  apply hz.1
  funext e
  exact False.elim (N.noLoops e.val (e.property.1.trans e.property.2.symm))

theorem rank_delete_leaf (N : Network V E) {e : E} {x y : V} (he : N.Joins e x y)
    (honly : ∀g,N.src g=x ∨ N.dst g=x → g=e) :
    networkRank N=networkRank (N.sub (N.outside (fun v => v=x))) := by
  have hC (g : E) (hg : N.crosses (fun v => v=x) g) : g=e := by
    apply honly
    by_contra h
    push_neg at h
    exact hg (by simp [h.1,h.2])
  rw [N.networkRank_of_one_crossing (fun v => v=x) hC
    (N.crosses_of_joins he rfl he.ne.symm),singleton_rank_zero,zero_add]

/-- Flatten two physical restrictions without changing any vertex or edge label. -/
def restrictionIso (N : Network V E) (p q r : E → Prop)
    (h : ∀e,p e ∧ q e ↔ r e) :
    NetworkIso ((N.sub p).sub (fun e => q e.val)) (N.sub r) where
  vertices := Equiv.refl V
  edges :=
    { toFun := fun e => ⟨e.val.val,(h e.val.val).mp ⟨e.val.property,e.property⟩⟩
      invFun := fun e => ⟨⟨e.val,((h e.val).mpr e.property).1⟩,((h e.val).mpr e.property).2⟩
      left_inv := fun e => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun e => by apply Subtype.ext; rfl }
  joins _ := Or.inl ⟨rfl,rfl⟩

/-- The twice-deleted graph is identified directly with its literal ambient labels. -/
def twoOutsideIso (N : Network V E) (p r : E → Prop) (x y : V)
    (h : ∀e,(p e ∧ N.outside (fun v => v=x) e) ∧
      N.outside (fun v => v=y) e ↔ r e) :
    NetworkIso (((N.sub p).sub ((N.sub p).outside (fun v => v=x))).sub
      (((N.sub p).sub ((N.sub p).outside (fun v => v=x))).outside (fun v => v=y)))
      (N.sub r) where
  vertices := Equiv.refl V
  edges :=
    { toFun := fun e => ⟨e.val.val.val,(h e.val.val.val).mp
        ⟨⟨e.val.val.property,e.val.property⟩,e.property⟩⟩
      invFun := fun e => ⟨⟨⟨e.val,((h e.val).mpr e.property).1.1⟩,
        ((h e.val).mpr e.property).1.2⟩,((h e.val).mpr e.property).2⟩
      left_inv := fun e => by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun e => by apply Subtype.ext; rfl }
  joins _ := Or.inl ⟨rfl,rfl⟩

end Erdos1016.ExactMaximumSupport.NetworkLeafRank

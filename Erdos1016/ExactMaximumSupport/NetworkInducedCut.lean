import Erdos1016.ExactMaximum.PoleBridges

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Lift a cyclic shore after removing isolated vertices

The shore uses original vertices and physical labels.
If the induced network keeps every edge, its cut size and vertex degrees are unchanged.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkInducedCut
open BoundaryTrace BoundaryTrace.Network
local instance inducedCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The original vertices selected by a shore of an induced network. -/
def liftSet (P : V → Prop) (S : {v // P v} → Prop) (v : V) : Prop := ∃h : P v,S ⟨v,h⟩

omit [Fintype V] [Fintype E] in
theorem liftSet_subtype (P : V → Prop) (S : {v // P v} → Prop) (v : {v // P v}) :
    liftSet P S v.val ↔ S v := by
  constructor
  · rintro ⟨h,hs⟩
    exact hs
  · intro hs
    exact ⟨v.property,hs⟩

omit [Fintype V] [Fintype E] in
theorem crosses_iff (P : V → Prop) (S : {v // P v} → Prop)
    (e : {e // N.inside P e}) :
    (N.induce P).crosses S e ↔ N.crosses (liftSet P S) e.val := by
  change (¬(S ⟨N.src e.val,e.property.1⟩ ↔ S ⟨N.dst e.val,e.property.2⟩)) ↔ _
  simp only [Network.crosses,←liftSet_subtype P S]

omit [Fintype V] [Fintype E] in
/-- Every crossing physical label survives when the induced network keeps all edges. -/
theorem cutSize_lift (P : V → Prop) (S : {v // P v} → Prop)
    (hP : ∀e,N.inside P e) :
    N.cutSize (liftSet P S)=(N.induce P).cutSize S := by
  apply Eq.symm
  apply Nat.card_congr
  exact
    { toFun := fun e => ⟨e.val.val,(crosses_iff N P S e.val).mp e.property⟩
      invFun := fun e => ⟨⟨e.val,hP e.val⟩,(crosses_iff N P S ⟨e.val,hP e.val⟩).mpr e.property⟩
      left_inv := fun e => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun e => by apply Subtype.ext; rfl }

/-- An actual cycle in an induced edge restriction survives in any containing original restriction. -/
theorem cycle_pos (P : V → Prop) (q : {e // N.inside P e} → Prop) (r : E → Prop)
    (hqr : ∀e,q e → r e.val) (hcyc : 0<((N.induce P).sub q).numCycles) :
    0<(N.sub r).numCycles := by
  let R : Network.Embed ((N.induce P).sub q) (N.sub r) :=
    { φ := Subtype.val
      ψ := fun e => ⟨e.val.val,hqr e.val e.property⟩
      φ_inj := Subtype.val_injective
      ψ_inj := by
        intro e f h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun e : {e // r e} => e.val) h
      src := fun _ => rfl
      dst := fun _ => rfl }
  obtain ⟨⟨z,hz⟩⟩ := Finite.card_pos_iff.mp hcyc
  haveI : Nonempty {x : (N.sub r).Word // (N.sub r).IsCycleWord x} :=
    ⟨⟨R.push z,(R.isCycleWord_push_iff z).mpr hz⟩⟩
  exact Nat.card_pos

/-- Both actual cycles survive when the induced shore is lifted to the original vertices. -/
theorem cyclic_lift (P : V → Prop) (S : {v // P v} → Prop)
    (hS : (N.induce P).IsCyclicCut S) : N.IsCyclicCut (liftSet P S) := by
  constructor
  · apply cycle_pos N P ((N.induce P).inside S) (N.inside (liftSet P S)) _ hS.1
    intro e he
    exact ⟨⟨e.property.1,he.1⟩,⟨e.property.2,he.2⟩⟩
  · apply cycle_pos N P ((N.induce P).outside S) (N.outside (liftSet P S)) _ hS.2
    intro e he
    exact ⟨fun h => he.1 ((liftSet_subtype P S ⟨N.src e.val,e.property.1⟩).mp h),
      fun h => he.2 ((liftSet_subtype P S ⟨N.dst e.val,e.property.2⟩).mp h)⟩

omit [Fintype V] in
/-- Removing vertices incident to no edge preserves the full physical degree. -/
theorem deg_lift (P : V → Prop) (hP : ∀e,N.inside P e) (v : {v // P v}) :
    (N.induce P).deg (fun _ => 1) v=N.deg (fun _ => 1) v.val := by
  rw [N.deg_induce,N.deg_sub_ones]
  have hw : restrict (fun _ : E => (1 : Bit)) (N.inside P)=fun _ => 1 := by
    funext e
    exact restrict_apply_of_pos _ (hP e)
  rw [hw]

end Erdos1016.ExactMaximumSupport.NetworkInducedCut

import Erdos1016.ExactMaximumSupport.MixedCappedTileCut
import Erdos1016.ExactMaximumSupport.MarkedTileCount

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # Discharging the suffix count for an actual marked local tile label -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedLocalCount
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles MixedCappedTileCut
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

private theorem numPaths_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) :
    @Network.numPaths A B i N a b = @Network.numPaths A B j N a b := by
  rw [Subsingleton.elim i j]

private theorem route_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) (d e : Decidable (a=b)) :
    @ite ℕ (a=b) d 1 (@Network.numPaths A B i N a b)=
      @ite ℕ (a=b) e 1 (@Network.numPaths A B j N a b) := by
  rw [Subsingleton.elim i j,Subsingleton.elim d e]

abbrev deletedInside (T : Fin (k+1) → Kind) (p : Fin (k+1)) (e : CappedEdge T) :=
  ((capped T).sub (fun g => g≠e)).sub
    (((capped T).sub (fun g => g≠e)).inside (after T p))

/-- A marked inside label does not change either actual suffix route count. -/
theorem deleted_exterior_route (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (e : CappedEdge T) (he : (capped T).inside (after T p) e) (b : Bool) :
    (if exitVertex T p b=Sum.inr true then 1 else
      (((capped T).sub (fun g => g≠e)).sub
        (((capped T).sub (fun g => g≠e)).outside (after T p))).numPaths
          (exitVertex T p b) (Sum.inr true))=2^remainingWeight T p := by
  have hout : ¬(capped T).outside (after T p) e := fun h =>
    (capped T).not_inside_of_outside h he
  have hh := exterior_route_count T p b
  by_cases hb : exitVertex T p b=Sum.inr true
  · simpa only [if_pos hb] using hh
  · simp only [if_neg hb] at hh ⊢
    have hn := NetworkSubnetworkPaths.numPaths_delete_outside (capped T)
      ((capped T).outside (after T p)) e hout (exitVertex T p b) (Sum.inr true)
    exact (numPaths_instances _ _ _ _ _).trans (hn.trans hh)

/-- The concrete suffix is full; all remaining variation is in four prefix routes. -/
theorem count_eq (T : Fin (k+1) → Kind) (p : Fin (k+1)) (e : CappedEdge T)
    {a b : CappedVertex T} (he : (capped T).Joins e a b)
    (ha : after T p a) (hb : after T p b) (c : Bool) :
    MarkedPathCount.count (capped T) e (Sum.inr true)=
      ((if a=Sum.inl (right T p c) then 1 else
          (deletedInside T p e).numPaths a (Sum.inl (right T p c)))+
        (if a=Sum.inl (right T p (!c)) then 1 else
          (deletedInside T p e).numPaths a (Sum.inl (right T p (!c))))+
        (if b=Sum.inl (right T p c) then 1 else
          (deletedInside T p e).numPaths b (Sum.inl (right T p c)))+
        (if b=Sum.inl (right T p (!c)) then 1 else
          (deletedInside T p e).numPaths b (Sum.inl (right T p (!c)))))*
        2^remainingWeight T p := by
  have hei : (capped T).inside (after T p) e := by
    rcases he with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · exact ⟨hs ▸ ha,hd ▸ hb⟩
    · exact ⟨hs ▸ hb,hd ▸ ha⟩
  have h := MarkedTileCount.count_eq (capped T) (after T p)
    (e:=e) (f:=exitEdge T p c) (g:=exitEdge T p (!c))
    (a:=a) (b:=b) (x:=Sum.inl (right T p c)) (u:=Sum.inl (right T p (!c)))
    (y:=exitVertex T p c) (v:=exitVertex T p (!c)) (t:=Sum.inr true) he ha hb
    (after_right T p c) (after_right T p (!c))
    (exit_joins T p c) (not_after_exit T p c)
    (exit_joins T p (!c)) (not_after_exit T p (!c))
    (exit_ne T p c) (crossing_labels T p c) (not_after_cap T p)
    (2^remainingWeight T p)
    (by
      by_cases hb : exitVertex T p c=Sum.inr true
      · simpa only [if_pos hb] using deleted_exterior_route T p e hei c
      · rw [if_neg hb]
        have hh := deleted_exterior_route T p e hei c
        rw [if_neg hb] at hh
        exact (numPaths_instances _ _ _ _ _).trans hh)
    (by
      by_cases hb : exitVertex T p (!c)=Sum.inr true
      · simpa only [if_pos hb] using deleted_exterior_route T p e hei (!c)
      · rw [if_neg hb]
        have hh := deleted_exterior_route T p e hei (!c)
        rw [if_neg hb] at hh
        exact (numPaths_instances _ _ _ _ _).trans hh)
  calc
    _ = _ := h
    _ = _ := by
      apply congrArg (fun n : ℕ => n*2^remainingWeight T p)
      apply congrArg₂ (fun x y : ℕ => x+y)
      · apply congrArg₂ (fun x y : ℕ => x+y)
        · apply congrArg₂ (fun x y : ℕ => x+y)
          · exact route_instances _ _ _ _ _ _ _
          · exact route_instances _ _ _ _ _ _ _
        · exact route_instances _ _ _ _ _ _ _
      · exact route_instances _ _ _ _ _ _ _

end Erdos1016.ExactMaximumSupport.MixedCappedLocalCount

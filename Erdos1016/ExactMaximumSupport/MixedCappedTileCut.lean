import Erdos1016.ExactMaximumSupport.MixedCappedInterfaceCounts
import Erdos1016.ExactMaximumSupport.NetworkSubnetworkPaths

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # The literal cut after an arbitrary capped-ladder tile

The last tile uses the two right-cap labels, so its continuation routes are
explicitly empty routes of count one.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedTileCut
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles MixedCappedTailEmbed
open scoped BigOperators
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

def after (T : Fin (k+1) → Kind) (p : Fin (k+1)) : CappedVertex T → Prop
  | Sum.inl v => v.1.val≤p.val
  | Sum.inr b => b=false

def exitEdge (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedEdge T :=
  if h : p.val<k then Sum.inl (link T ⟨p.val,h⟩ b) else Sum.inr (Sum.inr b)

def exitVertex (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedVertex T :=
  if h : p.val<k then Sum.inl (left T ⟨p.val+1,by omega⟩ b) else Sum.inr true

def precedingWeight (T : Fin (k+1) → Kind) (p : Fin (k+1)) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => i.val < p.val), (T i).weight

def remainingWeight (T : Fin (k+1) → Kind) (p : Fin (k+1)) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => p.val < i.val), (T i).weight

@[simp] theorem after_right (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    after T p (Sum.inl (right T p b)) := by simp [after,right]
@[simp] theorem after_left (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    after T p (Sum.inl (left T p b)) := by simp [after,left]
@[simp] theorem not_after_cap (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    ¬after T p (Sum.inr true) := by simp [after]
@[simp] theorem not_after_exit (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    ¬after T p (exitVertex T p b) := by
  unfold exitVertex
  split <;> simp [after,left]

theorem exit_joins (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    (capped T).Joins (exitEdge T p b) (Sum.inl (right T p b)) (exitVertex T p b) := by
  by_cases hp : p.val<k
  · simp only [exitEdge,exitVertex,dif_pos hp]
    exact Or.inl ⟨rfl,rfl⟩
  · have heq : p=Fin.last k := Fin.ext (by simp only [Fin.val_last]; have hh := p.isLt; omega)
    subst p
    simp only [exitEdge,exitVertex,Fin.val_last,lt_self_iff_false,dif_neg]
    exact Or.inl ⟨rfl,rfl⟩

theorem exit_ne (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    exitEdge T p b≠exitEdge T p (!b) := by
  unfold exitEdge
  split <;> cases b <;> simp [link]

theorem crossing_labels (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool)
    (e : CappedEdge T) (he : (capped T).crosses (after T p) e) :
    e=exitEdge T p b ∨ e=exitEdge T p (!b) := by
  rcases e with (⟨i,e⟩ | ⟨i,c⟩) | (c | c)
  · simp [Network.crosses,after,capped,cappedSrc,cappedDst,chain,chainSrc,chainDst] at he
  · have hip : i.val=p.val := by
      simp only [Network.crosses,after,capped,cappedSrc,cappedDst,chain,chainSrc,
        chainDst,right,left,Fin.coe_castSucc,Fin.val_succ] at he
      omega
    have hp : p.val<k := hip ▸ i.isLt
    have hie : i=⟨p.val,hp⟩ := Fin.ext hip
    subst i
    cases b <;> cases c <;> simp [exitEdge,hp,link]
  · simp [Network.crosses,after,capped,cappedSrc,cappedDst,left] at he
  · have hp : ¬p.val<k := by
      simp [Network.crosses,after,capped,cappedSrc,cappedDst,right,Fin.val_last] at he
      omega
    cases b <;> cases c <;> simp [exitEdge,hp]

theorem after_eq_before (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : p.val<k) :
    after T p=before T ⟨p.val+1,by omega⟩ := by
  funext v
  apply propext
  cases v with
  | inl v => simp only [after,before]; omega
  | inr b => rfl

/-- Either continuation route has its full suffix count, including the final empty route. -/
theorem exterior_route_count (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    (if exitVertex T p b=Sum.inr true then 1 else
      ((capped T).sub ((capped T).outside (after T p))).numPaths
        (exitVertex T p b) (Sum.inr true))=2^remainingWeight T p := by
  by_cases hp : p.val<k
  · rw [after_eq_before T p hp]
    simp only [exitVertex,dif_pos hp,Sum.inl_ne_inr,if_false]
    rw [exterior_entry_count_sum]
    congr 1
  · have hrem : remainingWeight T p=0 := by
      unfold remainingWeight
      apply Finset.sum_eq_zero
      intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      have hip := i.isLt
      omega
    simp [exitVertex,hp,hrem]

/-- The three literal index ranges partition the total tile weight. -/
theorem weight_split (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    precedingWeight T p+(T p).weight+remainingWeight T p=weight T := by
  classical
  have hp : p∈Finset.univ := Finset.mem_univ p
  have hsum := Finset.sum_filter_add_sum_filter_not
    (s:=Finset.univ) (p:=fun i : Fin (k+1) => i.val < p.val) (f:=fun i => (T i).weight)
  have htail : (∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => ¬i.val < p.val), (T i).weight)=
      (T p).weight+remainingWeight T p := by
    unfold remainingWeight
    rw [←Finset.sum_insert (a:=p) (s:=Finset.univ.filter (fun i : Fin (k+1) => p.val < i.val))
      (f:=fun i => (T i).weight) (by simp)]
    apply Finset.sum_congr
    · apply Finset.ext
      intro i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      have heq : i=p ↔ i.val=p.val := Fin.ext_iff
      omega
    · intro i hi
      rfl
  rw [htail] at hsum
  simpa only [precedingWeight,weight,Nat.add_assoc] using hsum

end Erdos1016.ExactMaximumSupport.MixedCappedTileCut

import Erdos1016.ExactMaximumSupport.MixedCappedTileCut

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! # The literal incoming interface of a capped mixed-ladder tile -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedEntry
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
open MixedCappedTailEmbed MixedCappedTileCut
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

def entryEdge (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedEdge T :=
  if h : 0<p.val then Sum.inl (link T ⟨p.val-1,by omega⟩ b)
  else Sum.inr (Sum.inl b)

def entryVertex (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedVertex T :=
  if h : 0<p.val then Sum.inl (right T ⟨p.val-1,by omega⟩ b)
  else Sum.inr false

theorem entry_joins (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    (capped T).Joins (entryEdge T p b) (Sum.inl (left T p b)) (entryVertex T p b) := by
  by_cases hp : 0<p.val
  · simp only [entryEdge,entryVertex,dif_pos hp]
    right
    constructor
    · rfl
    · change Sum.inl (left T ⟨p.val-1+1,by omega⟩ b) = (Sum.inl (left T p b) : CappedVertex T)
      apply congrArg Sum.inl
      congr 1
      apply Fin.ext
      change p.val-1+1=p.val
      omega
  · have heq : p=0 := Fin.ext (by change p.val=0; omega)
    subst p
    simp only [entryEdge,entryVertex,Fin.val_zero,lt_self_iff_false,dif_neg]
    exact Or.inr ⟨rfl,rfl⟩

@[simp] theorem entry_before (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    before T p (entryVertex T p b) := by
  unfold entryVertex
  split
  · simp only [before,right]
    omega
  · simp [before]

@[simp] theorem left_not_before (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    ¬before T p (Sum.inl (left T p b)) := by simp [before,left]


end Erdos1016.ExactMaximumSupport.MixedCappedEntry

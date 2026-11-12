import Erdos1016.ExactMaximumSupport.MixedChainAppend
import Erdos1016.ExactMaximumSupport.MixedChainGlueModel

set_option autoImplicit false

/-!
# Physical label coordinates for two glued chains

The central interface occupies the index between the two old interface ranges.
All local labels and all four new labels have distinct images.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles

variable {k l : ℕ} (T : Fin (k+1) → Kind) (U : Fin (l+1) → Kind)

/-- The two old interface ranges and their single new central interface. -/
def appendInterfaces : (Fin k ⊕ (Fin l ⊕ Unit)) ≃ Fin ((k+1)+l) where
  toFun
    | Sum.inl i => ⟨i.val,by omega⟩
    | Sum.inr (Sum.inl j) => ⟨k+1+j.val,by omega⟩
    | Sum.inr (Sum.inr _) => ⟨k,by omega⟩
  invFun i := if h : i.val<k then Sum.inl ⟨i.val,h⟩
    else if h' : i.val=k then Sum.inr (Sum.inr ())
    else Sum.inr (Sum.inl ⟨i.val-(k+1),by omega⟩)
  left_inv x := by
    rcases x with i | (j | u)
    · simp
    · simp only [show ¬k+1+j.val<k from by omega,show ¬k+1+j.val=k from by omega,
        ↓reduceDIte,Sum.inr.injEq,Sum.inl.injEq]
      apply Fin.ext
      change k+1+j.val-(k+1)=j.val
      omega
    · cases u
      simp
  right_inv i := by
    by_cases h : i.val<k
    · simp only [dif_pos h]
    · by_cases h' : i.val=k
      · simp only [dif_neg h,dif_pos h']
        apply Fin.ext
        exact h'.symm
      · simp only [dif_neg h,dif_neg h']
        apply Fin.ext
        change k+1+(i.val-(k+1))=i.val
        omega

@[simp] theorem appendInterfaces_left (i : Fin k) :
    appendInterfaces (l := l) (Sum.inl i)=⟨i.val,by omega⟩ := rfl

@[simp] theorem appendInterfaces_right (i : Fin l) :
    appendInterfaces (k := k) (Sum.inr (Sum.inl i))=⟨k+1+i.val,by omega⟩ := rfl

@[simp] theorem appendInterfaces_center :
    appendInterfaces (k := k) (l := l) (Sum.inr (Sum.inr ()))=⟨k,by omega⟩ := rfl

/-- Rearrange the physical label alternatives without identifying any labels. -/
def glueEdgePieces : GluedEdge T U ≃
    (((InnerEdge T ⊕ InnerEdge U) ⊕ ((Fin k ⊕ (Fin l ⊕ Unit)) × Bool)) ⊕ Bool) where
  toFun
    | Sum.inl (Sum.inl (Sum.inl e)) => Sum.inl (Sum.inl (Sum.inl e))
    | Sum.inl (Sum.inr (Sum.inl e)) => Sum.inl (Sum.inl (Sum.inr e))
    | Sum.inl (Sum.inl (Sum.inr (i,b))) => Sum.inl (Sum.inr (Sum.inl i,b))
    | Sum.inl (Sum.inr (Sum.inr (i,b))) => Sum.inl (Sum.inr (Sum.inr (Sum.inl i),b))
    | Sum.inr (Sum.inl b) => Sum.inr b
    | Sum.inr (Sum.inr b) => Sum.inl (Sum.inr (Sum.inr (Sum.inr ()),b))
  invFun
    | Sum.inl (Sum.inl (Sum.inl e)) => Sum.inl (Sum.inl (Sum.inl e))
    | Sum.inl (Sum.inl (Sum.inr e)) => Sum.inl (Sum.inr (Sum.inl e))
    | Sum.inl (Sum.inr (Sum.inl i,b)) => Sum.inl (Sum.inl (Sum.inr (i,b)))
    | Sum.inl (Sum.inr (Sum.inr (Sum.inl i),b)) => Sum.inl (Sum.inr (Sum.inr (i,b)))
    | Sum.inr b => Sum.inr (Sum.inl b)
    | Sum.inl (Sum.inr (Sum.inr (Sum.inr _),b)) => Sum.inr (Sum.inr b)
  left_inv e := by rcases e with ((e | ⟨i,b⟩) | (e | ⟨i,b⟩)) | (b | b) <;> rfl
  right_inv e := by
    rcases e with ((e | e) | ⟨i | (i | u),b⟩) | b <;> rfl

/-- The exact label equivalence from two glued chains to their canonical ring. -/
def gluedEdges : GluedEdge T U ≃ RingEdge (append T U) :=
  (glueEdgePieces T U).trans
    (Equiv.sumCongr
      (Equiv.sumCongr (appendInnerEdges T U)
        (Equiv.prodCongr appendInterfaces (Equiv.refl Bool))) (Equiv.refl Bool))

@[simp] theorem gluedEdges_inner_left (e : InnerEdge T) :
    gluedEdges T U (Sum.inl (Sum.inl (Sum.inl e)))=
      Sum.inl (Sum.inl (appendInnerEdges T U (Sum.inl e))) := rfl

@[simp] theorem gluedEdges_inner_right (e : InnerEdge U) :
    gluedEdges T U (Sum.inl (Sum.inr (Sum.inl e)))=
      Sum.inl (Sum.inl (appendInnerEdges T U (Sum.inr e))) := rfl

@[simp] theorem gluedEdges_link_left (i : Fin k) (b : Bool) :
    gluedEdges T U (Sum.inl (Sum.inl (link T i b)))=
      Sum.inl (Sum.inr (⟨i.val,by omega⟩,b)) := rfl

@[simp] theorem gluedEdges_link_right (i : Fin l) (b : Bool) :
    gluedEdges T U (Sum.inl (Sum.inr (link U i b)))=
      Sum.inl (Sum.inr (⟨k+1+i.val,by omega⟩,b)) := rfl

@[simp] theorem gluedEdges_closing (b : Bool) :
    gluedEdges T U (Sum.inr (Sum.inl b))=Sum.inr b := rfl

@[simp] theorem gluedEdges_central (b : Bool) :
    gluedEdges T U (Sum.inr (Sum.inr b))=
      Sum.inl (Sum.inr (⟨k,by omega⟩,b)) := rfl

end Erdos1016.ExactMaximumSupport.MixedTiles

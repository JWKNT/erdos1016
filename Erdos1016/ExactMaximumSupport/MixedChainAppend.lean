import Erdos1016.ExactMaximumSupport.MixedTiles
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Coordinates for concatenating two physical tile chains

The two tile lists occupy consecutive disjoint index ranges.
The maps keep the physical vertices and labels of each tile.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles

variable {k l : ℕ} (T : Fin (k+1) → Kind) (U : Fin (l+1) → Kind)

/-- Append the second tile sequence after the first. -/
def append : Fin ((k+1)+l+1) → Kind := Fin.addCases (m := k+1) (n := l+1) T U

@[simp] theorem append_left (i : Fin (k+1)) :
    append T U (i.castAdd (l+1))=T i := Fin.addCases_left _

@[simp] theorem append_right (i : Fin (l+1)) :
    append T U (i.natAdd (k+1))=U i := Fin.addCases_right _

private theorem cast_left {t u : Kind} (h : t=u) (b : Bool) :
    cast (congrArg Kind.Vertex h) (t.left b)=u.left b := by cases h; rfl

private theorem cast_right {t u : Kind} (h : t=u) (b : Bool) :
    cast (congrArg Kind.Vertex h) (t.right b)=u.right b := by cases h; rfl

/-- Concatenate dependent coordinates over the two tile sequences. -/
def appendSigma (F : Kind → Type*) :
    ((Σ i,F (T i)) ⊕ (Σ i,F (U i))) ≃ (Σ i,F (append T U i)) :=
  (Equiv.sumSigmaDistrib (fun i => F (Sum.elim T U i))).symm.trans
    (Equiv.sigmaCongr finSumFinEquiv (fun i =>
      Equiv.cast (congrArg F (by
        cases i with
        | inl i => exact (append_left T U i).symm
        | inr i => exact (append_right T U i).symm))))

/-- The physical vertex equivalence for the concatenated tile sequence. -/
abbrev appendVertices : (Vertex T ⊕ Vertex U) ≃ Vertex (append T U) :=
  appendSigma T U Kind.Vertex

/-- The local physical-label equivalence for the concatenated tile sequence. -/
abbrev appendInnerEdges : (InnerEdge T ⊕ InnerEdge U) ≃ InnerEdge (append T U) :=
  appendSigma T U Kind.Edge

@[simp] theorem appendVertices_left_port (i : Fin (k+1)) (b : Bool) :
    appendVertices T U (Sum.inl (left T i b))=
      left (append T U) (i.castAdd (l+1)) b := by
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1)) (cast (congrArg Kind.Vertex (append_left T U i).symm) ((T i).left b)) = _
  congr 1
  exact cast_left (append_left T U i).symm b

@[simp] theorem appendVertices_right_port (i : Fin (k+1)) (b : Bool) :
    appendVertices T U (Sum.inl (right T i b))=
      right (append T U) (i.castAdd (l+1)) b := by
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1)) (cast (congrArg Kind.Vertex (append_left T U i).symm) ((T i).right b)) = _
  congr 1
  exact cast_right (append_left T U i).symm b

@[simp] theorem appendVertices_left_port' (i : Fin (l+1)) (b : Bool) :
    appendVertices T U (Sum.inr (left U i b))=
      left (append T U) (i.natAdd (k+1)) b := by
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1)) (cast (congrArg Kind.Vertex (append_right T U i).symm) ((U i).left b)) = _
  congr 1
  exact cast_left (append_right T U i).symm b

@[simp] theorem appendVertices_right_port' (i : Fin (l+1)) (b : Bool) :
    appendVertices T U (Sum.inr (right U i b))=
      right (append T U) (i.natAdd (k+1)) b := by
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1)) (cast (congrArg Kind.Vertex (append_right T U i).symm) ((U i).right b)) = _
  congr 1
  exact cast_right (append_right T U i).symm b

private theorem cast_src {t u : Kind} (h : t=u) (e : t.Edge) :
    u.src (cast (congrArg Kind.Edge h) e)=cast (congrArg Kind.Vertex h) (t.src e) := by
  cases h
  rfl

private theorem cast_dst {t u : Kind} (h : t=u) (e : t.Edge) :
    u.dst (cast (congrArg Kind.Edge h) e)=cast (congrArg Kind.Vertex h) (t.dst e) := by
  cases h
  rfl

theorem appendInnerEdges_src_left (e : InnerEdge T) :
    (chain (append T U)).src (Sum.inl (appendInnerEdges T U (Sum.inl e)))=
      appendVertices T U (Sum.inl ((chain T).src (Sum.inl e))) := by
  rcases e with ⟨i,e⟩
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1))
    ((append T U _).src (cast (congrArg Kind.Edge (append_left T U i).symm) e)) =
    Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1))
      (cast (congrArg Kind.Vertex (append_left T U i).symm) ((T i).src e))
  exact congrArg (Sigma.mk _) (cast_src (append_left T U i).symm e)

theorem appendInnerEdges_dst_left (e : InnerEdge T) :
    (chain (append T U)).dst (Sum.inl (appendInnerEdges T U (Sum.inl e)))=
      appendVertices T U (Sum.inl ((chain T).dst (Sum.inl e))) := by
  rcases e with ⟨i,e⟩
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1))
    ((append T U _).dst (cast (congrArg Kind.Edge (append_left T U i).symm) e)) =
    Sigma.mk (β := fun q => (append T U q).Vertex) (i.castAdd (l+1))
      (cast (congrArg Kind.Vertex (append_left T U i).symm) ((T i).dst e))
  exact congrArg (Sigma.mk _) (cast_dst (append_left T U i).symm e)

theorem appendInnerEdges_src_right (e : InnerEdge U) :
    (chain (append T U)).src (Sum.inl (appendInnerEdges T U (Sum.inr e)))=
      appendVertices T U (Sum.inr ((chain U).src (Sum.inl e))) := by
  rcases e with ⟨i,e⟩
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1))
    ((append T U _).src (cast (congrArg Kind.Edge (append_right T U i).symm) e)) =
    Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1))
      (cast (congrArg Kind.Vertex (append_right T U i).symm) ((U i).src e))
  exact congrArg (Sigma.mk _) (cast_src (append_right T U i).symm e)

theorem appendInnerEdges_dst_right (e : InnerEdge U) :
    (chain (append T U)).dst (Sum.inl (appendInnerEdges T U (Sum.inr e)))=
      appendVertices T U (Sum.inr ((chain U).dst (Sum.inl e))) := by
  rcases e with ⟨i,e⟩
  change Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1))
    ((append T U _).dst (cast (congrArg Kind.Edge (append_right T U i).symm) e)) =
    Sigma.mk (β := fun q => (append T U q).Vertex) (i.natAdd (k+1))
      (cast (congrArg Kind.Vertex (append_right T U i).symm) ((U i).dst e))
  exact congrArg (Sigma.mk _) (cast_dst (append_right T U i).symm e)

/-- Appending tile lists adds their physical weights. -/
theorem append_weight : weight (append T U)=weight T+weight U := by
  have h := Equiv.sum_comp
    (finSumFinEquiv : Fin (k+1) ⊕ Fin (l+1) ≃ Fin ((k+1)+(l+1)))
    (fun i => (append T U i).weight)
  simpa only [Fintype.sum_sum_type,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
    append_left,append_right] using h.symm

end Erdos1016.ExactMaximumSupport.MixedTiles

import Erdos1016.ExactMaximumSupport.MixedTiles

set_option autoImplicit false

/-!
# Glue two physical chains into a ring

The central pair joins corresponding rails. The closing pair has one Bool permutation.
The old physical labels remain separate from the four new interface labels.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k l : ℕ} (T : Fin (k+1) → Kind) (U : Fin (l+1) → Kind)

abbrev GluedVertex := Vertex T ⊕ Vertex U
abbrev GluedEdge := (ChainEdge T ⊕ ChainEdge U) ⊕ (Bool ⊕ Bool)

/-- First ends of the old labels and the two new pairs. -/
def gluedSrc : GluedEdge T U → GluedVertex T U
  | Sum.inl (Sum.inl e) => Sum.inl ((chain T).src e)
  | Sum.inl (Sum.inr e) => Sum.inr ((chain U).src e)
  | Sum.inr (Sum.inl b) => Sum.inr (right U (Fin.last l) b)
  | Sum.inr (Sum.inr b) => Sum.inl (right T (Fin.last k) b)

/-- Second ends include the single closing rail permutation. -/
def gluedDst (twist : Equiv.Perm Bool) : GluedEdge T U → GluedVertex T U
  | Sum.inl (Sum.inl e) => Sum.inl ((chain T).dst e)
  | Sum.inl (Sum.inr e) => Sum.inr ((chain U).dst e)
  | Sum.inr (Sum.inl b) => Sum.inl (left T 0 (twist b))
  | Sum.inr (Sum.inr b) => Sum.inr (left U 0 b)

/-- The exact physical network formed by the two chains and four interface labels. -/
def glued (twist : Equiv.Perm Bool) : Network (GluedVertex T U) (GluedEdge T U) where
  src := gluedSrc T U
  dst := gluedDst T U twist
  noLoops e := by
    rcases e with (e | e) | (b | b)
    · exact fun h => (chain T).noLoops e (Sum.inl.inj h)
    · exact fun h => (chain U).noLoops e (Sum.inr.inj h)
    · exact Sum.inr_ne_inl
    · exact Sum.inl_ne_inr

theorem glued_joins_left (twist : Equiv.Perm Bool) (e : ChainEdge T) :
    (glued T U twist).Joins (Sum.inl (Sum.inl e))
      (Sum.inl ((chain T).src e)) (Sum.inl ((chain T).dst e)) := Or.inl ⟨rfl,rfl⟩

theorem glued_joins_right (twist : Equiv.Perm Bool) (e : ChainEdge U) :
    (glued T U twist).Joins (Sum.inl (Sum.inr e))
      (Sum.inr ((chain U).src e)) (Sum.inr ((chain U).dst e)) := Or.inl ⟨rfl,rfl⟩

theorem glued_joins_closing (twist : Equiv.Perm Bool) (b : Bool) :
    (glued T U twist).Joins (Sum.inr (Sum.inl b))
      (Sum.inr (right U (Fin.last l) b)) (Sum.inl (left T 0 (twist b))) := Or.inl ⟨rfl,rfl⟩

theorem glued_joins_central (twist : Equiv.Perm Bool) (b : Bool) :
    (glued T U twist).Joins (Sum.inr (Sum.inr b))
      (Sum.inl (right T (Fin.last k) b)) (Sum.inr (left U 0 b)) := Or.inl ⟨rfl,rfl⟩

end Erdos1016.ExactMaximumSupport.MixedTiles

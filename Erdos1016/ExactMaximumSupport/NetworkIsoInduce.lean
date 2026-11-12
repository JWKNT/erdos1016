import Erdos1016.ExactMaximumSupport.NetworkIsoComposition
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false

/-!
# Restrict a physical isomorphism to vertex sets

The induced networks keep exactly the labels whose two ends survive.
The vertex equivalence and the physical-label equivalence both restrict.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkIso
open BoundaryTrace BoundaryTrace.Network

universe u v u' v'
variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
variable {N : Network V E} {N' : Network V' E'} (R : NetworkIso N N')

/-- An induced physical label survives exactly when its image survives. -/
theorem inside_iff (S : V → Prop) (S' : V' → Prop)
    (hS : ∀ v, S v ↔ S' (R.vertices v)) (e : E) :
    N.inside S e ↔ N'.inside S' (R.edges e) := by
  rcases R.joins e with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · simp only [Network.inside,hs,ht,← hS]
  · simp only [Network.inside,hs,ht,← hS,and_comm]

/-- Restrict the vertex and label maps to corresponding induced networks. -/
def induce (S : V → Prop) (S' : V' → Prop)
    (hS : ∀ v, S v ↔ S' (R.vertices v)) :
    NetworkIso (N.induce S) (N'.induce S') where
  vertices :=
    { toFun := fun v => ⟨R.vertices v.1,(hS v.1).mp v.2⟩
      invFun := fun v => ⟨R.vertices.symm v.1,(hS _).mpr (by
        rw [R.vertices.apply_symm_apply]
        exact v.2)⟩
      left_inv := fun v => Subtype.ext (R.vertices.symm_apply_apply v.1)
      right_inv := fun v => Subtype.ext (R.vertices.apply_symm_apply v.1) }
  edges :=
    { toFun := fun e => ⟨R.edges e.1,(R.inside_iff S S' hS e.1).mp e.2⟩
      invFun := fun e => ⟨R.edges.symm e.1,(R.inside_iff S S' hS _).mpr (by
        rw [R.edges.apply_symm_apply]
        exact e.2)⟩
      left_inv := fun e => Subtype.ext (R.edges.symm_apply_apply e.1)
      right_inv := fun e => Subtype.ext (R.edges.apply_symm_apply e.1) }
  joins e := by
    rcases R.joins e.1 with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨Subtype.ext hs,Subtype.ext ht⟩
    · exact Or.inr ⟨Subtype.ext hs,Subtype.ext ht⟩

@[simp] theorem induce_vertices (S : V → Prop) (S' : V' → Prop)
    (hS : ∀ v, S v ↔ S' (R.vertices v)) (v : {v // S v}) :
    ((R.induce S S' hS).vertices v).1=R.vertices v.1 := rfl

@[simp] theorem induce_edges (S : V → Prop) (S' : V' → Prop)
    (hS : ∀ v, S v ↔ S' (R.vertices v)) (e : {e // N.inside S e}) :
    ((R.induce S S' hS).edges e).1=R.edges e.1 := rfl

end Erdos1016.ExactMaximumSupport.NetworkIso

import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false

/-!
# Compose physical network relabelings

All vertex and physical-label equivalences compose. Edge orientation remains arbitrary.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkIso
open BoundaryTrace BoundaryTrace.Network
universe u v u' v' u'' v''
variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
variable {V'' : Type u''} {E'' : Type v''}
variable {N : Network V E} {N' : Network V' E'} {N'' : Network V'' E''}

/-- An arbitrary joined endpoint pair maps to the same unordered endpoint pair. -/
theorem map_joins (R : NetworkIso N N') {e : E} {a b : V} (h : N.Joins e a b) :
    N'.Joins (R.edges e) (R.vertices a) (R.vertices b) := by
  have hj := R.joins e
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simpa only [ha,hb] using hj
  · simpa only [ha,hb] using hj.symm

/-- Compose two exact physical isomorphisms. -/
def trans (R : NetworkIso N N') (S : NetworkIso N' N'') : NetworkIso N N'' where
  vertices := R.vertices.trans S.vertices
  edges := R.edges.trans S.edges
  joins e := S.map_joins (R.joins e)

@[simp] theorem trans_vertices (R : NetworkIso N N') (S : NetworkIso N' N'') (a : V) :
    (R.trans S).vertices a=S.vertices (R.vertices a) := rfl

@[simp] theorem trans_edges (R : NetworkIso N N') (S : NetworkIso N' N'') (e : E) :
    (R.trans S).edges e=S.edges (R.edges e) := rfl

end Erdos1016.ExactMaximumSupport.NetworkIso

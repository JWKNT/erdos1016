import Erdos1016.Graph.PathExpansion.Basic

set_option autoImplicit false

/-!
# Interior degree-two paths force cycle-word constancy

The abstract route system in `PathExpansion` has no ordering of its support
edges. This module adds a path witness. Its `twoIncidence` field is the exact
linear boundary identity supplied by the graph-construction fact that an
interior path vertex has precisely the two consecutive route-edge incidence
slots (one slot from each edge). It is stated for every edge word, so it is
strong enough to expose that fact without hiding a construction-specific
degree argument in the proof below.
-/

noncomputable section

namespace Erdos1016
namespace FiniteMultiGraph

variable {A P : FiniteMultiGraph}

/-- One oriented traversal of a physical edge. The edge itself retains the
orientation stored by the multigraph; a path step may traverse it either way.
-/
structure PathStep (P : FiniteMultiGraph) where
  startVertex : P.Vertex
  edge : P.Edge
  endVertex : P.Vertex
  endpoints :
    (P.src edge = startVertex ∧ P.dst edge = endVertex) ∨
    (P.dst edge = startVertex ∧ P.src edge = endVertex)

/-- Two consecutive steps share their middle vertex, and that vertex sees
exactly their two incidence contributions in the boundary of any edge word.
The second conjunct is the algebraic form of the exact two-incidence
condition; it implies equality of the two edge coefficients for every cycle.
-/
def PathStep.Link (s t : PathStep P) : Prop :=
  s.endVertex = t.startVertex ∧
    ∀ y : P.EdgeWord,
      P.boundary y s.endVertex = y s.edge + y t.edge

/-- Ordered paths attached to the supports of an existing route system.
`chain` makes successive steps meet; `start` and `finish` say the path joins
the mapped endpoints of the auxiliary edge. `support_eq` identifies its edge
set with the route support. -/
structure PathBearingRouteSystem (R : EdgeDisjointRouteSystem A P) where
  steps : A.Edge → List (PathStep P)
  nonempty : ∀ e, steps e ≠ []
  chain : ∀ e, List.Chain' PathStep.Link (steps e)
  support_eq : ∀ e, ((steps e).map PathStep.edge).toFinset = R.support e
  start : ∀ e, ∃ s, (steps e).head? = some s ∧
    s.startVertex = R.vertexMap (A.src e)
  finish : ∀ e, ∃ s, (steps e).getLast? = some s ∧
    s.endVertex = R.vertexMap (A.dst e)

namespace PathBearingRouteSystem

variable (R : EdgeDisjointRouteSystem A P)

/-- A cycle word has equal coefficients on the two edges of every path link.
-/
theorem link_eq_of_cycle (s t : PathStep P)
    (hst : PathStep.Link s t) (y : P.EdgeWord) (hy : y ∈ P.CycleSpace) :
    y s.edge = y t.edge := by
  have hzero : P.boundary y s.endVertex = 0 := congrFun hy s.endVertex
  rw [hst.2 y] at hzero
  have hneg : -(y t.edge) = y t.edge := by
    have hz : ∀ z : F₂, -z = z := by
      intro z
      fin_cases z <;> decide
    exact hz _
  have hab := eq_neg_of_add_eq_zero_left hzero
  rw [hneg] at hab
  exact hab

/-- Along a linked step list, a cycle word takes the same value on every
step edge. -/
theorem chain_edges_eq (y : P.EdgeWord) (hy : y ∈ P.CycleSpace) :
    ∀ (l : List (PathStep P)), List.Chain' PathStep.Link l →
      ∀ s ∈ l, ∀ t ∈ l, y s.edge = y t.edge := by
  intro l
  induction l with
  | nil =>
      intro _ s hs
      simp at hs
  | cons a l ih =>
      intro hc s hs t ht
      rcases List.mem_cons.mp hs with hs | hs
      · subst s
        rcases List.mem_cons.mp ht with ht | ht
        · subst t
          rfl
        · cases l with
          | nil => simp at ht
          | cons b tail =>
              have hab := (List.chain'_cons.mp hc).1
              have hcb := (List.chain'_cons.mp hc).2
              calc
                y a.edge = y b.edge := link_eq_of_cycle a b hab y hy
                _ = y t.edge := ih hcb b (by simp) t ht
      · rcases List.mem_cons.mp ht with ht | ht
        · subst t
          cases l with
          | nil => simp at hs
          | cons b tail =>
              have hab := (List.chain'_cons.mp hc).1
              have hcb := (List.chain'_cons.mp hc).2
              calc
                y s.edge = y b.edge := ih hcb s hs b (by simp)
                _ = y a.edge := (link_eq_of_cycle a b hab y hy).symm
        · cases l with
          | nil => simp at hs
          | cons b tail =>
              exact ih (List.chain'_cons.mp hc).2 s hs t ht

/-- Any physical cycle word is constant across the entire support of each
path-bearing route. This is the `hconstant` premise accepted by
`cycleExpandEquiv`. -/
theorem cycle_word_constant_on_support
    (Q : PathBearingRouteSystem R)
    (y : P.EdgeWord) (hy : y ∈ P.CycleSpace) :
    ∀ e p q, p ∈ R.support e → q ∈ R.support e → y p = y q := by
  classical
  intro e p q hp hq
  have hp' : p ∈ (Q.steps e).map PathStep.edge := by
    have hfin : p ∈ ((Q.steps e).map PathStep.edge).toFinset := by
      rw [Q.support_eq e]
      exact hp
    exact List.mem_toFinset.mp hfin
  have hq' : q ∈ (Q.steps e).map PathStep.edge := by
    have hfin : q ∈ ((Q.steps e).map PathStep.edge).toFinset := by
      rw [Q.support_eq e]
      exact hq
    exact List.mem_toFinset.mp hfin
  rcases List.mem_map.mp hp' with ⟨s, hs, rfl⟩
  rcases List.mem_map.mp hq' with ⟨t, ht, rfl⟩
  exact chain_edges_eq y hy (Q.steps e) (Q.chain e) s hs t ht

end PathBearingRouteSystem

end FiniteMultiGraph
end Erdos1016

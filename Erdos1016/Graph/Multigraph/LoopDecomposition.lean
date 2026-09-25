import Erdos1016.Graph.Multigraph.Components
import Erdos1016.CycleSpace.Incidence

set_option autoImplicit false

/-!
# Removing independent loop coordinates

A loop has zero binary boundary. Thus the cycle space of a labelled
multigraph is the product of its free loop bits and the cycle space of the
loopless network. The projection preserves the uniform law and every event
that depends only on nonloop coordinates, including cut-zero events.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph
open BoundaryTrace

abbrev LoopEdge (G : FiniteMultiGraph) := {e : G.Edge // G.src e = G.dst e}
abbrev NonloopEdge (G : FiniteMultiGraph) := {e : G.Edge // G.src e ≠ G.dst e}

/-- The same vertices and exactly the nonloop labelled edges. Parallel edges remain. -/
def looplessNetwork (G : FiniteMultiGraph) : Network G.Vertex (NonloopEdge G) where
  src e := G.src e.1
  dst e := G.dst e.1
  noLoops e := e.2

/-- Discard the loop coordinates of an edge word. -/
def nonloopWord (G : FiniteMultiGraph) (x : G.EdgeWord) : (looplessNetwork G).Word :=
  fun e => x e.1

/-- Put the independent loop coordinates back into a word. -/
def joinLoopWord (G : FiniteMultiGraph) (l : LoopEdge G → F₂)
    (x : (looplessNetwork G).Word) : G.EdgeWord :=
  fun e => if h : G.src e = G.dst e then l ⟨e, h⟩ else x ⟨e, h⟩

/-- Loops cancel in the binary incidence boundary. -/
theorem nonloopWord_boundary (G : FiniteMultiGraph) (x : G.EdgeWord) :
    (looplessNetwork G).boundary (nonloopWord G x) = G.boundary x := by
  classical
  funext v
  let f : G.Edge → F₂ := fun e =>
    (if G.src e = v then x e else 0) + (if G.dst e = v then x e else 0)
  have hloop : (∑ e : LoopEdge G, f e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp [f, e.2, bit_add_self]
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun e : G.Edge => G.src e = G.dst e) f
  rw [hloop, zero_add] at hsum
  rw [Network.boundary_apply, ← Finset.sum_add_distrib]
  calc
    _ = ∑ e : NonloopEdge G, f e.1 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hs : G.src e.1 = v <;> by_cases hd : G.dst e.1 = v <;>
        simp [looplessNetwork, nonloopWord, f, hs, hd]
    _ = ∑ e, f e := hsum
    _ = _ := rfl

@[simp] theorem nonloopWord_joinLoopWord (G : FiniteMultiGraph)
    (l : LoopEdge G → F₂) (x : (looplessNetwork G).Word) :
    nonloopWord G (joinLoopWord G l x) = x := by
  funext e
  simp [nonloopWord, joinLoopWord, e.2]

/-- The exact product decomposition of the cycle space. -/
def loopCycleSpaceEquiv (G : FiniteMultiGraph) :
    G.CycleSpace ≃ₗ[F₂] (LoopEdge G → F₂) × (looplessNetwork G).CycleSpace where
  toFun x := (fun e => x.1 e.1, ⟨nonloopWord G x.1, by
    rw [LinearMap.mem_ker, nonloopWord_boundary]
    exact x.2⟩)
  invFun q := ⟨joinLoopWord G q.1 q.2.1, by
    rw [LinearMap.mem_ker, ← nonloopWord_boundary, nonloopWord_joinLoopWord]
    exact q.2.2⟩
  left_inv x := by
    apply Subtype.ext
    funext e
    simp only [joinLoopWord, nonloopWord]
    split <;> rfl
  right_inv q := by
    apply Prod.ext
    · funext e
      simp [joinLoopWord, e.2]
    · apply Subtype.ext
      exact nonloopWord_joinLoopWord G q.1 q.2.1
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

@[simp] theorem loopCycleSpaceEquiv_nonloop (G : FiniteMultiGraph) (x : G.CycleSpace)
    (e : NonloopEdge G) : ((loopCycleSpaceEquiv G x).2).1 e = x.1 e.1 := rfl

@[simp] theorem loopCycleSpaceEquiv_loop (G : FiniteMultiGraph) (x : G.CycleSpace)
    (e : LoopEdge G) : (loopCycleSpaceEquiv G x).1 e = x.1 e.1 := rfl

/-- Removing loops does not alter adjacency or any vertex-component count. -/
theorem looplessNetwork_graph (G : FiniteMultiGraph) :
    (looplessNetwork G).graph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨e, h | h⟩
    · refine ⟨?_, e.1, Or.inl h⟩
      intro huv
      exact e.2 (h.1.trans (huv.trans h.2.symm))
    · refine ⟨?_, e.1, Or.inr h⟩
      intro huv
      exact e.2 (h.1.trans (huv.symm.trans h.2.symm))
  · rintro ⟨huv, e, h | h⟩
    · refine ⟨⟨e, ?_⟩, Or.inl h⟩
      intro he
      exact huv (h.1.symm.trans (he.trans h.2))
    · refine ⟨⟨e, ?_⟩, Or.inr h⟩
      intro he
      exact huv (h.2.symm.trans (he.symm.trans h.1))

/-- Every event on the nonloop cycle coordinates retains its exact uniform probability. -/
theorem density_loopless_projection (G : FiniteMultiGraph)
    (P : (looplessNetwork G).CycleSpace → Prop) :
    Finite.density (fun x : G.CycleSpace => P ((loopCycleSpaceEquiv G x).2)) =
      Finite.density P := by
  let f : G.CycleSpace →ₗ[F₂] (looplessNetwork G).CycleSpace :=
    (LinearMap.snd F₂ (LoopEdge G → F₂) (looplessNetwork G).CycleSpace).comp
      (loopCycleSpaceEquiv G).toLinearMap
  have hf : Function.Surjective f := by
    intro x
    refine ⟨(loopCycleSpaceEquiv G).symm (0, x), ?_⟩
    change ((loopCycleSpaceEquiv G) ((loopCycleSpaceEquiv G).symm (0, x))).2 = x
    rw [LinearEquiv.apply_symm_apply]
  exact density_surjective_linear f hf P

end Erdos1016.FiniteMultiGraph

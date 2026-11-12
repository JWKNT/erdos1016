import Erdos1016.ExactMaximum.NetMinimal

set_option autoImplicit false

/-!
# The network of a set of edges

A part of a network is the network of the edges that satisfy a predicate, on the same vertices.
A word of the part is a word of the network when it is extended by zero. This file proves that
the boundary commutes with this extension, and one consequence that later files use in the place
of explicit walks:

* if two vertices are joined by edges of a word `x`, some sub-word of `x` has odd degree exactly
  at these two vertices (`exists_join_of_reachable`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netSubDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The network of the edges that satisfy `p`. -/
def sub (N : Network V E) (p : E → Prop) : Network V {e : E // p e} where
  src e := N.src e.1
  dst e := N.dst e.1
  noLoops e := N.noLoops e.1

/-- A word on the edges that satisfy `p`, extended by zero to all edges. -/
def extend (p : E → Prop) (y : {e : E // p e} → Bit) : E → Bit :=
  fun e => if h : p e then y ⟨e, h⟩ else 0

omit [Fintype V] [Fintype E] in
theorem extend_apply_of_pos (p : E → Prop) (y : {e : E // p e} → Bit) {e : E} (h : p e) :
    extend p y e = y ⟨e, h⟩ := dif_pos h

omit [Fintype V] [Fintype E] in
theorem extend_apply_of_neg (p : E → Prop) (y : {e : E // p e} → Bit) {e : E} (h : ¬ p e) :
    extend p y e = 0 := dif_neg h

omit [Fintype V] [Fintype E] in
/-- An edge of the extended word satisfies `p`. -/
theorem prop_of_extend_ne_zero (p : E → Prop) (y : {e : E // p e} → Bit) {e : E}
    (h : extend p y e ≠ 0) : p e :=
  Classical.not_not.1 fun hp => h (extend_apply_of_neg p y hp)

omit [Fintype V] in
/-- A sum over all edges of a function that vanishes outside `p` is a sum over the part. -/
theorem sum_eq_sum_sub {M : Type*} [AddCommMonoid M] (p : E → Prop) [Fintype {e : E // p e}]
    (g : E → M)
    (hg : ∀ e, ¬ p e → g e = 0) : ∑ e, g e = ∑ e : {e : E // p e}, g e.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro x; simp) g]
  symm
  apply Finset.sum_filter_of_ne
  intro e _ hne
  exact Classical.not_not.1 fun hp => hne (hg e hp)

/-- The boundary commutes with the extension by zero. The statement holds for every `Fintype`
instance on the subtype, so that it applies whatever instance Lean finds for a given `p`. -/
theorem boundary_extend (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (y : {e : E // p e} → Bit) :
    N.boundary (extend p y) = (N.sub p).boundary y := by
  funext v
  rw [boundary_apply, boundary_apply]
  have h1 : (∑ e, if N.src e = v then extend p y e else 0) =
      ∑ e : {e : E // p e}, if (N.sub p).src e = v then y e else 0 := by
    rw [sum_eq_sum_sub p (fun e => if N.src e = v then extend p y e else 0)]
    · apply Finset.sum_congr rfl
      intro e _
      show (if N.src e.1 = v then extend p y e.1 else 0) = if N.src e.1 = v then y e else 0
      rw [extend_apply_of_pos p y e.2]
    · intro e he
      rw [extend_apply_of_neg p y he]
      simp
  have h2 : (∑ e, if N.dst e = v then extend p y e else 0) =
      ∑ e : {e : E // p e}, if (N.sub p).dst e = v then y e else 0 := by
    rw [sum_eq_sum_sub p (fun e => if N.dst e = v then extend p y e else 0)]
    · apply Finset.sum_congr rfl
      intro e _
      show (if N.dst e.1 = v then extend p y e.1 else 0) = if N.dst e.1 = v then y e else 0
      rw [extend_apply_of_pos p y e.2]
    · intro e he
      rw [extend_apply_of_neg p y he]
      simp
  rw [h1, h2]

omit [Fintype V] [Fintype E] in
/-- The graph of the network of the edges of `x` is the graph that `x` selects. -/
theorem sub_support_graph (N : Network V E) (x : N.Word) :
    (N.sub fun e => x e ≠ 0).graph = N.selectedGraph x := by
  ext u w
  constructor
  · rintro ⟨e, h⟩
    exact ⟨e.1, e.2, h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨⟨e, he⟩, h⟩

/-- If two vertices are joined by edges of `x`, some sub-word of `x` has odd degree exactly at
these two vertices. If the two vertices are equal, the sub-word is even. -/
theorem exists_join_of_reachable (N : Network V E) (x : N.Word) {u w : V}
    (h : (N.selectedGraph x).Reachable u w) :
    ∃ y : N.Word, N.IsSubword y x ∧ N.boundary y = unitWord u + unitWord w := by
  have h' : (N.sub fun e => x e ≠ 0).graph.Reachable u w := by
    rw [sub_support_graph]
    exact h
  obtain ⟨p⟩ := h'
  obtain ⟨y', hy'⟩ := (N.sub fun e => x e ≠ 0).pair_mem_range_of_walk p
  refine ⟨extend (fun e => x e ≠ 0) y', ?_, ?_⟩
  · intro e he
    exact prop_of_extend_ne_zero _ y' he
  · rw [boundary_extend]
    exact hy'

end Erdos1016.BoundaryTrace.Network

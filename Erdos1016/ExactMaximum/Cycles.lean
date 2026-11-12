import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Graph.Multigraph.RegionDegrees

set_option autoImplicit false

/-!
# Cycles of a finite multigraph

The paper "The maximum number of cycles in a graph of large rank" counts the cycles of connected
cubic multigraphs. This file defines a cycle of a `FiniteMultiGraph` as an edge word and proves
the first facts:

* the boundary of an edge word at a vertex is the selected degree modulo two;
* a cycle is a nonzero element of the cycle space;
* a multigraph of cycle rank `r` has fewer than `2^r` cycles.

A loop is a cycle of length one, and two parallel edges form a cycle of length two.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.FiniteMultiGraph

variable (G : FiniteMultiGraph)

/-- A cycle of a multigraph, as an edge word: the word is not zero, every vertex has selected
degree zero or two (a loop counts twice), and any two vertices of positive selected degree are
joined by selected edges. -/
def IsCycleWord (x : G.EdgeWord) : Prop :=
  x ≠ 0 ∧ (∀ v, G.selectedDegree x v = 0 ∨ G.selectedDegree x v = 2) ∧
  ∀ u v, 0 < G.selectedDegree x u → 0 < G.selectedDegree x v →
    (G.selectedGraph x).Reachable u v

/-- The number of cycles of a multigraph. -/
def numCycles : ℕ := Nat.card {x : G.EdgeWord // G.IsCycleWord x}

/-- Every vertex has degree three. -/
def IsCubic : Prop := ∀ v, G.degree v = 3

/-- Some edge is a loop. -/
def HasLoop : Prop := ∃ e, G.src e = G.dst e

/-- The number of edges of an edge word. -/
def wordLength (x : G.EdgeWord) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : G.Edge => x e ≠ 0).card

/-- All selected edges have both ends in `U`. -/
def SupportedIn (x : G.EdgeWord) (U : Finset G.Vertex) : Prop :=
  ∀ e, x e ≠ 0 → G.src e ∈ U ∧ G.dst e ∈ U

/-- The subgraph induced on `U` contains a cycle. -/
def HasCycleIn (U : Finset G.Vertex) : Prop :=
  ∃ x, G.IsCycleWord x ∧ G.SupportedIn x U

/-- The edges that leave `U` form a cyclic cut: both sides contain a cycle. -/
def IsCyclicCut (U : Finset G.Vertex) : Prop :=
  G.HasCycleIn U ∧ G.HasCycleIn Uᶜ

/-- There is a cyclic cut with at most `k` edges. -/
def HasCyclicCutLE (k : ℕ) : Prop :=
  ∃ U : Finset G.Vertex, G.IsCyclicCut U ∧ (G.cutEdges U).card ≤ k

/-- There is a cycle with fewer than `D` edges. -/
def HasCycleShorterThan (D : ℕ) : Prop :=
  ∃ x, G.IsCycleWord x ∧ G.wordLength x < D

variable {G}

/-- An element of `F₂` is zero or one. -/
theorem f2_eq_zero_or_one (a : F₂) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- The boundary at a vertex is the selected degree modulo two. -/
theorem boundary_apply_eq_selectedDegree (x : G.EdgeWord) (v : G.Vertex) :
    G.boundary x v = ((G.selectedDegree x v : ℕ) : F₂) := by
  classical
  rw [G.selectedDegree_eq_sum_endpoints x v, Nat.cast_sum]
  show (∑ e, ((if G.src e = v then x e else 0) + (if G.dst e = v then x e else 0))) = _
  apply Finset.sum_congr rfl
  intro e _
  rcases f2_eq_zero_or_one (x e) with hx | hx <;> by_cases hs : G.src e = v <;>
    by_cases ht : G.dst e = v <;> (simp [hx, hs, ht]; try rfl)

/-- A selected edge gives its first end a positive selected degree. -/
theorem selectedDegree_src_pos {x : G.EdgeWord} {f : G.Edge} (hf : x f ≠ 0) :
    0 < G.selectedDegree x (G.src f) := by
  classical
  rw [G.selectedDegree_eq_sum_endpoints]
  refine Nat.lt_of_lt_of_le ?_
    (Finset.single_le_sum (fun e _ => Nat.zero_le _) (Finset.mem_univ f))
  rw [if_pos hf, if_pos rfl]
  omega

/-- A selected edge gives its second end a positive selected degree. -/
theorem selectedDegree_dst_pos {x : G.EdgeWord} {f : G.Edge} (hf : x f ≠ 0) :
    0 < G.selectedDegree x (G.dst f) := by
  classical
  rw [G.selectedDegree_eq_sum_endpoints]
  refine Nat.lt_of_lt_of_le ?_
    (Finset.single_le_sum (fun e _ => Nat.zero_le _) (Finset.mem_univ f))
  rw [if_pos hf, if_pos rfl]
  omega

/-- A vertex of positive selected degree is an end of a selected edge. -/
theorem exists_edge_of_selectedDegree_pos {x : G.EdgeWord} {v : G.Vertex}
    (h : 0 < G.selectedDegree x v) : ∃ e, x e ≠ 0 ∧ (G.src e = v ∨ G.dst e = v) := by
  classical
  rw [G.selectedDegree_eq_sum_endpoints] at h
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.1 h)
  by_cases hx : x e ≠ 0
  · refine ⟨e, hx, ?_⟩
    rw [if_pos hx] at he
    by_cases hs : G.src e = v
    · exact Or.inl hs
    · by_cases ht : G.dst e = v
      · exact Or.inr ht
      · rw [if_neg hs, if_neg ht] at he
        exact absurd rfl he
  · rw [if_neg hx] at he
    exact absurd rfl he

/-- A cycle has zero boundary. -/
theorem IsCycleWord.boundary_eq_zero {x : G.EdgeWord} (hx : G.IsCycleWord x) :
    G.boundary x = 0 := by
  funext v
  rw [boundary_apply_eq_selectedDegree]
  rcases hx.2.1 v with h | h <;> rw [h] <;> rfl

/-- A cycle is an element of the cycle space. -/
def IsCycleWord.toCycleSpace {x : G.EdgeWord} (hx : G.IsCycleWord x) : G.CycleSpace :=
  ⟨x, LinearMap.mem_ker.2 hx.boundary_eq_zero⟩

instance : Finite {x : G.EdgeWord // G.IsCycleWord x} := Subtype.finite

/-- A multigraph of cycle rank `r` has fewer than `2^r` cycles. -/
theorem numCycles_lt_two_pow (G : FiniteMultiGraph) : G.numCycles < 2 ^ G.cycleRank := by
  classical
  have hinj : Function.Injective
      (fun o : Option {x : G.EdgeWord // G.IsCycleWord x} =>
        (match o with
          | none => (0 : G.CycleSpace)
          | some x => x.2.toCycleSpace)) := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exfalso
      have h := congrArg Subtype.val hab
      exact b.2.1 h.symm
    · exfalso
      have h := congrArg Subtype.val hab
      exact a.2.1 h
    · have h := congrArg Subtype.val hab
      exact congrArg some (Subtype.ext h)
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hZ : Nat.card G.CycleSpace = 2 ^ G.cycleRank := by
    rw [Nat.card_eq_fintype_card, cycleSpace_card]
  rw [hZ, Finite.card_option] at hcard
  unfold numCycles
  omega

end Erdos1016.FiniteMultiGraph

import Erdos1016.Extremal.Construction.BinarySubsetSums

set_option autoImplicit false

/-!
# Graph-level closing step for binary shortcuts

The length arithmetic in `BinaryShortcut` applies after a shortcut-chain path
has been realized in a graph. This file formalizes the graph-theoretic closing
step and isolates the remaining geometric input as a family of simple paths.
-/

namespace Erdos1016.Extremal

open SimpleGraph

/-- A simple path together with a new edge between its endpoints gives a cycle.
The edge-disjointness premise says that the closing edge is not already on the
path. -/
theorem cycle_of_path_and_closing_edge {V : Type*} (G : SimpleGraph V)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hclose : G.Adj v u)
    (hnew : s(v, u) ∉ p.edges) :
    (Walk.cons hclose p).IsCycle := by
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp, ?_⟩
  simpa [Walk.edges_reverse] using hnew

/-- Two vertex-disjoint-after-the-joint-endpoint simple paths concatenate to a
simple path. `support_disjoint` is the precise condition used when composing
successive shortcut segments. -/
theorem isPath_append_of_support_disjoint {V : Type*} (G : SimpleGraph V)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
    (hp : p.IsPath) (hq : q.IsPath)
    (support_disjoint : ∀ x ∈ p.support, x ∉ q.support.tail) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  apply List.nodup_append.mpr
  have hqnod := hq.support_nodup
  have hqt : q.support.tail.Nodup := by
    rw [Walk.support_eq_cons q] at hqnod
    exact List.Nodup.of_cons hqnod
  refine ⟨hp.support_nodup, hqt, ?_⟩
  intro x hx hx'
  exact support_disjoint x hx hx'

/-- The cycle made by closing a path has the path length plus one. -/
theorem length_cycle_of_path_and_closing_edge {V : Type*} (G : SimpleGraph V)
    {u v : V} (p : G.Walk u v) (hclose : G.Adj v u) :
    (Walk.cons hclose p).length = p.length + 1 := by
  simp [Walk.length_cons, Walk.length_reverse]

/-- Abstract graph-level form of the interval conclusion in the binary-chain
lemma. The only construction-specific premise is a simple path of every
arithmetic length in the interval, avoiding the closing edge. -/
theorem cycle_interval_of_path_family {V : Type*} [Fintype V]
    (G : SimpleGraph V) (j : ℕ) {u v : V} (hclose : G.Adj v u)
    (paths : ∀ ℓ, j ≤ ℓ → ℓ < j + 2 ^ j →
      ∃ p : G.Walk u v, p.IsPath ∧ p.length = ℓ ∧ s(v, u) ∉ p.edges)
    (c : ℕ) (hlo : j + 1 ≤ c) (hhi : c ≤ 2 ^ j + j) :
    Erdos1016.Problem1016.HasCycleLength G c := by
  obtain ⟨p, hp, hlen, hnew⟩ := paths (c - 1) (by omega) (by omega)
  refine ⟨v, Walk.cons hclose p, ?_, ?_⟩
  · exact cycle_of_path_and_closing_edge G p hp hclose hnew
  · rw [length_cycle_of_path_and_closing_edge G p hclose, hlen]
    omega

end Erdos1016.Extremal

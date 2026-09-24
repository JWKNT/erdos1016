import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

namespace Erdos1016.Proof.ClosedGraphEmbeddingAcyclic

/-- Lift walks through an injective graph embedding when its image is closed
under adjacency. The equality records every step, including its labels. -/
theorem lift_walk {α β : Type*} {H : SimpleGraph α} {K : SimpleGraph β}
    (f : H ↪g K) (hclosed : ∀ a b, K.Adj (f a) b → ∃ a', f a' = b)
    {x y : β} (p : K.Walk x y) :
    ∀ a b (ha : f a = x) (hb : f b = y),
      ∃ q : H.Walk a b, (q.map f.toHom).copy ha hb = p := by
  induction p with
  | @nil u =>
      intro a b ha hb
      have hab : a = b := f.injective (ha.trans hb.symm)
      subst b
      subst u
      exact ⟨.nil, rfl⟩
  | @cons x y z hxy p ih =>
      intro a b ha hb
      obtain ⟨m, hm⟩ := hclosed a y (ha ▸ hxy)
      obtain ⟨q, hq⟩ := ih m b hm hb
      have ham : H.Adj a m := f.map_adj_iff.mp (by simpa [ha, hm] using hxy)
      refine ⟨.cons ham q, ?_⟩
      subst x
      subst y
      subst z
      simpa using congrArg (fun p => SimpleGraph.Walk.cons hxy p) hq

/-- Adding isolated vertices to an embedded acyclic graph preserves
acyclicity. Every edge, rather than every ambient vertex, must be embedded. -/
theorem acyclic {α β : Type*} {H : SimpleGraph α} {K : SimpleGraph β}
    (f : H ↪g K)
    (hends : ∀ a b, K.Adj a b → ∃ u v, f u = a ∧ f v = b)
    (hH : H.IsAcyclic) : K.IsAcyclic := by
  have hclosed : ∀ a b, K.Adj (f a) b → ∃ a', f a' = b := by
    intro a b hab
    obtain ⟨_, v, _, hv⟩ := hends (f a) b hab
    exact ⟨v, hv⟩
  intro x p hp
  have hx : ∃ a, f a = x := by
    cases p with
    | nil => exact (hp.not_nil (by constructor)).elim
    | cons h p => obtain ⟨a, _, ha, _⟩ := hends _ _ h; exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hx
  obtain ⟨q, hq⟩ := lift_walk f hclosed p a a ha ha
  have hqcycle : q.IsCycle := by
    apply (SimpleGraph.Walk.map_isCycle_iff_of_injective (f := f.toHom) f.injective).mp
    subst x
    have hq' : q.map f.toHom = p := by simpa using hq
    rw [hq']
    exact hp
  exact hH q hqcycle

end Erdos1016.Proof.ClosedGraphEmbeddingAcyclic

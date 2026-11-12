import Erdos1016.ExactMaximum.PoleSides
import Erdos1016.ExactMaximum.NetCutRank
import Erdos1016.ExactMaximum.NetBridgeCut
import Erdos1016.ExactMaximum.SmallCutCase
import Erdos1016.ExactMaximum.CountTools

set_option autoImplicit false

/-!
# The component of a vertex in a part of a network

The proof of Theorem 7.1 of the paper "The maximum number of cycles in a graph of large rank"
deletes vertices of a shortest cycle one by one and looks at a component `K` of what remains.
This file has the facts about such a component that do not depend on the cycle. Let `q` be a set
of edges of a network `N`, and let `a` be a vertex. `compEdges q a` is the set of the edges of
`q` in the component of `a` in the network of `q`, and `K` is its network.

* `isWeakPole_compEdges`: if the vertices of the component have degree two or three in `q`, then
  `K` is a pole (with isolated vertices).
* `natCard_ports_compEdges_le`: in a cubic network, `K` has at most twice as many ports as there
  are edges outside `q`.
* `rank_compEdges_add_le`: the rank of `K` plus the number of edges outside `q` is at most the
  rank of `N` plus the number of isolated vertices of `q` outside the component, if `N` is
  connected and every vertex outside the component has degree zero or at least two in `q`.
  This is the count of the step "The rank of `K_p`" of the paper.
* `false_of_shore`: a cubic cyclic shore of the network of a set of edges of a cubic network `N`
  is a cyclic cut of `N` with at most four crossing edges.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance exitPoleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The edges of `q` in the component of the vertex `a` of the network of `q`. -/
def compEdges (N : Network V E) (q : E → Prop) (a : V) (g : E) : Prop :=
  q g ∧ (N.sub q).graph.Reachable a (N.src g)

omit [Fintype V] [Fintype E] in
/-- The two ends of an edge of `q` are in the same component. -/
theorem reachable_src_iff_dst (N : Network V E) (q : E → Prop) (a : V) {g : E} (hg : q g) :
    (N.sub q).graph.Reachable a (N.src g) ↔ (N.sub q).graph.Reachable a (N.dst g) := by
  have hadj : (N.sub q).graph.Adj (N.src g) (N.dst g) := ⟨⟨g, hg⟩, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩

omit [Fintype V] [Fintype E] in
/-- A vertex of the component of `a` is joined to `a` by edges of the component. -/
theorem reachable_compEdges (N : Network V E) (q : E → Prop) (a : V) {v : V}
    (h : (N.sub q).graph.Reachable a v) : (N.sub (N.compEdges q a)).graph.Reachable a v := by
  have hmono : ∀ {b : V}, (N.sub (N.compEdges q a)).graph.Reachable a b →
      (N.sub q).graph.Reachable a b := fun hb => N.reachable_sub_mono (fun g hg => hg.1) hb
  refine (N.sub q).mem_of_reachable_of_closed
    (fun v => (N.sub (N.compEdges q a)).graph.Reachable a v) ?_ h (SimpleGraph.Reachable.refl a)
  intro e
  constructor
  · intro hs
    have hce : N.compEdges q a e.1 := ⟨e.2, hmono hs⟩
    have hadj : (N.sub (N.compEdges q a)).graph.Adj (N.src e.1) (N.dst e.1) :=
      ⟨⟨e.1, hce⟩, Or.inl ⟨rfl, rfl⟩⟩
    exact SimpleGraph.Reachable.trans hs hadj.reachable
  · intro hd
    have hce : N.compEdges q a e.1 := ⟨e.2, (N.reachable_src_iff_dst q a e.2).2 (hmono hd)⟩
    have hadj : (N.sub (N.compEdges q a)).graph.Adj (N.src e.1) (N.dst e.1) :=
      ⟨⟨e.1, hce⟩, Or.inl ⟨rfl, rfl⟩⟩
    exact SimpleGraph.Reachable.trans hd hadj.symm.reachable

omit [Fintype V] in
/-- A vertex of the component has the same degree in the component as in `q`. -/
theorem deg_compEdges_of_reachable (N : Network V E) (q : E → Prop) (a : V) {v : V}
    (h : (N.sub q).graph.Reachable a v) :
    (N.sub (N.compEdges q a)).deg (fun _ => 1) v = (N.sub q).deg (fun _ => 1) v := by
  rw [N.deg_sub_ones, N.deg_sub_ones]
  apply N.deg_congr
  intro g hg
  rw [restrict_ne_zero_iff, restrict_ne_zero_iff]
  constructor
  · intro hh
    exact ⟨hh.1.1, hh.2⟩
  · intro hh
    refine ⟨⟨hh.1, ?_⟩, hh.2⟩
    rcases hg with hg | hg
    · rw [hg]
      exact h
    · apply (N.reachable_src_iff_dst q a hh.1).2
      rw [hg]
      exact h

omit [Fintype V] in
/-- A vertex outside the component has degree zero in the component. -/
theorem deg_compEdges_of_not_reachable (N : Network V E) (q : E → Prop) (a : V) {v : V}
    (h : ¬ (N.sub q).graph.Reachable a v) :
    (N.sub (N.compEdges q a)).deg (fun _ => 1) v = 0 := by
  rw [N.deg_sub_ones]
  apply N.deg_eq_zero_of_forall
  intro g hg
  apply restrict_apply_of_neg
  intro hc
  apply h
  rcases hg with hg | hg
  · rw [← hg]
    exact hc.2
  · rw [← hg]
    exact (N.reachable_src_iff_dst q a hc.1).1 hc.2

omit [Fintype V] in
/-- **The component is a pole**, if its vertices have degree two or three in `q`. -/
theorem isWeakPole_compEdges (N : Network V E) (q : E → Prop) (a : V)
    (hdeg : ∀ v, (N.sub q).graph.Reachable a v →
      (N.sub q).deg (fun _ => 1) v = 2 ∨ (N.sub q).deg (fun _ => 1) v = 3) :
    (N.sub (N.compEdges q a)).IsWeakPole := by
  constructor
  · intro v
    by_cases hv : (N.sub q).graph.Reachable a v
    · rw [N.deg_compEdges_of_reachable q a hv]
      exact Or.inr (hdeg v hv)
    · exact Or.inl (N.deg_compEdges_of_not_reachable q a hv)
  · intro u v hu hv
    have hu' : (N.sub q).graph.Reachable a u := Classical.not_not.1 fun h => by
      rw [N.deg_compEdges_of_not_reachable q a h] at hu
      omega
    have hv' : (N.sub q).graph.Reachable a v := Classical.not_not.1 fun h => by
      rw [N.deg_compEdges_of_not_reachable q a h] at hv
      omega
    exact (N.reachable_compEdges q a hu').symm.trans (N.reachable_compEdges q a hv')

omit [Fintype V] in
/-- **The ports of the component.** In a cubic network, the component has at most twice as many
ports as there are edges outside `q`: every port is an end of such an edge. -/
theorem natCard_ports_compEdges_le [Finite V] (N : Network V E) (hcubic : N.IsCubic)
    (q : E → Prop) (a : V) :
    Nat.card {v : V // (N.sub (N.compEdges q a)).IsPort v} ≤
      2 * Nat.card {g : E // ¬ q g} := by
  have h : ∀ v : {v : V // (N.sub (N.compEdges q a)).IsPort v},
      ∃ g : E, ¬ q g ∧ (N.src g = v.1 ∨ N.dst g = v.1) := by
    intro v
    refine Classical.not_not.1 fun hno => ?_
    have hall : ∀ g, (N.src g = v.1 ∨ N.dst g = v.1) → q g := fun g hg =>
      Classical.not_not.1 fun hq => hno ⟨g, hq, hg⟩
    have h2 : (N.sub (N.compEdges q a)).deg (fun _ => 1) v.1 = 2 := v.2
    have hreach : (N.sub q).graph.Reachable a v.1 := Classical.not_not.1 fun hnr => by
      have h0 := N.deg_compEdges_of_not_reachable q a hnr
      omega
    have h1 := N.deg_compEdges_of_reachable q a hreach
    have h3 : (N.sub q).deg (fun _ => 1) v.1 = N.deg (fun _ => 1) v.1 := by
      rw [N.deg_sub_ones]
      apply N.deg_congr
      intro g hg
      rw [restrict_ne_zero_iff]
      exact ⟨fun hh => hh.2, fun hh => ⟨hall g hg, hh⟩⟩
    have h4 := hcubic v.1
    omega
  choose G hG using h
  obtain ⟨φ, hφ⟩ : ∃ φ : {v : V // (N.sub (N.compEdges q a)).IsPort v} →
      {g : E // ¬ q g} × Bool,
      ∀ v, (φ v).1.1 = G v ∧ ((φ v).2 = true ↔ N.src (G v) = v.1) :=
    ⟨fun v => (⟨G v, (hG v).1⟩, decide (N.src (G v) = v.1)),
      fun v => ⟨rfl, decide_eq_true_iff⟩⟩
  have hinj : Function.Injective φ := by
    intro v v' hvv
    have e1 : G v = G v' := by rw [← (hφ v).1, ← (hφ v').1, hvv]
    have e2 : (φ v).2 = (φ v').2 := by rw [hvv]
    by_cases hs : N.src (G v) = v.1
    · have k1 : (φ v').2 = true := by
        rw [← e2]
        exact (hφ v).2.2 hs
      have hs' := (hφ v').2.1 k1
      exact Subtype.ext (by rw [← hs, e1, hs'])
    · have hd : N.dst (G v) = v.1 := (hG v).2.resolve_left hs
      have hns' : ¬ N.src (G v') = v'.1 := by
        intro hs'
        have k1 : (φ v).2 = true := by
          rw [e2]
          exact (hφ v').2.2 hs'
        exact hs ((hφ v).2.1 k1)
      have hd' : N.dst (G v') = v'.1 := (hG v').2.resolve_left hns'
      exact Subtype.ext (by rw [← hd, e1, hd'])
  have h1 := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  omega

/-- **The rank of the component.** Let `N` be connected, and let every vertex outside the
component of `a` have degree zero or at least two in `q`. Then the rank of the component plus
the number of the edges outside `q` is at most the rank of `N` plus the number of the vertices
outside the component that have degree zero in `q`. -/
theorem rank_compEdges_add_le (N : Network V E) (hN : N.graph.Connected) (q : E → Prop) (a : V)
    (h2 : ∀ v, ¬ (N.sub q).graph.Reachable a v →
      (N.sub q).deg (fun _ => 1) v = 0 ∨ 2 ≤ (N.sub q).deg (fun _ => 1) v) :
    networkRank (N.sub (N.compEdges q a)) + Nat.card {g : E // ¬ q g} ≤
      networkRank N + Nat.card {v : V // ¬ (N.sub q).graph.Reachable a v ∧
        (N.sub q).deg (fun _ => 1) v = 0} := by
  obtain ⟨T, hT⟩ : ∃ T : V → Prop, ∀ v, T v ↔ (N.sub q).graph.Reachable a v :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : V → ℕ, ∀ v, d v = (N.sub q).deg (fun _ => 1) v := ⟨_, fun _ => rfl⟩
  -- Euler's formula for `N` and for the component
  have e0 := network_rank_euler N
  rw [connected_component_card N hN] at e0
  have e1 := network_rank_euler (N.sub (N.compEdges q a))
  simp only [← Nat.card_eq_fintype_card] at e0 e1
  have c1 : Nat.card (N.sub (N.compEdges q a)).Component = Nat.card {v : V // ¬ T v} + 1 :=
    natCard_component_of_side (N.sub (N.compEdges q a)) T
      ((hT a).2 (SimpleGraph.Reachable.refl a))
      (fun (e : {g : E // N.compEdges q a g}) =>
        ⟨(hT _).2 e.2.2, (hT _).2 ((N.reachable_src_iff_dst q a e.2.1).1 e.2.2)⟩)
      (fun u hu => N.reachable_compEdges q a ((hT u).1 hu))
  rw [c1] at e1
  -- the vertices outside the component
  have hU : Nat.card {v : V // ¬ T v} =
      Nat.card {v : V // ¬ T v ∧ 0 < d v} + Nat.card {v : V // ¬ T v ∧ d v = 0} := by
    rw [← natCard_or_of_disjoint (fun v : V => ¬ T v ∧ 0 < d v) (fun v => ¬ T v ∧ d v = 0)
      (fun v h1 h2 => by have := h1.2; have := h2.2; omega)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h => (Nat.eq_zero_or_pos (d v)).elim (fun h0 => Or.inr ⟨h, h0⟩)
        (fun hp => Or.inl ⟨h, hp⟩), fun h => h.elim (fun h' => h'.1) (fun h' => h'.1)⟩)
  -- the edges
  have hE : Nat.card E = Nat.card {g : E // q g} + Nat.card {g : E // ¬ q g} := by
    rw [← natCard_or_of_disjoint (fun g : E => q g) (fun g => ¬ q g) (fun g h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun g => Classical.em (q g)))).symm
  have hq : Nat.card {g : E // q g} = Nat.card {e : {g : E // q g} // T (N.src e.1)} +
      Nat.card {e : {g : E // q g} // ¬ T (N.src e.1)} := by
    rw [← natCard_or_of_disjoint (fun e : {g : E // q g} => T (N.src e.1))
      (fun e => ¬ T (N.src e.1)) (fun e h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun e : {g : E // q g} => Classical.em (T (N.src e.1))))).symm
  have hc : Nat.card {e : {g : E // q g} // T (N.src e.1)} =
      Nat.card {g : E // N.compEdges q a g} :=
    Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter q (fun g => T (N.src g))).trans
      (Equiv.subtypeEquivRight fun g => ⟨fun h => ⟨h.1, (hT _).1 h.2⟩,
        fun h => ⟨h.1, (hT _).2 h.2⟩⟩))
  -- the count of edge ends outside the component
  have hclosed : ∀ e : {g : E // q g}, T (N.src e.1) ↔ T (N.dst e.1) := by
    intro e
    rw [hT, hT]
    exact N.reachable_src_iff_dst q a e.2
  have hsum := (N.sub q).sum_deg_eq (fun v => ¬ T v)
  have hends := (N.sub q).sum_ends_eq (fun v => ¬ T v)
  have hcut : (N.sub q).cutSize (fun v => ¬ T v) = 0 := by
    apply Nat.card_eq_zero.2
    refine Or.inl ⟨fun e => e.2 ?_⟩
    exact ⟨fun h1 h2 => h1 ((hclosed e.1).2 h2), fun h1 h2 => h1 ((hclosed e.1).1 h2)⟩
  have hin : Nat.card {e : {g : E // q g} // (N.sub q).inside (fun v => ¬ T v) e} ≤
      Nat.card {e : {g : E // q g} // ¬ T (N.src e.1)} :=
    natCard_le_of_imp (fun e he => he.1)
  have hlow2 : 2 * Nat.card {v : V // ¬ T v ∧ 0 < d v} ≤
      2 * Nat.card {e : {g : E // q g} // (N.sub q).inside (fun v => ¬ T v) e} +
        (N.sub q).cutSize (fun v => ¬ T v) := by
    rw [← hends, ← hsum, natCard_subtype_eq_card_filter, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : T v
    · rw [if_neg (fun h : ¬ T v ∧ 0 < d v => h.1 hv), if_neg (fun h : ¬ T v => h hv)]
      omega
    · rw [if_pos hv]
      by_cases hp : 0 < d v
      · rw [if_pos (⟨hv, hp⟩ : ¬ T v ∧ 0 < d v)]
        have h3 := h2 v (fun h => hv ((hT v).2 h))
        rw [hd v] at hp
        omega
      · rw [if_neg (fun h : ¬ T v ∧ 0 < d v => hp h.2)]
        omega
  rw [hcut] at hlow2
  have hI : Nat.card {v : V // ¬ T v ∧ d v = 0} =
      Nat.card {v : V // ¬ (N.sub q).graph.Reachable a v ∧
        (N.sub q).deg (fun _ => 1) v = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [hT, hd])
  omega

/-! ### A cubic cyclic shore of a part is a cyclic cut -/

/-- **A cubic cyclic shore of a part.** Let `N` be a cubic network in which every cyclic cut has
at least five crossing edges, and let `p` be a set of edges. Then the network of `p` has no
cyclic cut with at most four crossing edges all of whose vertices have degree three in `p`. -/
theorem false_of_shore {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hcubic : N.IsCubic) (hcut : ∀ S : V → Prop, N.IsCyclicCut S → 5 ≤ N.cutSize S)
    (p : E → Prop) (S : V → Prop) (hS : (N.sub p).IsCyclicCut S)
    (h4 : (N.sub p).cutSize S ≤ 4) (h3 : ∀ v, S v → (N.sub p).deg (fun _ => 1) v = 3) :
    False := by
  -- all edges of `N` at a vertex of `S` are in `p`
  have hall : ∀ v, S v → ∀ g, (N.src g = v ∨ N.dst g = v) → p g := by
    intro v hv g hg
    refine Classical.not_not.1 fun hpg => ?_
    have h1 := h3 v hv
    rw [N.deg_sub_ones] at h1
    have h2 := hcubic v
    -- the degree in `p` is smaller, because `g` is missing
    have hlt : N.deg (restrict (fun _ => 1) p) v < N.deg (fun _ => 1) v := by
      unfold deg
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ g, one_ne_zero, hg⟩, fun hmem => ?_⟩
        exact hpg ((restrict_ne_zero_iff _ _ g).1 (Finset.mem_filter.1 hmem).2.1).1
      · intro k hk
        exact Finset.mem_filter.2 ⟨Finset.mem_univ k, one_ne_zero, (Finset.mem_filter.1 hk).2.2⟩
    omega
  -- the cut of `N`
  have hcyc : N.IsCyclicCut S := by
    constructor
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨y, hy, hw⟩⟩ := Finite.card_pos_iff.1 h
      refine Erdos1016.ExactMaximum.numCycles_sub_pos N _
        ((N.isCycleWord_extend_iff p y).2 hy) ?_
      intro g hg
      by_cases hpg : p g
      · rw [extend_apply_of_pos p _ hpg] at hg
        exact hw ⟨g, hpg⟩ hg
      · rw [extend_apply_of_neg p _ hpg] at hg
        exact absurd rfl hg
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨y, hy, hw⟩⟩ := Finite.card_pos_iff.1 h
      refine Erdos1016.ExactMaximum.numCycles_sub_pos N _
        ((N.isCycleWord_extend_iff p y).2 hy) ?_
      intro g hg
      by_cases hpg : p g
      · rw [extend_apply_of_pos p _ hpg] at hg
        exact hw ⟨g, hpg⟩ hg
      · rw [extend_apply_of_neg p _ hpg] at hg
        exact absurd rfl hg
  have hle : N.cutSize S ≤ (N.sub p).cutSize S := by
    have hp : ∀ g, N.crosses S g → p g := by
      intro g hg
      by_cases hs : S (N.src g)
      · exact hall _ hs g (Or.inl rfl)
      · have hd : S (N.dst g) := Classical.not_not.1 fun hd =>
          hg ⟨fun h => absurd h hs, fun h => absurd h hd⟩
        exact hall _ hd g (Or.inr rfl)
    obtain ⟨φ, hφ⟩ : ∃ φ : {g : E // N.crosses S g} →
        {g : {g : E // p g} // (N.sub p).crosses S g}, ∀ g, (φ g).1.1 = g.1 :=
      ⟨fun g => ⟨⟨g.1, hp g.1 g.2⟩, g.2⟩, fun _ => rfl⟩
    apply Nat.card_le_card_of_injective φ
    intro g g' hgg
    apply Subtype.ext
    rw [← hφ g, ← hφ g', hgg]
  have h5 := hcut S hcyc
  omega

end Erdos1016.BoundaryTrace.Network

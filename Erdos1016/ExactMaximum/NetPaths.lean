import Erdos1016.CycleSpace.NetworkRank
import Erdos1016.CycleSpace.Parity

set_option autoImplicit false

/-!
# Cycles and paths in a network

A `Network V E` is a finite multigraph without loops on arbitrary finite types of vertices and
edges. A part of a network (for example one side of a cut) is the network of a subtype of the
edges, so no vertices or edges are renumbered. Sections 5 to 7 of the paper "The maximum number
of cycles in a graph of large rank" work with such parts, which the paper calls poles.

This file defines cycles and paths of a network as edge words and proves the statements of
Section 5.1 that the later sections use:

* the boundary of an edge word at a vertex is the selected degree modulo two;
* a cycle is a nonzero even word, so a network of rank `b` has fewer than `2^b` cycles;
* a path from `s` to `t` is an `{s,t}`-join, so there are at most `2^b` paths (inequality (5.1));
* if a cycle and a path have no common vertex, their sum is a join that is not a path;
* so if the pair `s,t` is full, every cycle meets every path, and if some cycle meets no path,
  there are at most `2^(b-1)` paths (Lemma 5.1).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netPathsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype E]

/-- An element of `Bit` is zero or one. -/
theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-! ### Degrees -/

/-- The number of selected edges at the vertex `v`. A network has no loops, so an edge is
counted once. -/
def deg (N : Network V E) (x : N.Word) (v : V) : ℕ :=
  (Finset.univ.filter fun e : E => x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)).card

theorem deg_eq_sum (N : Network V E) (x : N.Word) (v : V) :
    N.deg x v = ∑ e, if x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v) then 1 else 0 := by
  unfold deg
  rw [Finset.card_filter]

/-- The boundary at a vertex is the selected degree modulo two. -/
theorem boundary_eq_deg [Fintype V] (N : Network V E) (x : N.Word) (v : V) :
    N.boundary x v = ((N.deg x v : ℕ) : Bit) := by
  rw [boundary_apply, deg_eq_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hne := N.noLoops e
  rcases bit_cases (x e) with hx | hx <;> by_cases hs : N.src e = v <;>
    by_cases ht : N.dst e = v
  all_goals first
    | (exfalso; exact hne (hs.trans ht.symm))
    | simp [hx, hs, ht]

/-- A selected edge gives its first end a positive selected degree. -/
theorem deg_src_pos (N : Network V E) {x : N.Word} {e : E} (hx : x e ≠ 0) :
    0 < N.deg x (N.src e) :=
  Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ e, hx, Or.inl rfl⟩⟩

/-- A selected edge gives its second end a positive selected degree. -/
theorem deg_dst_pos (N : Network V E) {x : N.Word} {e : E} (hx : x e ≠ 0) :
    0 < N.deg x (N.dst e) :=
  Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ e, hx, Or.inr rfl⟩⟩

/-- A vertex of positive selected degree is an end of a selected edge. -/
theorem exists_edge_of_deg_pos (N : Network V E) {x : N.Word} {v : V} (h : 0 < N.deg x v) :
    ∃ e, x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v) := by
  obtain ⟨e, he⟩ := Finset.card_pos.1 h
  exact ⟨e, (Finset.mem_filter.1 he).2⟩

/-- The selected degree is additive for edge words with disjoint supports. -/
theorem deg_add_of_disjoint (N : Network V E) {x y : N.Word} (h : ∀ e, x e ≠ 0 → y e = 0)
    (v : V) : N.deg (x + y) v = N.deg x v + N.deg y v := by
  simp only [deg_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rcases bit_cases (x e) with hx | hx
  · have hxy : (x + y) e = y e := by simp [hx]
    rw [hxy]
    simp [hx]
  · have hy : y e = 0 := h e (by rw [hx]; exact one_ne_zero)
    have hxy : (x + y) e = x e := by simp [hy]
    rw [hxy]
    simp [hy]

/-! ### Cycles -/

section

variable [Fintype V]

/-- A cycle of a network, as an edge word: the word is not zero, every vertex has selected degree
zero or two, and any two vertices of positive selected degree are joined by selected edges. -/
def IsCycleWord (N : Network V E) (x : N.Word) : Prop :=
  x ≠ 0 ∧ (∀ v, N.deg x v = 0 ∨ N.deg x v = 2) ∧
  ∀ u v, 0 < N.deg x u → 0 < N.deg x v → (N.selectedGraph x).Reachable u v

/-- The number of cycles of a network. -/
def numCycles (N : Network V E) : ℕ := Nat.card {x : N.Word // N.IsCycleWord x}

instance (N : Network V E) : Finite {x : N.Word // N.IsCycleWord x} := Subtype.finite

/-- A cycle has zero boundary. -/
theorem IsCycleWord.boundary_eq_zero {N : Network V E} {x : N.Word} (hx : N.IsCycleWord x) :
    N.boundary x = 0 := by
  funext v
  rw [boundary_eq_deg]
  rcases hx.2.1 v with h | h <;> rw [h] <;> rfl

omit [Fintype V] in
/-- A cycle has a selected edge. -/
theorem IsCycleWord.exists_edge {N : Network V E} {x : N.Word} (hx : N.IsCycleWord x) :
    ∃ e, x e ≠ 0 := by
  rcases Classical.em (∃ e, x e ≠ 0) with h | h
  · exact h
  · exfalso
    apply hx.1
    funext e
    exact Classical.not_not.1 fun hne => h ⟨e, hne⟩

/-- A network of rank `b` has fewer than `2^b` cycles. -/
theorem numCycles_lt_two_pow (N : Network V E) : N.numCycles < 2 ^ networkRank N := by
  let f : Option {x : N.Word // N.IsCycleWord x} → N.CycleSpace := fun o =>
    match o with
    | none => 0
    | some x => ⟨x.1, LinearMap.mem_ker.2 x.2.boundary_eq_zero⟩
  have hinj : Function.Injective f := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exfalso
      have h : (f none).1 = (f (some b)).1 := congrArg Subtype.val hab
      exact b.2.1 h.symm
    · exfalso
      have h : (f (some a)).1 = (f none).1 := congrArg Subtype.val hab
      exact a.2.1 h
    · have h : (f (some a)).1 = (f (some b)).1 := congrArg Subtype.val hab
      exact congrArg some (Subtype.ext h)
  have hcard := Nat.card_le_card_of_injective f hinj
  have hZ : Nat.card N.CycleSpace = 2 ^ networkRank N := by
    have h := Module.natCard_eq_pow_finrank (K := Bit) (V := N.CycleSpace)
    simpa [Bit] using h
  rw [hZ, Finite.card_option] at hcard
  unfold numCycles
  omega

/-! ### Paths -/

/-- A path from `s` to `t`, as an edge word. -/
def IsPathWord (N : Network V E) (s t : V) (x : N.Word) : Prop :=
  s ≠ t ∧ N.deg x s = 1 ∧ N.deg x t = 1 ∧
  (∀ v, v ≠ s → v ≠ t → N.deg x v = 0 ∨ N.deg x v = 2) ∧
  ∀ v, 0 < N.deg x v → (N.selectedGraph x).Reachable s v

/-- The number of paths from `s` to `t`. -/
def numPaths (N : Network V E) (s t : V) : ℕ := Nat.card {x : N.Word // N.IsPathWord s t x}

/-- The parity pattern of a path from `s` to `t`: odd degree at `s` and at `t` only. -/
def pathDemand (N : Network V E) (s t : V) : N.Demand := Pi.single s 1 + Pi.single t 1

/-- The pair `s,t` is full: the number of paths is the largest possible. -/
def IsFullPair (N : Network V E) (s t : V) : Prop := N.numPaths s t = 2 ^ networkRank N

/-- The two edge words have no common vertex. -/
def VertexDisjoint (N : Network V E) (x y : N.Word) : Prop :=
  ∀ v, N.deg x v = 0 ∨ N.deg y v = 0

instance (N : Network V E) (s t : V) : Finite {x : N.Word // N.IsPathWord s t x} :=
  Subtype.finite

/-- A path from `s` to `t` is an `{s,t}`-join. -/
theorem IsPathWord.boundary_eq {N : Network V E} {s t : V} {x : N.Word}
    (h : N.IsPathWord s t x) : N.boundary x = N.pathDemand s t := by
  funext v
  rw [boundary_eq_deg]
  by_cases hs : v = s
  · subst hs
    rw [h.2.1]
    simp [pathDemand, h.1]
  · by_cases ht : v = t
    · subst ht
      rw [h.2.2.1]
      simp [pathDemand, hs]
    · have h0 : N.pathDemand s t v = 0 := by simp [pathDemand, hs, ht]
      rw [h0]
      rcases h.2.2.2.1 v hs ht with hd | hd <;> rw [hd] <;> rfl

/-- The number of `{s,t}`-joins is `2^b` if there is one. -/
theorem card_joins (N : Network V E) (s t : V)
    (x₀ : Parity.Fiber N.boundary (N.pathDemand s t)) :
    Nat.card (Parity.Fiber N.boundary (N.pathDemand s t)) = 2 ^ networkRank N :=
  Parity.fiber_natCard N.boundary x₀

/-- **Inequality (5.1) of the paper.** There are at most `2^b` paths between two vertices of a
network of rank `b`. -/
theorem numPaths_le_two_pow (N : Network V E) (s t : V) :
    N.numPaths s t ≤ 2 ^ networkRank N := by
  by_cases hne : Nonempty {x : N.Word // N.IsPathWord s t x}
  · obtain ⟨x₀⟩ := hne
    let f : {x : N.Word // N.IsPathWord s t x} →
        Parity.Fiber N.boundary (N.pathDemand s t) := fun x => ⟨x.1, x.2.boundary_eq⟩
    have hf : Function.Injective f := by
      intro a b h
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val h
      exact Subtype.ext h'
    have hcard := Nat.card_le_card_of_injective f hf
    rw [card_joins N s t (f x₀)] at hcard
    exact hcard
  · have h0 : N.numPaths s t = 0 := by
      unfold numPaths
      rw [Nat.card_eq_zero]
      exact Or.inl (not_nonempty_iff.mp hne)
    rw [h0]
    exact Nat.zero_le _

omit [Fintype V] in
/-- Edge words without a common vertex have disjoint supports. -/
theorem VertexDisjoint.support {N : Network V E} {x y : N.Word} (h : N.VertexDisjoint x y) :
    ∀ e, x e ≠ 0 → y e = 0 := by
  intro e hx
  refine Classical.not_not.1 fun hy => ?_
  have h1 := N.deg_src_pos hx
  have h2 := N.deg_src_pos hy
  rcases h (N.src e) with h0 | h0 <;> omega

omit [Fintype V] in
/-- The sum of a path and a vertex-disjoint cycle is not a path. -/
theorem IsPathWord.add_cycle_not_path {N : Network V E} {s t : V} {p z : N.Word}
    (hp : N.IsPathWord s t p) (hz : N.IsCycleWord z) (hd : N.VertexDisjoint p z) :
    ¬ N.IsPathWord s t (p + z) := by
  intro hpz
  have hsupp := hd.support
  -- a vertex that is joined to `s` by edges of `p + z` is not on `z`
  have hreach : ∀ u v, (N.selectedGraph (p + z)).Walk u v → N.deg z u = 0 → N.deg z v = 0 := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons a b c hadj _ ih =>
      intro ha
      apply ih
      obtain ⟨e, he, hends⟩ := hadj
      by_cases hze : z e = 0
      · -- then `e` is an edge of `p`, and the next vertex is on `p`
        have hpe : p e ≠ 0 := by
          intro h0
          apply he
          show p e + z e = 0
          rw [h0, hze, add_zero]
        have hb : 0 < N.deg p b := by
          rcases hends with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2 ▸ N.deg_dst_pos hpe
          · exact h1 ▸ N.deg_src_pos hpe
        rcases hd b with h0 | h0
        · omega
        · exact h0
      · -- then the first vertex of the step is on `z`
        exfalso
        have ha' : 0 < N.deg z a := by
          rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact h1 ▸ N.deg_src_pos hze
          · exact h2 ▸ N.deg_dst_pos hze
        omega
  -- `s` is on `p`, so it is not on `z`
  have hs : N.deg z s = 0 := by
    rcases hd s with h0 | h0
    · rw [hp.2.1] at h0
      exact absurd h0 one_ne_zero
    · exact h0
  obtain ⟨e, he⟩ := hz.exists_edge
  have hzpos := N.deg_src_pos he
  have hsum := N.deg_add_of_disjoint hsupp (N.src e)
  have hpos : 0 < N.deg (p + z) (N.src e) := by omega
  obtain ⟨w⟩ := hpz.2.2.2.2 _ hpos
  have := hreach _ _ w hs
  omega

/-- The sum of a path from `s` to `t` and a cycle is an `{s,t}`-join. -/
theorem IsPathWord.add_cycle_boundary {N : Network V E} {s t : V} {p z : N.Word}
    (hp : N.IsPathWord s t p) (hz : N.IsCycleWord z) :
    N.boundary (p + z) = N.pathDemand s t := by
  rw [map_add, hp.boundary_eq, hz.boundary_eq_zero, add_zero]

/-- **Lemma 5.1 of the paper, second part.** If some cycle has no common vertex with any path
from `s` to `t`, there are at most `2^(b-1)` such paths: `2 * numPaths ≤ 2^b`. -/
theorem two_mul_numPaths_le_of_disjoint_cycle (N : Network V E) (s t : V) {z : N.Word}
    (hz : N.IsCycleWord z) (hd : ∀ p, N.IsPathWord s t p → N.VertexDisjoint p z) :
    2 * N.numPaths s t ≤ 2 ^ networkRank N := by
  by_cases hne : Nonempty {x : N.Word // N.IsPathWord s t x}
  · obtain ⟨x₀⟩ := hne
    -- send a path to itself, and to its sum with the cycle
    let f : {x : N.Word // N.IsPathWord s t x} ⊕ {x : N.Word // N.IsPathWord s t x} →
        Parity.Fiber N.boundary (N.pathDemand s t) := fun x =>
      match x with
      | Sum.inl x => ⟨x.1, x.2.boundary_eq⟩
      | Sum.inr x => ⟨x.1 + z, x.2.add_cycle_boundary hz⟩
    have hf : Function.Injective f := by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · have h : (f (Sum.inl a)).1 = (f (Sum.inl b)).1 := congrArg Subtype.val hab
        exact congrArg Sum.inl (Subtype.ext h)
      · exfalso
        have h : (f (Sum.inl a)).1 = (f (Sum.inr b)).1 := congrArg Subtype.val hab
        have h' : a.1 = b.1 + z := h
        exact b.2.add_cycle_not_path hz (hd _ b.2) (h' ▸ a.2)
      · exfalso
        have h : (f (Sum.inr a)).1 = (f (Sum.inl b)).1 := congrArg Subtype.val hab
        have h' : a.1 + z = b.1 := h
        exact a.2.add_cycle_not_path hz (hd _ a.2) (h' ▸ b.2)
      · have h : (f (Sum.inr a)).1 = (f (Sum.inr b)).1 := congrArg Subtype.val hab
        have h' : a.1 + z = b.1 + z := h
        exact congrArg Sum.inr (Subtype.ext (add_right_cancel h'))
    have hcard := Nat.card_le_card_of_injective f hf
    rw [card_joins N s t (f (Sum.inl x₀)), Nat.card_sum] at hcard
    unfold numPaths
    omega
  · have h0 : N.numPaths s t = 0 := by
      unfold numPaths
      rw [Nat.card_eq_zero]
      exact Or.inl (not_nonempty_iff.mp hne)
    rw [h0]
    exact Nat.zero_le _

/-- **Lemma 5.1 of the paper, first part.** If the pair `s,t` is full, every cycle has a common
vertex with every path from `s` to `t`. -/
theorem IsFullPair.cycle_meets_path {N : Network V E} {s t : V} (hfull : N.IsFullPair s t)
    {p z : N.Word} (hp : N.IsPathWord s t p) (hz : N.IsCycleWord z) :
    ∃ v, 0 < N.deg p v ∧ 0 < N.deg z v := by
  refine Classical.not_not.1 fun hno => ?_
  have hd : N.VertexDisjoint p z := by
    intro v
    refine Classical.not_not.1 fun h => hno ⟨v, ?_, ?_⟩ <;> omega
  -- the join `p + z` is not a path, so the paths do not fill the set of joins
  let f : Option {x : N.Word // N.IsPathWord s t x} →
      Parity.Fiber N.boundary (N.pathDemand s t) := fun x =>
    match x with
    | none => ⟨p + z, hp.add_cycle_boundary hz⟩
    | some x => ⟨x.1, x.2.boundary_eq⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exfalso
      have h : (f none).1 = (f (some b)).1 := congrArg Subtype.val hab
      have h' : p + z = b.1 := h
      exact hp.add_cycle_not_path hz hd (h' ▸ b.2)
    · exfalso
      have h : (f (some a)).1 = (f none).1 := congrArg Subtype.val hab
      have h' : a.1 = p + z := h
      exact hp.add_cycle_not_path hz hd (h' ▸ a.2)
    · have h : (f (some a)).1 = (f (some b)).1 := congrArg Subtype.val hab
      exact congrArg some (Subtype.ext h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [card_joins N s t (f none), Finite.card_option] at hcard
  have h2 : Nat.card {x : N.Word // N.IsPathWord s t x} = 2 ^ networkRank N := hfull
  omega

end

end Erdos1016.BoundaryTrace.Network

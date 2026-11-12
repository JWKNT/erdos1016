import Erdos1016.ExactMaximum.NetGlue
import Erdos1016.ExactMaximum.NetPairs
import Erdos1016.ExactMaximum.NetBridge
import Erdos1016.ExactMaximum.NetTransfer
import Erdos1016.ExactMaximum.CountTools

set_option autoImplicit false

/-!
# Paths by their first edge, and cycles through an edge

The proof of Theorem 7.1 of the paper "The maximum number of cycles in a graph of large rank"
counts the cycles through an edge `e` as paths between the ends of `e`, and it sorts these paths
by the vertex where they leave a fixed cycle. This file proves the two counting steps, for paths
within a set `q` of edges of a network (`numPathsIn`):

* `numCycles_le_add_numPathsIn`: `c(N) ≤ c(N - e) + P`, where `P` is the number of paths between
  the ends of `e` that do not use `e`;
* `numPathsIn_le_of_two_edges`, `numPathsIn_le_of_one_edge`: a path from `s` starts with one of
  the edges at `s`, and the rest is a path from the other end of that edge that does not use an
  edge at `s`.

All words are words of the same network `N`, so no sub-network of a sub-network occurs.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance pathFirstEdgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The number of paths from `s` to `t` within the set `q` of edges. -/
def numPathsIn (N : Network V E) (q : E → Prop) (s t : V) : ℕ :=
  Nat.card {x : N.Word // N.IsPathWord s t x ∧ Within x q}

omit [Fintype V] in
/-- The paths within `q` are the paths of the network of `q`. -/
theorem numPathsIn_eq (N : Network V E) (q : E → Prop) (s t : V) :
    N.numPathsIn q s t = (N.sub q).numPaths s t :=
  (N.numPaths_sub q s t).symm

omit [Fintype V] in
/-- The paths from `s` to `t` are the paths from `t` to `s`. -/
theorem numPathsIn_symm (N : Network V E) (q : E → Prop) (s t : V) :
    N.numPathsIn q s t = N.numPathsIn q t s :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩)

/-- At most `2^b` paths within `q`, where `b` is the rank of the network of `q`. -/
theorem numPathsIn_le_two_pow (N : Network V E) (q : E → Prop) (s t : V) :
    N.numPathsIn q s t ≤ 2 ^ networkRank (N.sub q) := by
  rw [N.numPathsIn_eq q s t]
  exact (N.sub q).numPaths_le_two_pow s t

omit [Fintype V] in
/-- A smaller set of edges has fewer paths. -/
theorem numPathsIn_mono (N : Network V E) {q q' : E → Prop} (h : ∀ g, q g → q' g) (s t : V) :
    N.numPathsIn q s t ≤ N.numPathsIn q' s t :=
  natCard_le_of_imp (fun _ hx => ⟨hx.1, fun g hg => h g (hx.2 g hg)⟩)

/-! ### Single edges -/

omit [Fintype V] in
theorem unitWord_apply_self (f : E) : (unitWord f : E → Bit) f = 1 := by
  rw [unitWord_apply, if_pos rfl]

omit [Fintype V] in
theorem unitWord_apply_of_ne {f g : E} (h : f ≠ g) : (unitWord f : E → Bit) g = 0 := by
  rw [unitWord_apply, if_neg h]

omit [Fintype V] in
/-- A vertex of selected degree one is on one selected edge only. -/
theorem eq_of_deg_eq_one (N : Network V E) {x : N.Word} {v : V} (h : N.deg x v = 1) {f g : E}
    (hf : x f ≠ 0) (hfv : N.src f = v ∨ N.dst f = v) (hg : x g ≠ 0)
    (hgv : N.src g = v ∨ N.dst g = v) : f = g := by
  unfold deg at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
  have h1 : f ∈ ({a} : Finset E) := by
    rw [← ha]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ f, hf, hfv⟩
  have h2 : g ∈ ({a} : Finset E) := by
    rw [← ha]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ g, hg, hgv⟩
  rw [Finset.mem_singleton] at h1 h2
  rw [h1, h2]

omit [Fintype V] in
/-- The word `x` without its edge `f`: the values. -/
theorem add_unitWord_ne_zero_iff {x : E → Bit} {f : E} (hxf : x f ≠ 0) (g : E) :
    (x + unitWord f) g ≠ 0 ↔ (x g ≠ 0 ∧ g ≠ f) := by
  by_cases hg : g = f
  · subst hg
    constructor
    · intro h
      exfalso
      apply h
      show x g + unitWord g g = 0
      rw [bit_eq_one_of_ne_zero hxf, unitWord_apply_self]
      exact bit_add_self 1
    · intro h
      exact absurd rfl h.2
  · have h0 : (x + unitWord f) g = x g := by
      show x g + unitWord f g = x g
      rw [unitWord_apply_of_ne (fun h => hg h.symm), add_zero]
    rw [h0]
    exact ⟨fun h => ⟨h, hg⟩, fun h => h.1⟩

/-! ### The first edge of a path -/

/-- **A path without its first edge.** Let `x` be a path from `s` to `t` whose edge `f` joins `s`
and `u ≠ t`. Then `x` without `f` is a path from `u` to `t`. -/
theorem IsPathWord.erase_first {N : Network V E} {s t u : V} {x : N.Word} {f : E}
    (hx : N.IsPathWord s t x) (hf : N.Joins f s u) (hxf : x f ≠ 0) (hut : u ≠ t) :
    N.IsPathWord u t (x + unitWord f) := by
  have hsub : N.IsSubword (x + unitWord f) x := (N.isSubword_unitWord hxf).add_self
  apply N.isPathWord_of_minimal hut
  · rw [map_add, hx.boundary_eq, N.boundary_unitWord_of_joins hf]
    show (unitWord s : V → Bit) + unitWord t + (unitWord s + unitWord u) =
      unitWord u + unitWord t
    have e1 : (unitWord s : V → Bit) + unitWord t + (unitWord s + unitWord u) =
        (unitWord s + unitWord s) + (unitWord u + unitWord t) := by abel
    rw [e1, word_add_self, zero_add]
  · intro y hy hy0
    exact hx.eq_zero_of_even_subword (fun g hg => hsub g (hy g hg)) hy0

/-- **A path whose first edge ends in `t`** is this edge. -/
theorem IsPathWord.eq_unitWord_of_first {N : Network V E} {s t : V} {x : N.Word} {f : E}
    (hx : N.IsPathWord s t x) (hf : N.Joins f s t) (hxf : x f ≠ 0) : x = unitWord f := by
  have hsub : N.IsSubword (x + unitWord f) x := (N.isSubword_unitWord hxf).add_self
  apply word_eq_of_add_eq_zero
  apply hx.eq_zero_of_even_subword hsub
  rw [map_add, hx.boundary_eq, N.boundary_unitWord_of_joins hf]
  exact word_add_self _

omit [Fintype V] in
/-- A path from `s` without its first edge has no edge at `s`. -/
theorem IsPathWord.erase_first_not_at {N : Network V E} {s t u : V} {x : N.Word} {f : E}
    (hx : N.IsPathWord s t x) (hf : N.Joins f s u) (hxf : x f ≠ 0) {g : E}
    (hg : (x + unitWord f) g ≠ 0) : ¬ (N.src g = s ∨ N.dst g = s) := by
  intro hgs
  have h1 := (add_unitWord_ne_zero_iff hxf g).1 hg
  exact h1.2 (N.eq_of_deg_eq_one hx.2.1 h1.1 hgs hxf hf.at_left)

/-- **The paths with a given first edge.** Let the edge `f` join `s` and `u`. The paths from `s`
to `t` within `q` that use `f` are at most the paths from `u` to `t` within `q` that use no edge
at `s`. If `u = t`, there is at most one. -/
theorem natCard_paths_first_le (N : Network V E) (q : E → Prop) (t : V) {s u : V} {f : E}
    (hf : N.Joins f s u) :
    Nat.card {x : N.Word // (N.IsPathWord s t x ∧ Within x q) ∧ x f ≠ 0} ≤
      if u = t then 1
      else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u t := by
  by_cases hut : u = t
  · rw [if_pos hut]
    subst hut
    rw [Finite.card_le_one_iff_subsingleton]
    refine ⟨fun a b => Subtype.ext ?_⟩
    rw [a.2.1.1.eq_unitWord_of_first hf a.2.2, b.2.1.1.eq_unitWord_of_first hf b.2.2]
  · rw [if_neg hut]
    obtain ⟨φ, hφ⟩ : ∃ φ : {x : N.Word // (N.IsPathWord s t x ∧ Within x q) ∧ x f ≠ 0} →
        {x : N.Word // N.IsPathWord u t x ∧
          Within x (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s))},
        ∀ x, (φ x).1 = x.1 + unitWord f := by
      refine ⟨fun x => ⟨x.1 + unitWord f, x.2.1.1.erase_first hf x.2.2 hut, ?_⟩, fun _ => rfl⟩
      intro g hg
      exact ⟨x.2.1.2 g ((add_unitWord_ne_zero_iff x.2.2 g).1 hg).1,
        x.2.1.1.erase_first_not_at hf x.2.2 hg⟩
    apply Nat.card_le_card_of_injective φ
    intro x x' hxx
    have h : x.1 + unitWord f = x'.1 + unitWord f := by rw [← hφ x, ← hφ x', hxx]
    exact Subtype.ext (add_right_cancel h)

/-- **The first edge of a path, two edges.** Let all edges of `q` at `s` be among `f₁`, `f₂`,
where `fᵢ` joins `s` and `uᵢ`. Then the number of paths from `s` to `t` within `q` is at most the
sum over `i` of the number of paths from `uᵢ` to `t` within `q` without the edges at `s`, where
the number is one if `uᵢ = t`. -/
theorem numPathsIn_le_of_two_edges (N : Network V E) (q : E → Prop) (t : V) {s u₁ u₂ : V}
    {f₁ f₂ : E} (h₁ : N.Joins f₁ s u₁) (h₂ : N.Joins f₂ s u₂)
    (hall : ∀ g, q g → (N.src g = s ∨ N.dst g = s) → g = f₁ ∨ g = f₂) :
    N.numPathsIn q s t ≤
      (if u₁ = t then 1
        else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u₁ t) +
      (if u₂ = t then 1
        else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u₂ t) := by
  obtain ⟨P, hP⟩ : ∃ P : N.Word → Prop, ∀ x, P x ↔ (N.IsPathWord s t x ∧ Within x q) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : N.Word → Prop,
      ∀ x, P₁ x ↔ ((N.IsPathWord s t x ∧ Within x q) ∧ x f₁ ≠ 0) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : N.Word → Prop,
      ∀ x, P₂ x ↔ ((N.IsPathWord s t x ∧ Within x q) ∧ x f₂ ≠ 0) := ⟨_, fun _ => Iff.rfl⟩
  have k0 : N.numPathsIn q s t = Nat.card {x : N.Word // P x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hP x).symm)
  have k1 : Nat.card {x : N.Word // P x} ≤ Nat.card {x : N.Word // P₁ x ∨ P₂ x} := by
    apply natCard_le_of_imp
    intro x hx
    have hx' := (hP x).1 hx
    obtain ⟨g, hg, hgs⟩ := N.exists_edge_of_deg_pos (x := x) (v := s) (by rw [hx'.1.2.1]; omega)
    rcases hall g (hx'.2 g hg) hgs with h | h
    · exact Or.inl ((hP₁ x).2 ⟨hx', h ▸ hg⟩)
    · exact Or.inr ((hP₂ x).2 ⟨hx', h ▸ hg⟩)
  have k2 := natCard_or_le P₁ P₂
  have k3 : Nat.card {x : N.Word // P₁ x} ≤
      if u₁ = t then 1
      else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u₁ t :=
    le_trans (natCard_le_of_imp (fun x hx => (hP₁ x).1 hx)) (N.natCard_paths_first_le q t h₁)
  have k4 : Nat.card {x : N.Word // P₂ x} ≤
      if u₂ = t then 1
      else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u₂ t :=
    le_trans (natCard_le_of_imp (fun x hx => (hP₂ x).1 hx)) (N.natCard_paths_first_le q t h₂)
  omega

/-- **The first edge of a path, one edge.** Let `f` be the only edge of `q` at `s`, and let `f`
join `s` and `u`. Then the number of paths from `s` to `t` within `q` is at most the number of
paths from `u` to `t` within `q` without `f`, or one if `u = t`. -/
theorem numPathsIn_le_of_one_edge (N : Network V E) (q : E → Prop) (t : V) {s u : V} {f : E}
    (hf : N.Joins f s u) (hall : ∀ g, q g → (N.src g = s ∨ N.dst g = s) → g = f) :
    N.numPathsIn q s t ≤
      if u = t then 1
      else N.numPathsIn (fun g => q g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u t := by
  refine le_trans ?_ (N.natCard_paths_first_le q t hf)
  apply natCard_le_of_imp
  intro x hx
  obtain ⟨g, hg, hgs⟩ := N.exists_edge_of_deg_pos (x := x) (v := s) (by rw [hx.1.2.1]; omega)
  have h := hall g (hx.2 g hg) hgs
  exact ⟨hx, h ▸ hg⟩

/-! ### The cycles through an edge -/

/-- **The cycles through an edge.** Let the edge `e` join `a` and `b`. Then the number of cycles
is at most the number of cycles that do not use `e` plus the number of paths from `a` to `b` that
do not use `e`. -/
theorem numCycles_le_add_numPathsIn (N : Network V E) {e : E} {a b : V} (he : N.Joins e a b) :
    N.numCycles ≤ (N.sub fun g => g ≠ e).numCycles + N.numPathsIn (fun g => g ≠ e) a b := by
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : N.Word → Prop,
      ∀ x, P₁ x ↔ (N.IsCycleWord x ∧ Within x (fun g => g ≠ e)) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : N.Word → Prop, ∀ x, P₂ x ↔ (N.IsCycleWord x ∧ x e ≠ 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  have k1 : N.numCycles ≤ Nat.card {x : N.Word // P₁ x ∨ P₂ x} := by
    apply natCard_le_of_imp
    intro x hx
    by_cases hxe : x e = 0
    · refine Or.inl ((hP₁ x).2 ⟨hx, fun g hg hge => hg ?_⟩)
      rw [hge]
      exact hxe
    · exact Or.inr ((hP₂ x).2 ⟨hx, hxe⟩)
  have k2 := natCard_or_le P₁ P₂
  have k3 : Nat.card {x : N.Word // P₁ x} = (N.sub fun g => g ≠ e).numCycles := by
    rw [N.numCycles_sub]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => hP₁ x)
  have k4 : Nat.card {x : N.Word // P₂ x} ≤ N.numPathsIn (fun g => g ≠ e) a b := by
    obtain ⟨φ, hφ⟩ : ∃ φ : {x : N.Word // P₂ x} →
        {x : N.Word // N.IsPathWord a b x ∧ Within x (fun g => g ≠ e)},
        ∀ x, (φ x).1 = x.1 + unitWord e := by
      refine ⟨fun x => ⟨x.1 + unitWord e, ?_, ?_⟩, fun _ => rfl⟩
      · have hx := (hP₂ x.1).1 x.2
        have hsub : N.IsSubword (x.1 + unitWord e) x.1 := (N.isSubword_unitWord hx.2).add_self
        apply N.isPathWord_of_minimal he.ne
        · rw [map_add, hx.1.boundary_eq_zero, zero_add, N.boundary_unitWord_of_joins he]
          rfl
        · intro y hy hy0
          refine Classical.not_not.1 fun hne => ?_
          have hyx := hx.1.eq_of_even_subword (fun g hg => hsub g (hy g hg)) hy0 hne
          have h1 := ((add_unitWord_ne_zero_iff hx.2 e).1 (hy e (by rw [hyx]; exact hx.2))).2
          exact h1 rfl
      · intro g hg
        exact ((add_unitWord_ne_zero_iff ((hP₂ x.1).1 x.2).2 g).1 hg).2
    apply Nat.card_le_card_of_injective φ
    intro x x' hxx
    have h : x.1 + unitWord e = x'.1 + unitWord e := by rw [← hφ x, ← hφ x', hxx]
    exact Subtype.ext (add_right_cancel h)
  omega

end Erdos1016.BoundaryTrace.Network

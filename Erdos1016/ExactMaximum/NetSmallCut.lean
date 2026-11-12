import Erdos1016.ExactMaximum.NetBridge

set_option autoImplicit false

/-!
# Small cuts of a cubic network

Section 6 of the paper "The maximum number of cycles in a graph of large rank" starts with a
count of edge ends: if `X` is a set of `n` vertices of a cubic multigraph and `d` edges leave
`X`, then the rank of `G[X]` is `(n - d)/2` plus the number of components of `G[X]`. So every cut
of size at most two is cyclic. This file proves these facts for a network in which every vertex
has degree three.

* `three_mul_card_eq`: `3 n = 2 (number of edges inside) + d`.
* `rank_side_ge`: the rank of a nonempty side is at least `(number of edges inside) + 1 - n`.
* `isCyclicCut_of_cutSize_le_two`: a cut with at most two crossing edges, with a vertex on each
  side, has a cycle in each side.
* `cutSize_ge_of_minimal`: if the smallest cyclic cut has `d ≤ 3` edges, then every cut with a
  vertex on each side has at least `d` edges.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance netSmallCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Cuts -/

/-- The number of edges that cross the cut `S`. -/
def cutSize (N : Network V E) (S : V → Prop) : ℕ := Nat.card {e : E // N.crosses S e}

/-- Both sides of the cut `S` contain a cycle. -/
def IsCyclicCut (N : Network V E) (S : V → Prop) : Prop :=
  0 < (N.sub (N.inside S)).numCycles ∧ 0 < (N.sub (N.outside S)).numCycles

/-- Every vertex has degree three. -/
def IsCubic (N : Network V E) : Prop := ∀ v, N.deg (fun _ => 1) v = 3

omit [Fintype V] [Fintype E] in
/-- The complement of `S` has the same crossing edges. -/
theorem crosses_not_iff (N : Network V E) (S : V → Prop) (e : E) :
    N.crosses (fun v => ¬ S v) e ↔ N.crosses S e :=
  not_congr not_iff_not

omit [Fintype V] [Fintype E] in
/-- The complement of `S` has the same number of crossing edges. -/
theorem cutSize_not (N : Network V E) (S : V → Prop) :
    N.cutSize (fun v => ¬ S v) = N.cutSize S :=
  Nat.card_congr (Equiv.subtypeEquivRight fun e => N.crosses_not_iff S e)

/-! ### Counting edge ends -/

omit [Fintype E] in
theorem sum_ite_eq_ite_nat (S : V → Prop) (c : ℕ) (u : V) :
    (∑ v, if S v then (if u = v then c else 0) else 0) = if S u then c else 0 := by
  rw [Finset.sum_eq_single u]
  · rw [if_pos rfl]
  · intro v _ hv
    rw [if_neg (Ne.symm hv)]
    exact ite_self 0
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- **Double counting.** The sum of the degrees of the vertices of `S` counts every edge once
for each of its ends in `S`. -/
theorem sum_deg_eq (N : Network V E) (S : V → Prop) :
    (∑ v, if S v then N.deg (fun _ => 1) v else 0) =
      ∑ e, ((if S (N.src e) then 1 else 0) + (if S (N.dst e) then 1 else 0)) := by
  have h1 : ∀ v, (if S v then N.deg (fun _ => 1) v else 0) =
      ∑ e, ((if S v then (if N.src e = v then 1 else 0) else 0) +
        (if S v then (if N.dst e = v then 1 else 0) else 0)) := by
    intro v
    by_cases hS : S v
    · simp only [if_pos hS]
      rw [deg_eq_sum]
      apply Finset.sum_congr rfl
      intro e _
      have hne := N.noLoops e
      by_cases hs : N.src e = v <;> by_cases hd : N.dst e = v
      · exact absurd (hs.trans hd.symm) hne
      · simp [hs, hd]
      · simp [hs, hd]
      · simp [hs, hd]
    · simp only [if_neg hS, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib, sum_ite_eq_ite_nat S 1 (N.src e),
    sum_ite_eq_ite_nat S 1 (N.dst e)]

/-- **The count of edge ends in a cubic network.** If `n` vertices are in `S`, then `3n` is
twice the number of edges inside `S` plus the number of crossing edges. -/
theorem three_mul_card_eq (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop) :
    3 * Nat.card {v : V // S v} =
      2 * Nat.card {e : E // N.inside S e} + N.cutSize S := by
  have h := N.sum_deg_eq S
  have hL : (∑ v, if S v then N.deg (fun _ => 1) v else 0) = 3 * Nat.card {v : V // S v} := by
    rw [natCard_subtype_eq_card_filter, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hS : S v
    · rw [if_pos hS, if_pos hS, hcubic v, mul_one]
    · rw [if_neg hS, if_neg hS, mul_zero]
  have hR : (∑ e, ((if S (N.src e) then 1 else 0) + (if S (N.dst e) then 1 else 0))) =
      2 * Nat.card {e : E // N.inside S e} + N.cutSize S := by
    unfold cutSize
    rw [natCard_subtype_eq_card_filter, natCard_subtype_eq_card_filter, Finset.card_filter,
      Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h1 : S (N.src e) <;> by_cases h2 : S (N.dst e)
    · have hi : N.inside S e := ⟨h1, h2⟩
      rw [if_pos h1, if_pos h2, if_pos hi, if_neg (N.not_crosses_of_inside hi)]
      omega
    · have hc : N.crosses S e := fun h => h2 (h.1 h1)
      rw [if_pos h1, if_neg h2, if_neg (N.not_inside_of_crosses hc), if_pos hc]
      omega
    · have hc : N.crosses S e := fun h => h1 (h.2 h2)
      rw [if_neg h1, if_pos h2, if_neg (N.not_inside_of_crosses hc), if_pos hc]
      omega
    · have ho : N.outside S e := ⟨h1, h2⟩
      rw [if_neg h1, if_neg h2, if_neg (N.not_inside_of_outside ho),
        if_neg (N.not_crosses_of_outside ho)]
      omega
  rw [← hL, h, hR]

/-! ### The rank of a side -/

omit [Fintype E] in
/-- If every edge of `M` has both ends in `S` and `S` is not empty, then `M` has at least one
component more than there are vertices outside `S`. -/
theorem natCard_component_ge (M : Network V E) (S : V → Prop) {s₀ : V} (hs₀ : S s₀)
    (hedge : ∀ e, S (M.src e) ∧ S (M.dst e)) :
    Nat.card {v : V // ¬ S v} + 1 ≤ Nat.card M.Component := by
  have hiso : ∀ v w, ¬ S v → M.graph.Reachable v w → v = w := by
    intro v w hv hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => rfl
    | cons hadj _ =>
      exfalso
      obtain ⟨e, h | h⟩ := hadj
      · exact hv (h.1 ▸ (hedge e).1)
      · exact hv (h.2 ▸ (hedge e).2)
  let g : Option {v : V // ¬ S v} → M.Component := fun o =>
    match o with
    | none => M.graph.connectedComponentMk s₀
    | some v => M.graph.connectedComponentMk v.1
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exfalso
      have h1 : M.graph.connectedComponentMk s₀ = M.graph.connectedComponentMk b.1 := hab
      have h2 : M.graph.Reachable s₀ b.1 := SimpleGraph.ConnectedComponent.exact h1
      have h3 : b.1 = s₀ := hiso b.1 s₀ b.2 h2.symm
      exact b.2 (h3 ▸ hs₀)
    · exfalso
      have h1 : M.graph.connectedComponentMk a.1 = M.graph.connectedComponentMk s₀ := hab
      have h2 : M.graph.Reachable a.1 s₀ := SimpleGraph.ConnectedComponent.exact h1
      have h3 : a.1 = s₀ := hiso a.1 s₀ a.2 h2
      exact a.2 (h3 ▸ hs₀)
    · have h1 : M.graph.connectedComponentMk a.1 = M.graph.connectedComponentMk b.1 := hab
      have h2 : M.graph.Reachable a.1 b.1 := SimpleGraph.ConnectedComponent.exact h1
      exact congrArg some (Subtype.ext (hiso a.1 b.1 a.2 h2))
  have hcard := Nat.card_le_card_of_injective g hg
  rw [Finite.card_option] at hcard
  exact hcard

/-- **The rank of a nonempty side.** It is at least the number of the edges inside `S` plus one
minus the number of the vertices of `S`. -/
theorem rank_side_ge (N : Network V E) (S : V → Prop) {s₀ : V} (hs₀ : S s₀) :
    Nat.card {e : E // N.inside S e} + 1 ≤
      networkRank (N.sub (N.inside S)) + Nat.card {v : V // S v} := by
  have e1 := network_rank_euler (N.sub (N.inside S))
  simp only [← Nat.card_eq_fintype_card] at e1
  have c1 := natCard_component_ge (N.sub (N.inside S)) S hs₀ (fun e => e.2)
  have hV : Nat.card V = Nat.card {v : V // S v} + Nat.card {v : V // ¬ S v} := by
    rw [← natCard_or_of_disjoint (fun v : V => S v) (fun v => ¬ S v) (fun v h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun v => Classical.em (S v)))).symm
  omega

/-- In a cubic network, a nonempty side of a cut with at most two crossing edges has positive
rank. -/
theorem rank_side_pos_of_cubic (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop) {s₀ : V}
    (hs₀ : S s₀) (hd : N.cutSize S ≤ 2) : 0 < networkRank (N.sub (N.inside S)) := by
  have h1 := N.three_mul_card_eq hcubic S
  have h2 := N.rank_side_ge S hs₀
  have h3 : 0 < Nat.card {v : V // S v} := by
    haveI : Nonempty {v : V // S v} := ⟨⟨s₀, hs₀⟩⟩
    exact Nat.card_pos
  omega

/-- **A cut with at most two edges is cyclic.** In a cubic network, let the cut `S` have a
vertex on each side and at most two crossing edges. Then both sides contain a cycle. -/
theorem isCyclicCut_of_cutSize_le_two (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop)
    {s₀ t₀ : V} (hs₀ : S s₀) (ht₀ : ¬ S t₀) (hd : N.cutSize S ≤ 2) : N.IsCyclicCut S := by
  refine ⟨numCycles_pos_of_rank_pos _ (N.rank_side_pos_of_cubic hcubic S hs₀ hd), ?_⟩
  have hd' : N.cutSize (fun v => ¬ S v) ≤ 2 := by
    rw [N.cutSize_not S]
    exact hd
  have h := N.rank_side_pos_of_cubic hcubic (fun v => ¬ S v) ht₀ hd'
  exact numCycles_pos_of_rank_pos _ h

/-- **No smaller cut.** In a cubic network, let `d ≤ 3` be such that every cyclic cut has at
least `d` crossing edges. Then every cut with a vertex on each side has at least `d` crossing
edges. -/
theorem cutSize_ge_of_minimal (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop) {s₀ t₀ : V}
    (hs₀ : S s₀) (ht₀ : ¬ S t₀) : d ≤ N.cutSize S := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h2 : N.cutSize S ≤ 2 := by omega
  have := hmin S (N.isCyclicCut_of_cutSize_le_two hcubic S hs₀ ht₀ h2)
  omega

/-! ### The sides of a smallest cyclic cut are connected -/

/-- Two properties that exclude each other and both imply a third one. -/
theorem natCard_add_le_of_imp {α : Type*} [Finite α] (P Q R : α → Prop) (hP : ∀ a, P a → R a)
    (hQ : ∀ a, Q a → R a) (hPQ : ∀ a, P a → Q a → False) :
    Nat.card {a // P a} + Nat.card {a // Q a} ≤ Nat.card {a // R a} := by
  rw [← natCard_or_of_disjoint P Q hPQ]
  apply Nat.card_le_card_of_injective
    (fun a : {a // P a ∨ Q a} => (⟨a.1, a.2.elim (hP a.1) (hQ a.1)⟩ : {a // R a}))
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext h

/-- **A side of a smallest cyclic cut is connected.** In a cubic network, let `1 ≤ d ≤ 3`, let
every cyclic cut have at least `d` crossing edges, and let the cut `S` have exactly `d` crossing
edges. Then every vertex of `S` is joined to `s₀ ∈ S` by edges inside `S`. -/
theorem reachable_inside_of_minimal (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hd1 : 1 ≤ d) (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = d) {s₀ t₀ : V} (hs₀ : S s₀) (ht₀ : ¬ S t₀) :
    ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u := by
  intro u hu
  refine Classical.not_not.1 fun hnot => ?_
  -- the two parts of `S`
  obtain ⟨C, hC⟩ : ∃ C : V → Prop,
      ∀ v, C v ↔ (S v ∧ (N.sub (N.inside S)).graph.Reachable s₀ v) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : V → Prop,
      ∀ v, D v ↔ (S v ∧ ¬ (N.sub (N.inside S)).graph.Reachable s₀ v) := ⟨_, fun _ => Iff.rfl⟩
  have hCs : C s₀ := (hC s₀).2 ⟨hs₀, SimpleGraph.Reachable.refl _⟩
  have hCt : ¬ C t₀ := fun h => ht₀ ((hC t₀).1 h).1
  have hDu : D u := (hD u).2 ⟨hu, hnot⟩
  have hDs : ¬ D s₀ := fun h => ((hD s₀).1 h).2 (SimpleGraph.Reachable.refl _)
  have h1 := N.cutSize_ge_of_minimal hcubic hd hmin C hCs hCt
  have h2 := N.cutSize_ge_of_minimal hcubic hd hmin D hDu hDs
  -- an edge inside `S` joins two vertices of the same part
  have hin : ∀ e, N.inside S e → ((N.sub (N.inside S)).graph.Reachable s₀ (N.src e) ↔
      (N.sub (N.inside S)).graph.Reachable s₀ (N.dst e)) := by
    intro e he
    have hadj : (N.sub (N.inside S)).graph.Adj (N.src e) (N.dst e) :=
      ⟨⟨e, he⟩, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  -- a crossing edge of a part is a crossing edge of `S`
  have hCS : ∀ e, N.crosses C e → N.crosses S e := by
    intro e he
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · exfalso
      apply he
      rw [hC, hC]
      exact ⟨fun k => ⟨h.2, (hin e h).1 k.2⟩, fun k => ⟨h.1, (hin e h).2 k.2⟩⟩
    · exfalso
      apply he
      rw [hC, hC]
      exact ⟨fun k => absurd k.1 h.1, fun k => absurd k.1 h.2⟩
    · exact h
  have hDS : ∀ e, N.crosses D e → N.crosses S e := by
    intro e he
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · exfalso
      apply he
      rw [hD, hD]
      exact ⟨fun k => ⟨h.2, fun k' => k.2 ((hin e h).2 k')⟩,
        fun k => ⟨h.1, fun k' => k.2 ((hin e h).1 k')⟩⟩
    · exfalso
      apply he
      rw [hD, hD]
      exact ⟨fun k => absurd k.1 h.1, fun k => absurd k.1 h.2⟩
    · exact h
  -- no edge crosses both parts
  have hCD : ∀ e, N.crosses C e → N.crosses D e → False := by
    intro e heC heD
    have hS' := hCS e heC
    by_cases k1 : S (N.src e)
    · have k2 : ¬ S (N.dst e) := fun k2 => hS' ⟨fun _ => k2, fun _ => k1⟩
      have c2 : ¬ C (N.dst e) := fun h => k2 ((hC _).1 h).1
      have d2 : ¬ D (N.dst e) := fun h => k2 ((hD _).1 h).1
      have c1 : C (N.src e) := Classical.not_not.1 fun h => heC ⟨fun k => absurd k h, fun k => absurd k c2⟩
      have d1 : D (N.src e) := Classical.not_not.1 fun h => heD ⟨fun k => absurd k h, fun k => absurd k d2⟩
      exact ((hD _).1 d1).2 ((hC _).1 c1).2
    · have c1 : ¬ C (N.src e) := fun h => k1 ((hC _).1 h).1
      have d1 : ¬ D (N.src e) := fun h => k1 ((hD _).1 h).1
      have c2 : C (N.dst e) := Classical.not_not.1 fun h => heC ⟨fun k => absurd k c1, fun k => absurd k h⟩
      have d2 : D (N.dst e) := Classical.not_not.1 fun h => heD ⟨fun k => absurd k d1, fun k => absurd k h⟩
      exact ((hD _).1 d2).2 ((hC _).1 c2).2
  have h3 := natCard_add_le_of_imp (fun e : E => N.crosses C e) (fun e => N.crosses D e)
    (fun e => N.crosses S e) hCS hDS hCD
  have h4 : N.cutSize C + N.cutSize D ≤ N.cutSize S := h3
  omega

/-! ### No vertex is on two edges of a smallest cyclic cut -/

omit [Fintype V] in
/-- A side that contains a cycle has two different vertices. -/
theorem exists_ne_of_numCycles_pos (N : Network V E) (S : V → Prop)
    (hcyc : 0 < (N.sub (N.inside S)).numCycles) (v : V) : ∃ u, S u ∧ u ≠ v := by
  rw [numCycles_sub] at hcyc
  obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.1 hcyc
  obtain ⟨g, hg⟩ := hx.exists_edge
  have hin := hw g hg
  by_cases h : N.src g = v
  · refine ⟨N.dst g, hin.2, fun h' => N.noLoops g (h.trans h'.symm)⟩
  · exact ⟨N.src g, hin.1, h⟩

/-- **No vertex is on two edges of a smallest cyclic cut.** In a cubic network, let `d ≤ 3`,
let every cyclic cut have at least `d` crossing edges, and let the cut `S` have exactly `d`
crossing edges and a cycle in its first side. Then two different crossing edges do not have the
same end in `S`. -/
theorem false_of_two_crossing_at (N : Network V E) (hcubic : N.IsCubic) {d : ℕ} (hd : d ≤ 3)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → d ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = d) (hcyc : 0 < (N.sub (N.inside S)).numCycles) {e f : E}
    {v w₁ w₂ : V} (hef : e ≠ f) (he : N.Joins e v w₁) (hf : N.Joins f v w₂) (hv : S v)
    (hw₁ : ¬ S w₁) (hw₂ : ¬ S w₂) : False := by
  obtain ⟨u₀, hu₀, hu₀v⟩ := N.exists_ne_of_numCycles_pos S hcyc v
  have hce : N.crosses S e := N.crosses_of_joins he hv hw₁
  have hcf : N.crosses S f := N.crosses_of_joins hf hv hw₂
  -- the cut without the vertex `v`
  obtain ⟨S', hS'⟩ : ∃ S' : V → Prop, ∀ u, S' u ↔ (S u ∧ u ≠ v) := ⟨_, fun _ => Iff.rfl⟩
  have h1 := N.cutSize_ge_of_minimal hcubic hd hmin S' ((hS' u₀).2 ⟨hu₀, hu₀v⟩)
    (fun h => ((hS' v).1 h).2 rfl)
  -- the edges at `v`
  have hfour : ∀ g g' : E, g ≠ g' → g ≠ e → g ≠ f → g' ≠ e → g' ≠ f →
      (N.src g = v ∨ N.dst g = v) → (N.src g' = v ∨ N.dst g' = v) → False := by
    intro g g' k1 k2 k3 k4 k5 hg hg'
    have hsub : ({e, f, g, g'} : Finset E) ⊆ Finset.univ.filter
        (fun k : E => (fun _ => (1 : Bit)) k ≠ 0 ∧ (N.src k = v ∨ N.dst k = v)) := by
      intro k hk
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hk
      refine Finset.mem_filter.2 ⟨Finset.mem_univ k, one_ne_zero, ?_⟩
      rcases hk with hk | hk | hk | hk
      · rw [hk]
        exact he.at_left
      · rw [hk]
        exact hf.at_left
      · rw [hk]
        exact hg
      · rw [hk]
        exact hg'
    have hcard : ({e, f, g, g'} : Finset E).card = 4 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
      · rw [Finset.mem_singleton]
        exact k1
      · rw [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact k3 h.symm
        · exact k5 h.symm
      · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h | h)
        · exact hef h
        · exact k2 h.symm
        · exact k4 h.symm
    have hle := Finset.card_le_card hsub
    have hdeg : (Finset.univ.filter
        (fun k : E => (fun _ => (1 : Bit)) k ≠ 0 ∧ (N.src k = v ∨ N.dst k = v))).card = 3 :=
      hcubic v
    omega
  -- an edge that is not at `v` crosses both cuts or none
  have hnot_at : ∀ g, ¬ (N.src g = v ∨ N.dst g = v) → (N.crosses S' g ↔ N.crosses S g) := by
    intro g hg
    have k1 : N.src g ≠ v := fun h => hg (Or.inl h)
    have k2 : N.dst g ≠ v := fun h => hg (Or.inr h)
    have e1 : S' (N.src g) ↔ S (N.src g) := by
      rw [hS']
      exact ⟨fun h => h.1, fun h => ⟨h, k1⟩⟩
    have e2 : S' (N.dst g) ↔ S (N.dst g) := by
      rw [hS']
      exact ⟨fun h => h.1, fun h => ⟨h, k2⟩⟩
    unfold crosses
    rw [e1, e2]
  -- an edge at `v` that crosses the new cut is inside `S`
  have hat : ∀ g, (N.src g = v ∨ N.dst g = v) → N.crosses S' g → N.inside S g := by
    intro g hg hc
    have hv' : ¬ S' v := fun h => ((hS' v).1 h).2 rfl
    rcases hg with hg | hg
    · have k : S' (N.dst g) := Classical.not_not.1 fun k =>
        hc ⟨fun h => absurd (hg ▸ h) hv', fun h => absurd h k⟩
      exact ⟨hg ▸ hv, ((hS' _).1 k).1⟩
    · have k : S' (N.src g) := Classical.not_not.1 fun k =>
        hc ⟨fun h => absurd h k, fun h => absurd (hg ▸ h) hv'⟩
      exact ⟨((hS' _).1 k).1, hg ▸ hv⟩
  -- the injective map
  obtain ⟨φ, hφ⟩ : ∃ φ : {g : E // N.crosses S' g} → {g : E // N.crosses S g ∧ g ≠ f},
      ∀ g, (φ g).1 = if (N.src g.1 = v ∨ N.dst g.1 = v) then e else g.1 := by
    refine ⟨fun g => ⟨if (N.src g.1 = v ∨ N.dst g.1 = v) then e else g.1, ?_⟩, fun _ => rfl⟩
    by_cases hg : N.src g.1 = v ∨ N.dst g.1 = v
    · rw [if_pos hg]
      exact ⟨hce, hef⟩
    · rw [if_neg hg]
      exact ⟨(hnot_at g.1 hg).1 g.2, fun h => hg (h ▸ hf.at_left)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hφ, hφ] at h
    by_cases ha : N.src a.1 = v ∨ N.dst a.1 = v <;> by_cases hb : N.src b.1 = v ∨ N.dst b.1 = v
    · -- both edges are inside `S` and at `v`
      refine Classical.not_not.1 fun hne => ?_
      have hne' : a.1 ≠ b.1 := fun h' => hne (Subtype.ext h')
      have ia := hat a.1 ha a.2
      have ib := hat b.1 hb b.2
      exact hfour a.1 b.1 hne' (fun h' => N.not_inside_of_crosses hce (h' ▸ ia))
        (fun h' => N.not_inside_of_crosses hcf (h' ▸ ia))
        (fun h' => N.not_inside_of_crosses hce (h' ▸ ib))
        (fun h' => N.not_inside_of_crosses hcf (h' ▸ ib)) ha hb
    · rw [if_pos ha, if_neg hb] at h
      exact absurd (h ▸ he.at_left) hb
    · rw [if_neg ha, if_pos hb] at h
      exact absurd (h.symm ▸ he.at_left) ha
    · rw [if_neg ha, if_neg hb] at h
      exact Subtype.ext h
  have h2 := Nat.card_le_card_of_injective φ hinj
  have h3 := natCard_add_le_of_imp (fun g : E => N.crosses S g ∧ g ≠ f) (fun g => g = f)
    (fun g => N.crosses S g) (fun g h => h.1) (fun g h => h ▸ hcf) (fun g h h' => h.2 h')
  have h4 : Nat.card {g : E // g = f} = 1 := Nat.card_unique
  have h5 : N.cutSize S' ≤ Nat.card {g : E // N.crosses S g ∧ g ≠ f} := h2
  have h6 : Nat.card {g : E // N.crosses S g ∧ g ≠ f} + Nat.card {g : E // g = f} ≤
      N.cutSize S := h3
  omega

end Erdos1016.BoundaryTrace.Network

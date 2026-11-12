import Erdos1016.ExactMaximum.ExitPole
import Erdos1016.ExactMaximum.ShortestCycle
import Erdos1016.ExactMaximum.CyclicShore

set_option autoImplicit false

/-!
# One exit term in the proof of Theorem 7.1

Let `C` be a shortest cycle of a connected cubic network `N`, with at least five edges, and let
`e` be an edge of `C` (`ShortSetting`). The proof of Theorem 7.1 of the paper "The maximum number
of cycles in a graph of large rank" deletes `e` and a set `D` of vertices of `C`. The edges that
remain are `keep e D`. This file bounds the number of paths between two vertices `x`, `y` in what
remains (`exit_bound`):

`2^(m+1) P ≤ (2^m + 2) 2^(r-1-k) + 2^(m+1) 2^B`,

where `k` is at most the number of edges of `C` other than `e` with an end in `D`. The hypotheses
are that every vertex outside `D` keeps at least two edges, that `x` and `y` keep at most two
edges, that `N` has no cyclic cut with at most four crossing edges, and the statement of
`CyclicShore.lean` for one pair of parameters (`hshore`).

The steps are the steps "The rank of `K_p`", "The shape of `K_p`" and "The count" of the paper:
the component `K` of `x` is a pole with at most `12 |C| + 2` ports; its rank is at most
`r - 1 - k`, by the count of `rank_compEdges_add_le`, because `1 + k + |D|` edges are deleted
and only the `|D|` deleted vertices are isolated; if the rank of `K` is at least `B`, then `K`
has no cubic cyclic shore, so fewer than `(1/2 + 2^(-m)) 2^(rank K)` paths join `x` and `y`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance shortCycleExitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Degrees in a part -/

section Degrees

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- If some edge at `v` is outside `q`, then `v` has smaller degree in `q`. -/
theorem deg_restrict_lt (N : Network V E) (q : E → Prop) {v : V} {g : E}
    (hg : N.src g = v ∨ N.dst g = v) (hq : ¬ q g) :
    (N.sub q).deg (fun _ => 1) v < N.deg (fun _ => 1) v := by
  rw [N.deg_sub_ones]
  unfold deg
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ g, one_ne_zero, hg⟩, fun hmem => ?_⟩
    exact hq ((restrict_ne_zero_iff _ _ g).1 (Finset.mem_filter.1 hmem).2.1).1
  · intro k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ k, one_ne_zero, (Finset.mem_filter.1 hk).2.2⟩

omit [Fintype V] in
/-- If at most one edge at `v` is outside `q`, then `v` loses at most one from its degree. -/
theorem deg_le_deg_restrict_add_one (N : Network V E) (q : E → Prop) {v : V}
    (h : ∀ g g', (N.src g = v ∨ N.dst g = v) → ¬ q g → (N.src g' = v ∨ N.dst g' = v) → ¬ q g' →
      g = g') : N.deg (fun _ => 1) v ≤ (N.sub q).deg (fun _ => 1) v + 1 := by
  rw [N.deg_sub_ones]
  unfold deg
  obtain ⟨A, hA⟩ : ∃ A : Finset E, A = Finset.univ.filter
      (fun g : E => (fun _ => (1 : Bit)) g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset E, B = Finset.univ.filter
      (fun g : E => restrict (fun _ => (1 : Bit)) q g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)) :=
    ⟨_, rfl⟩
  rw [← hA, ← hB]
  have memA : ∀ g, g ∈ A ↔ (N.src g = v ∨ N.dst g = v) := by
    intro g
    rw [hA, Finset.mem_filter]
    exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_univ g, one_ne_zero, h⟩⟩
  have memB : ∀ g, g ∈ B ↔ (q g ∧ (N.src g = v ∨ N.dst g = v)) := by
    intro g
    rw [hB, Finset.mem_filter, restrict_ne_zero_iff]
    exact ⟨fun h => ⟨h.2.1.1, h.2.2⟩, fun h => ⟨Finset.mem_univ g, ⟨h.1, one_ne_zero⟩, h.2⟩⟩
  have hBA : B ⊆ A := fun g hg => (memA g).2 ((memB g).1 hg).2
  have h1 := Finset.card_sdiff_add_card_eq_card hBA
  have h2 : (A \ B).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro g hg g' hg'
    have k1 := Finset.mem_sdiff.1 hg
    have k2 := Finset.mem_sdiff.1 hg'
    exact h g g' ((memA g).1 k1.1) (fun hq => k1.2 ((memB g).2 ⟨hq, (memA g).1 k1.1⟩))
      ((memA g').1 k2.1) (fun hq => k2.2 ((memB g').2 ⟨hq, (memA g').1 k2.1⟩))
  omega

omit [Fintype V] in
/-- Two different edges of `q` at `v` give degree at least two in `q`. -/
theorem two_le_deg_restrict (N : Network V E) (q : E → Prop) {v : V} {g g' : E} (hne : g ≠ g')
    (hg : N.src g = v ∨ N.dst g = v) (hq : q g) (hg' : N.src g' = v ∨ N.dst g' = v)
    (hq' : q g') : 2 ≤ (N.sub q).deg (fun _ => 1) v := by
  rw [N.deg_sub_ones]
  unfold deg
  have h1 : 1 < (Finset.univ.filter fun k : E =>
      restrict (fun _ => (1 : Bit)) q k ≠ 0 ∧ (N.src k = v ∨ N.dst k = v)).card := by
    rw [Finset.one_lt_card]
    refine ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ g, ?_, hg⟩, g',
      Finset.mem_filter.2 ⟨Finset.mem_univ g', ?_, hg'⟩, hne⟩
    · rw [restrict_ne_zero_iff]
      exact ⟨hq, one_ne_zero⟩
    · rw [restrict_ne_zero_iff]
      exact ⟨hq', one_ne_zero⟩
  exact h1

omit [Fintype V] in
/-- A vertex without an edge of `q` has degree zero in `q`. -/
theorem deg_restrict_eq_zero (N : Network V E) (q : E → Prop) {v : V}
    (h : ∀ g, (N.src g = v ∨ N.dst g = v) → ¬ q g) : (N.sub q).deg (fun _ => 1) v = 0 := by
  rw [N.deg_sub_ones]
  apply N.deg_eq_zero_of_forall
  intro g hg
  exact restrict_apply_of_neg _ (h g hg)

omit [Fintype V] in
/-- The degree in a part is at most the degree. -/
theorem deg_restrict_le (N : Network V E) (q : E → Prop) (v : V) :
    (N.sub q).deg (fun _ => 1) v ≤ N.deg (fun _ => 1) v := by
  rw [N.deg_sub_ones]
  unfold deg
  apply Finset.card_le_card
  intro k hk
  exact Finset.mem_filter.2 ⟨Finset.mem_univ k, one_ne_zero, (Finset.mem_filter.1 hk).2.2⟩

omit [Fintype V] [Fintype E] in
/-- A vertex of degree zero in `q` is joined to itself only. -/
theorem eq_of_reachable_of_deg_eq_zero (N : Network V E) (q : E → Prop)
    [Fintype {g : E // q g}] {x v : V} (h : (N.sub q).graph.Reachable x v)
    (h0 : (N.sub q).deg (fun _ => 1) v = 0) : x = v := by
  refine (N.sub q).mem_of_reachable_of_closed (fun u => u = v) ?_ h.symm rfl
  intro k
  have h1 := (N.sub q).deg_src_pos (x := fun _ => 1) (e := k) one_ne_zero
  have h2 := (N.sub q).deg_dst_pos (x := fun _ => 1) (e := k) one_ne_zero
  constructor
  · intro hs
    rw [hs] at h1
    omega
  · intro hd
    rw [hd] at h2
    omega

omit [Fintype V] in
/-- If every vertex of a set is an end of an edge of a set of edges, then the set has at most
twice as many vertices as there are edges. -/
theorem natCard_le_two_mul_of_incident [Finite V] (N : Network V E) (A : V → Prop)
    (P : E → Prop) (h : ∀ v, A v → ∃ g, P g ∧ (N.src g = v ∨ N.dst g = v)) :
    Nat.card {v : V // A v} ≤ 2 * Nat.card {g : E // P g} := by
  have h' : ∀ v : {v : V // A v}, ∃ g : E, P g ∧ (N.src g = v.1 ∨ N.dst g = v.1) :=
    fun v => h v.1 v.2
  choose G hG using h'
  obtain ⟨φ, hφ⟩ : ∃ φ : {v : V // A v} → {g : E // P g} × Bool,
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

omit [Fintype V] in
/-- A path within `q` from `x` lies in the component of `x`. -/
theorem IsPathWord.within_compEdges {N : Network V E} {q : E → Prop} {x y : V} {z : N.Word}
    (hz : N.IsPathWord x y z) (hw : Within z q) : Within z (N.compEdges q x) := by
  intro g hg
  refine ⟨hw g hg, ?_⟩
  have h1 := hz.2.2.2.2 (N.src g) (N.deg_src_pos hg)
  rw [← N.sub_support_graph z] at h1
  exact N.reachable_sub_mono (fun k hk => hw k hk) h1

end Degrees

/-! ### The setting -/

variable {V E : Type} [Fintype V] [Fintype E]

/-- The edges that remain when the edge `e` and the vertices of `D` are deleted. -/
def keep (N : Network V E) (e : E) (D : V → Prop) (g : E) : Prop :=
  g ≠ e ∧ ¬ D (N.src g) ∧ ¬ D (N.dst g)

/-- The edges of `C` other than `e` with an end in `D`. -/
def arcEdges (N : Network V E) (C : N.Word) (e : E) (D : V → Prop) (g : E) : Prop :=
  g ≠ e ∧ C g ≠ 0 ∧ (D (N.src g) ∨ D (N.dst g))

/-- **The setting of the count.** `N` is a connected cubic network, `C` is a cycle with at least
five edges such that no cycle has fewer edges, and `e` is an edge of `C`. -/
structure ShortSetting (N : Network V E) (C : N.Word) (e : E) : Prop where
  conn : N.graph.Connected
  cubic : N.IsCubic
  cyc : N.IsCycleWord C
  short : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z
  five : 5 ≤ size C
  mem : C e ≠ 0

namespace ShortSetting

variable {N : Network V E} {C : N.Word} {e : E}

omit [Fintype V] in
/-- A deleted vertex has no edge left. -/
theorem deg_keep_of_mem (_H : N.ShortSetting C e) (D : V → Prop) {v : V} (hv : D v) :
    (N.sub (N.keep e D)).deg (fun _ => 1) v = 0 := by
  apply N.deg_restrict_eq_zero
  intro g hg hk
  rcases hg with hg | hg
  · exact hk.2.1 (by rw [hg]; exact hv)
  · exact hk.2.2 (by rw [hg]; exact hv)

/-- **A vertex outside the cycle keeps at least two edges.** -/
theorem two_le_deg_keep_of_off (H : N.ShortSetting C e) (D : V → Prop)
    (hD : ∀ v, D v → 0 < N.deg C v) {v : V} (hv : N.deg C v = 0) :
    2 ≤ (N.sub (N.keep e D)).deg (fun _ => 1) v := by
  have h1 := N.deg_le_deg_restrict_add_one (N.keep e D) (v := v) (by
    intro g g' hg hq hg' hq'
    refine Classical.not_not.1 fun hne => ?_
    -- an edge at `v` that is deleted ends in `D`
    have key : ∀ k, (N.src k = v ∨ N.dst k = v) → ¬ N.keep e D k →
        ∃ u, N.Joins k v u ∧ 0 < N.deg C u := by
      intro k hk hkq
      obtain ⟨u, hu⟩ := N.exists_joins hk
      refine ⟨u, hu, ?_⟩
      have hke : k ≠ e := by
        intro hke
        have h0 := N.eq_zero_of_deg_eq_zero hv hk
        rw [hke] at h0
        exact H.mem h0
      have hDu : D u := by
        refine Classical.not_not.1 fun hDu => hkq ⟨hke, ?_, ?_⟩
        · rcases hu with ⟨k1, _⟩ | ⟨k1, _⟩
          · rw [k1]
            exact fun hDv => by have := hD v hDv; omega
          · rw [k1]
            exact hDu
        · rcases hu with ⟨_, k2⟩ | ⟨_, k2⟩
          · rw [k2]
            exact hDu
          · rw [k2]
            exact fun hDv => by have := hD v hDv; omega
      exact hD u hDu
    obtain ⟨u, hu, hCu⟩ := key g hg hq
    obtain ⟨u', hu', hCu'⟩ := key g' hg' hq'
    exact H.cyc.no_two_feet H.short H.five hne hu hu' hv hCu hCu')
  have h2 := H.cubic v
  omega

/-- **The deleted edges, from below.** At least `1 + k + |D|` edges are deleted, where `k` is the
number of edges of `C` other than `e` with an end in `D`: the edge `e`, these `k` edges, and
the exit edges of the vertices of `D`. -/
theorem natCard_not_keep_ge (H : N.ShortSetting C e) (D : V → Prop)
    (hD : ∀ v, D v → 0 < N.deg C v) :
    1 + Nat.card {g : E // N.arcEdges C e D g} + Nat.card {v : V // D v} ≤
      Nat.card {g : E // ¬ N.keep e D g} := by
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : E → Prop, ∀ g, P₃ g ↔ (C g = 0 ∧ (D (N.src g) ∨ D (N.dst g))) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₁₂, hP₁₂⟩ : ∃ P : E → Prop, ∀ g, P g ↔ (g = e ∨ N.arcEdges C e D g) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hnk : ∀ g, (D (N.src g) ∨ D (N.dst g)) → ¬ N.keep e D g := by
    intro g hg hk
    rcases hg with hg | hg
    · exact hk.2.1 hg
    · exact hk.2.2 hg
  have k1 : Nat.card {g : E // g = e} + Nat.card {g : E // N.arcEdges C e D g} ≤
      Nat.card {g : E // P₁₂ g} :=
    natCard_add_le_of_imp (fun g : E => g = e) (fun g => N.arcEdges C e D g) P₁₂
      (fun g h => (hP₁₂ g).2 (Or.inl h)) (fun g h => (hP₁₂ g).2 (Or.inr h))
      (fun g h h' => h'.1 h)
  have k2 : Nat.card {g : E // P₁₂ g} + Nat.card {g : E // P₃ g} ≤
      Nat.card {g : E // ¬ N.keep e D g} :=
    natCard_add_le_of_imp P₁₂ P₃ (fun g => ¬ N.keep e D g)
    (by
      intro g h hk
      rcases (hP₁₂ g).1 h with h | h
      · exact hk.1 h
      · exact hnk g h.2.2 hk)
    (fun g h => hnk g ((hP₃ g).1 h).2)
    (by
      intro g h h'
      have h3 := (hP₃ g).1 h'
      rcases (hP₁₂ g).1 h with h | h
      · rw [h] at h3
        exact H.mem h3.1
      · exact h.2.1 h3.1)
  have k3 : Nat.card {g : E // g = e} = 1 := Nat.card_unique
  -- the exit edges of the vertices of `D`
  have hex : ∀ v : {v : V // D v}, ∃ f : E, C f = 0 ∧ (N.src f = v.1 ∨ N.dst f = v.1) ∧
      ∀ u, (N.src f = u ∨ N.dst f = u) → 0 < N.deg C u → u = v.1 := by
    intro v
    obtain ⟨f, w, hfw, hCf, -⟩ := H.cyc.exists_exit H.cubic (hD v.1 v.2)
    have hw := H.cyc.deg_exit_eq_zero H.short (by have := H.five; omega) hfw hCf (hD v.1 v.2)
    refine ⟨f, hCf, hfw.at_left, ?_⟩
    intro u hu hCu
    rcases hfw with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rcases hu with hu | hu
      · rw [← hu, k1]
      · rw [← hu, k2] at hCu
        omega
    · rcases hu with hu | hu
      · rw [← hu, k1] at hCu
        omega
      · rw [← hu, k2]
  choose F hF using hex
  have k4 : Nat.card {v : V // D v} ≤ Nat.card {g : E // P₃ g} := by
    obtain ⟨φ, hφ⟩ : ∃ φ : {v : V // D v} → {g : E // P₃ g}, ∀ v, (φ v).1 = F v := by
      refine ⟨fun v => ⟨F v, (hP₃ _).2 ⟨(hF v).1, ?_⟩⟩, fun _ => rfl⟩
      rcases (hF v).2.1 with h | h
      · exact Or.inl (by rw [h]; exact v.2)
      · exact Or.inr (by rw [h]; exact v.2)
    apply Nat.card_le_card_of_injective φ
    intro v v' hvv
    have h1 : F v = F v' := by rw [← hφ v, ← hφ v', hvv]
    have h2 := (hF v').2.1
    rw [← h1] at h2
    exact Subtype.ext ((hF v).2.2 v'.1 h2 (hD v'.1 v'.2)).symm
  omega

/-- **The deleted edges, from above.** At most `1 + 6 |C|` edges are deleted. -/
theorem natCard_not_keep_le (H : N.ShortSetting C e) (D : V → Prop)
    (hD : ∀ v, D v → 0 < N.deg C v) :
    Nat.card {g : E // ¬ N.keep e D g} ≤ 1 + 6 * size C := by
  obtain ⟨S, hS⟩ : ∃ S : V → Prop, ∀ v, S v ↔ 0 < N.deg C v := ⟨_, fun _ => Iff.rfl⟩
  -- the vertices of the cycle
  have h1 : Nat.card {v : V // S v} ≤ 2 * Nat.card {g : E // C g ≠ 0} := by
    apply N.natCard_le_two_mul_of_incident S (fun g => C g ≠ 0)
    intro v hv
    exact N.exists_edge_of_deg_pos ((hS v).1 hv)
  have h2 : Nat.card {g : E // C g ≠ 0} = size C := by
    rw [natCard_subtype_eq_card_filter]
    unfold size
    apply congrArg Finset.card
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- the edges with an end on the cycle
  have h3 := N.three_mul_card_eq H.cubic S
  have h4 : Nat.card {g : E // ¬ N.keep e D g} ≤
      Nat.card {g : E // g = e ∨ (N.inside S g ∨ N.crosses S g)} := by
    apply natCard_le_of_imp
    intro g hg
    by_cases hge : g = e
    · exact Or.inl hge
    · right
      rcases N.inside_or_outside_or_crosses S g with h | h | h
      · exact Or.inl h
      · exfalso
        apply hg
        refine ⟨hge, fun hd => h.1 ((hS _).2 (hD _ hd)), fun hd => h.2 ((hS _).2 (hD _ hd))⟩
      · exact Or.inr h
  have h5 : Nat.card {g : E // g = e ∨ (N.inside S g ∨ N.crosses S g)} ≤
      Nat.card {g : E // g = e} + Nat.card {g : E // N.inside S g ∨ N.crosses S g} :=
    natCard_or_le (fun g : E => g = e) (fun g => N.inside S g ∨ N.crosses S g)
  have h6 : Nat.card {g : E // N.inside S g ∨ N.crosses S g} ≤
      Nat.card {g : E // N.inside S g} + Nat.card {g : E // N.crosses S g} :=
    natCard_or_le (fun g : E => N.inside S g) (fun g => N.crosses S g)
  have h7 : Nat.card {g : E // g = e} = 1 := Nat.card_unique
  have h8 : Nat.card {g : E // N.crosses S g} = N.cutSize S := rfl
  omega

end ShortSetting

/-! ### The bound for one exit term -/

/-- **One exit term.** In the setting of the count, let `N` have no cyclic cut with at most four
crossing edges, and let the statement of `CyclicShore.lean` hold for the numbers `m`, `G`, `B`,
where `12 |C| ≤ G`. Let `D` be a set of vertices of `C` such that every vertex outside `D` keeps
at least two edges, and let `x ≠ y` keep at most two edges. Then
`2^(m+1) P ≤ (2^m + 2) 2^(r-1-k) + 2^(m+1) 2^B` for the number `P` of paths from `x` to `y` in
what remains, where `k` is at most the number of edges of `C` other than `e` with an end in
`D`. -/
theorem ShortSetting.exit_bound {m G B₁ : ℕ}
    (hshore : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        (2 ^ m + 2) * 2 ^ networkRank K ≤ 2 ^ (m + 1) * K.numPaths s t →
        ∃ S : V → Prop, K.IsCyclicCut S ∧ K.cutSize S ≤ 4 ∧
          ∀ v, S v → K.deg (fun _ => 1) v = 3)
    {N : Network V E} {C : N.Word} {e : E} (H : N.ShortSetting C e)
    (hcut : ∀ S : V → Prop, N.IsCyclicCut S → 5 ≤ N.cutSize S) (hG : 12 * size C ≤ G)
    (D : V → Prop) (hD : ∀ v, D v → 0 < N.deg C v)
    (hdeg : ∀ v, ¬ D v → 2 ≤ (N.sub (N.keep e D)).deg (fun _ => 1) v) {x y : V} (hxy : x ≠ y)
    (hx : (N.sub (N.keep e D)).deg (fun _ => 1) x ≤ 2)
    (hy : (N.sub (N.keep e D)).deg (fun _ => 1) y ≤ 2) (k : ℕ)
    (hk : k ≤ Nat.card {g : E // N.arcEdges C e D g}) :
    2 ^ (m + 1) * N.numPathsIn (N.keep e D) x y ≤
      (2 ^ m + 2) * 2 ^ (networkRank N - 1 - k) + 2 ^ (m + 1) * 2 ^ B₁ := by
  -- the paths lie in the component of `x`
  have hP : N.numPathsIn (N.keep e D) x y ≤
      (N.sub (N.compEdges (N.keep e D) x)).numPaths x y := by
    rw [← N.numPathsIn_eq]
    exact natCard_le_of_imp (fun z hz => ⟨hz.1, hz.1.within_compEdges hz.2⟩)
  by_cases hzero : (N.sub (N.compEdges (N.keep e D) x)).numPaths x y = 0
  · have h0 : N.numPathsIn (N.keep e D) x y = 0 := by omega
    rw [h0, mul_zero]
    exact Nat.zero_le _
  -- a path of the component
  have hpos : 0 < (N.sub (N.compEdges (N.keep e D) x)).numPaths x y := Nat.pos_of_ne_zero hzero
  obtain ⟨⟨z, hz⟩⟩ := Finite.card_pos_iff.1 hpos
  have hdx := hz.deg_left_pos
  have hdy := hz.deg_right_pos
  have hdle : ∀ v, (N.sub (N.compEdges (N.keep e D) x)).deg z v ≤
      (N.sub (N.compEdges (N.keep e D) x)).deg (fun _ => 1) v := by
    intro v
    unfold deg
    apply Finset.card_le_card
    intro k' hk'
    exact Finset.mem_filter.2 ⟨Finset.mem_univ k', one_ne_zero, (Finset.mem_filter.1 hk').2.2⟩
  have hrx : (N.sub (N.keep e D)).graph.Reachable x x := SimpleGraph.Reachable.refl x
  have hry : (N.sub (N.keep e D)).graph.Reachable x y := Classical.not_not.1 fun h => by
    have h1 := N.deg_compEdges_of_not_reachable (N.keep e D) x h
    have h2 := hdle y
    omega
  have hnDx : ¬ D x := by
    intro hDx
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hrx
    have h2 := H.deg_keep_of_mem D hDx
    have h3 := hdle x
    omega
  -- the vertices of the component are not deleted
  have hnD : ∀ v, (N.sub (N.keep e D)).graph.Reachable x v → ¬ D v := by
    intro v hv hDv
    have h1 := N.eq_of_reachable_of_deg_eq_zero (N.keep e D) hv (H.deg_keep_of_mem D hDv)
    rw [← h1] at hDv
    exact hnDx hDv
  have hle3 : ∀ v, (N.sub (N.keep e D)).deg (fun _ => 1) v ≤ 3 := by
    intro v
    have h1 := N.deg_restrict_le (N.keep e D) v
    have h2 := H.cubic v
    omega
  -- the component is a pole
  have hpole : (N.sub (N.compEdges (N.keep e D) x)).IsWeakPole := by
    apply N.isWeakPole_compEdges
    intro v hv
    have h1 := hdeg v (hnD v hv)
    have h2 := hle3 v
    omega
  have hportx : (N.sub (N.compEdges (N.keep e D) x)).IsPort x := by
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hrx
    have h2 := hdeg x hnDx
    unfold IsPort
    omega
  have hporty : (N.sub (N.compEdges (N.keep e D) x)).IsPort y := by
    have h1 := N.deg_compEdges_of_reachable (N.keep e D) x hry
    have h2 := hdeg y (hnD y hry)
    unfold IsPort
    omega
  -- the number of ports
  have hports : Nat.card {v : V // (N.sub (N.compEdges (N.keep e D) x)).IsPort v} ≤ G + 2 := by
    have h1 := N.natCard_ports_compEdges_le H.cubic (N.keep e D) x
    have h2 := H.natCard_not_keep_le D hD
    omega
  -- the rank
  have hrank : networkRank (N.sub (N.compEdges (N.keep e D) x)) + 1 + k ≤ networkRank N := by
    have h1 := N.rank_compEdges_add_le H.conn (N.keep e D) x (by
      intro v _
      by_cases hDv : D v
      · exact Or.inl (H.deg_keep_of_mem D hDv)
      · exact Or.inr (hdeg v hDv))
    have h2 := H.natCard_not_keep_ge D hD
    have h3 : Nat.card {v : V // ¬ (N.sub (N.keep e D)).graph.Reachable x v ∧
        (N.sub (N.keep e D)).deg (fun _ => 1) v = 0} ≤ Nat.card {v : V // D v} := by
      apply natCard_le_of_imp
      intro v hv
      refine Classical.not_not.1 fun hDv => ?_
      have := hdeg v hDv
      omega
    omega
  have hpow : 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤
      2 ^ (networkRank N - 1 - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 2 ^ (m + 1) * N.numPathsIn (N.keep e D) x y ≤
      2 ^ (m + 1) * (N.sub (N.compEdges (N.keep e D) x)).numPaths x y :=
    Nat.mul_le_mul_left _ hP
  by_cases hB : B₁ ≤ networkRank (N.sub (N.compEdges (N.keep e D) x))
  · -- the component has no cubic cyclic shore
    have hlt : 2 ^ (m + 1) * (N.sub (N.compEdges (N.keep e D) x)).numPaths x y <
        (2 ^ m + 2) * 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) := by
      refine Nat.lt_of_not_le fun hmany => ?_
      obtain ⟨S, hS, h4, h3⟩ := hshore V _ (N.sub (N.compEdges (N.keep e D) x)) hpole hports hB
        x y hportx hporty hxy hmany
      exact N.false_of_shore H.cubic hcut (N.compEdges (N.keep e D) x) S hS h4 h3
    have h1 : (2 ^ m + 2) * 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤
        (2 ^ m + 2) * 2 ^ (networkRank N - 1 - k) := Nat.mul_le_mul_left _ hpow
    omega
  · have h1 := (N.sub (N.compEdges (N.keep e D) x)).numPaths_le_two_pow x y
    have h2 : 2 ^ networkRank (N.sub (N.compEdges (N.keep e D) x)) ≤ 2 ^ B₁ :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (m + 1) * (N.sub (N.compEdges (N.keep e D) x)).numPaths x y ≤
        2 ^ (m + 1) * 2 ^ B₁ := Nat.mul_le_mul_left _ (le_trans h1 h2)
    omega

end Erdos1016.BoundaryTrace.Network

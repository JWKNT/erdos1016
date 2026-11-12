import Erdos1016.ExactMaximum.NetSub

set_option autoImplicit false

/-!
# Cycles and paths as minimal words

An even word is an edge word with zero boundary. This file proves the converses of the two
statements of `NetMinimal.lean`:

* a nonzero even word whose even sub-words are zero or the word itself is a cycle
  (`isCycleWord_of_minimal`);
* a word with odd degree exactly at `s` and `t` that has no nonzero even sub-word is a path from
  `s` to `t` (`isPathWord_of_minimal`).

So cycles and paths are described by parities and by the sub-word relation only
(`isCycleWord_iff_minimal`, `isPathWord_iff_minimal`). The later files use this description when
they cut a cycle into the parts on the two sides of a cut.

The proofs use two constructions. The first is the part of a word on the edges with an end in a
set of vertices that is closed under the edges of the word (`deg_restrict_of_closed`). The second
is an even word through two edges at a vertex `v` whose other ends are joined away from `v`
(`exists_even_through`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netCircuitsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### The part of a word on a set of edges -/

/-- The part of the word `x` on the edges that satisfy `p`. -/
def restrict (x : E → Bit) (p : E → Prop) : E → Bit := fun e => if p e then x e else 0

omit [Fintype E] in
theorem restrict_apply_of_pos (x : E → Bit) {p : E → Prop} {e : E} (h : p e) :
    restrict x p e = x e := if_pos h

omit [Fintype E] in
theorem restrict_apply_of_neg (x : E → Bit) {p : E → Prop} {e : E} (h : ¬ p e) :
    restrict x p e = 0 := if_neg h

omit [Fintype E] in
/-- An edge of the part satisfies `p` and is an edge of the word. -/
theorem restrict_ne_zero_iff (x : E → Bit) (p : E → Prop) (e : E) :
    restrict x p e ≠ 0 ↔ p e ∧ x e ≠ 0 := by
  by_cases h : p e
  · rw [restrict_apply_of_pos x h]
    exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
  · rw [restrict_apply_of_neg x h]
    exact ⟨fun hx => absurd rfl hx, fun hx => absurd hx.1 h⟩

omit [Fintype V] [Fintype E] in
/-- The part of a word is a sub-word. -/
theorem restrict_isSubword (N : Network V E) (x : N.Word) (p : E → Prop) :
    N.IsSubword (restrict x p) x := fun e he => ((restrict_ne_zero_iff x p e).1 he).2

/-! ### Degrees -/

omit [Fintype V] in
/-- The zero word has degree zero. -/
theorem deg_zero (N : Network V E) (v : V) : N.deg (0 : N.Word) v = 0 := by
  unfold deg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _ h
  exact h.1 rfl

omit [Fintype V] in
/-- Two words with the same edges at `v` have the same degree at `v`. -/
theorem deg_congr (N : Network V E) {x y : N.Word} {v : V}
    (h : ∀ e, (N.src e = v ∨ N.dst e = v) → (y e ≠ 0 ↔ x e ≠ 0)) : N.deg y v = N.deg x v := by
  unfold deg
  congr 1
  apply Finset.filter_congr
  intro e _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(h e h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(h e h2).2 h1, h2⟩

omit [Fintype V] in
/-- A word without an edge at `v` has degree zero at `v`. -/
theorem deg_eq_zero_of_forall (N : Network V E) {y : N.Word} {v : V}
    (h : ∀ e, (N.src e = v ∨ N.dst e = v) → y e = 0) : N.deg y v = 0 := by
  unfold deg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _ he
  exact he.1 (h e he.2)

/-- A number of parity one that is at most two is one. -/
theorem eq_one_of_cast_eq_one {n : ℕ} (h2 : n ≤ 2) (h : (n : Bit) = 1) : n = 1 := by
  have h3 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h3 with h0 | h0 | h0
  · rw [h0] at h
    exact absurd h (by decide)
  · exact h0
  · rw [h0] at h
    exact absurd h (by decide)

/-- A number of parity zero that is at most two is zero or two. -/
theorem eq_zero_or_two_of_cast_eq_zero {n : ℕ} (h2 : n ≤ 2) (h : (n : Bit) = 0) :
    n = 0 ∨ n = 2 := by
  have h3 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h3 with h0 | h0 | h0
  · exact Or.inl h0
  · rw [h0] at h
    exact absurd h (by decide)
  · exact Or.inr h0

/-! ### Edges and their ends -/

/-- The edge `e` joins the vertices `v` and `w`. -/
def Joins (N : Network V E) (e : E) (v w : V) : Prop :=
  (N.src e = v ∧ N.dst e = w) ∨ (N.src e = w ∧ N.dst e = v)

omit [Fintype V] [Fintype E] in
/-- The two ends of an edge are distinct. -/
theorem Joins.ne {N : Network V E} {e : E} {v w : V} (h : N.Joins e v w) : v ≠ w := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact fun hvw => N.noLoops e (h1.trans (hvw.trans h2.symm))
  · exact fun hvw => N.noLoops e (h1.trans (hvw.symm.trans h2.symm))

omit [Fintype V] [Fintype E] in
theorem Joins.at_left {N : Network V E} {e : E} {v w : V} (h : N.Joins e v w) :
    N.src e = v ∨ N.dst e = v := by
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

omit [Fintype V] [Fintype E] in
theorem Joins.at_right {N : Network V E} {e : E} {v w : V} (h : N.Joins e v w) :
    N.src e = w ∨ N.dst e = w := by
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact Or.inr h2
  · exact Or.inl h1

omit [Fintype V] [Fintype E] in
theorem Joins.symm {N : Network V E} {e : E} {v w : V} (h : N.Joins e v w) : N.Joins e w v := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

omit [Fintype V] [Fintype E] in
/-- An edge at `v` joins `v` and its other end. -/
theorem exists_joins (N : Network V E) {e : E} {v : V} (h : N.src e = v ∨ N.dst e = v) :
    ∃ w, N.Joins e v w := by
  rcases h with h | h
  · exact ⟨N.dst e, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨N.src e, Or.inr ⟨rfl, h⟩⟩

/-- The boundary of a single edge that joins `v` and `w`. -/
theorem boundary_unitWord_of_joins (N : Network V E) {e : E} {v w : V} (h : N.Joins e v w) :
    N.boundary (unitWord e) = unitWord v + unitWord w := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [boundary_unit, h1, h2]
  · rw [boundary_unit, h1, h2, add_comm]

omit [Fintype V] [Fintype E] in
/-- The ends of an edge of `y` are joined by edges of `y`. -/
theorem reachable_iff_of_edge (N : Network V E) {y : N.Word} {e : E} (he : y e ≠ 0) (w : V) :
    (N.selectedGraph y).Reachable w (N.src e) ↔ (N.selectedGraph y).Reachable w (N.dst e) := by
  have hadj : (N.selectedGraph y).Adj (N.src e) (N.dst e) := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩

/-! ### The part of a word in a closed set of vertices -/

omit [Fintype V] in
/-- Let `S` be a set of vertices that contains no vertex of `T`, and suppose that every edge of
`x` without an end in `T` has both ends in `S` or none. Then the part of `x` on the edges with an
end in `S` has the degrees of `x` in `S`, and degree zero at the other vertices outside `T`. -/
theorem deg_restrict_of_closed (N : Network V E) (x : N.Word) (S T : V → Prop)
    (hST : ∀ u, T u → ¬ S u)
    (hclosed : ∀ e, x e ≠ 0 → ¬ T (N.src e) → ¬ T (N.dst e) → (S (N.src e) ↔ S (N.dst e)))
    {u : V} (hu : ¬ T u) :
    N.deg (restrict x fun e => S (N.src e) ∨ S (N.dst e)) u =
      if S u then N.deg x u else 0 := by
  by_cases hS : S u
  · rw [if_pos hS]
    apply N.deg_congr
    intro e he
    rw [restrict_ne_zero_iff]
    constructor
    · exact fun h => h.2
    · intro hx
      refine ⟨?_, hx⟩
      rcases he with he | he
      · exact Or.inl (by rw [he]; exact hS)
      · exact Or.inr (by rw [he]; exact hS)
  · rw [if_neg hS]
    apply N.deg_eq_zero_of_forall
    intro e he
    refine Classical.not_not.1 fun hne => ?_
    obtain ⟨hp, hx⟩ := (restrict_ne_zero_iff x _ e).1 hne
    rcases he with he | he
    · have hsrc : ¬ S (N.src e) := by rw [he]; exact hS
      have hdst : S (N.dst e) := by
        rcases hp with hp | hp
        · exact absurd hp hsrc
        · exact hp
      have hT1 : ¬ T (N.src e) := by rw [he]; exact hu
      have hT2 : ¬ T (N.dst e) := fun hT => hST _ hT hdst
      exact hsrc ((hclosed e hx hT1 hT2).2 hdst)
    · have hdst : ¬ S (N.dst e) := by rw [he]; exact hS
      have hsrc : S (N.src e) := by
        rcases hp with hp | hp
        · exact hp
        · exact absurd hp hdst
      have hT2 : ¬ T (N.dst e) := by rw [he]; exact hu
      have hT1 : ¬ T (N.src e) := fun hT => hST _ hT hsrc
      exact hdst ((hclosed e hx hT1 hT2).1 hsrc)

/-- The boundary form of `deg_restrict_of_closed`. -/
theorem boundary_restrict_of_closed (N : Network V E) (x : N.Word) (S T : V → Prop)
    (hST : ∀ u, T u → ¬ S u)
    (hclosed : ∀ e, x e ≠ 0 → ¬ T (N.src e) → ¬ T (N.dst e) → (S (N.src e) ↔ S (N.dst e)))
    {u : V} (hu : ¬ T u) :
    N.boundary (restrict x fun e => S (N.src e) ∨ S (N.dst e)) u =
      if S u then N.boundary x u else 0 := by
  rw [boundary_eq_deg, N.deg_restrict_of_closed x S T hST hclosed hu]
  by_cases hS : S u
  · rw [if_pos hS, if_pos hS, boundary_eq_deg]
  · rw [if_neg hS, if_neg hS]
    exact Nat.cast_zero

/-! ### A word without its edges at a vertex -/

/-- The word `x` without its edges at the vertex `v`. -/
def removeVertex (N : Network V E) (x : N.Word) (v : V) : N.Word :=
  restrict x fun e => N.src e ≠ v ∧ N.dst e ≠ v

omit [Fintype V] [Fintype E] in
/-- An edge of `removeVertex x v` is an edge of `x` and is not at `v`. -/
theorem removeVertex_ne_zero_iff (N : Network V E) (x : N.Word) (v : V) (e : E) :
    N.removeVertex x v e ≠ 0 ↔ (N.src e ≠ v ∧ N.dst e ≠ v) ∧ x e ≠ 0 :=
  restrict_ne_zero_iff x _ e

omit [Fintype V] [Fintype E] in
/-- Without the edges at `v`, the vertex `v` is joined to no other vertex. -/
theorem eq_of_reachable_removeVertex (N : Network V E) (x : N.Word) {v w : V}
    (h : (N.selectedGraph (N.removeVertex x v)).Reachable v w) : v = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    obtain ⟨e, he, hends⟩ := hadj
    have h1 := ((N.removeVertex_ne_zero_iff x v e).1 he).1
    rcases hends with ⟨h2, _⟩ | ⟨_, h2⟩
    · exact h1.1 h2
    · exact h1.2 h2

/-- Let `e₁` and `e₂` be two edges of `x` at `v` whose other ends are joined by edges of `x` that
are not at `v`. Then `e₁` lies in an even sub-word of `x` that has no edge at `v` other than `e₁`
and `e₂`. -/
theorem exists_even_through (N : Network V E) (x : N.Word) {v w₁ w₂ : V} {e₁ e₂ : E}
    (hne : e₁ ≠ e₂) (hx₁ : x e₁ ≠ 0) (hx₂ : x e₂ ≠ 0) (h₁ : N.Joins e₁ v w₁)
    (h₂ : N.Joins e₂ v w₂)
    (hr : (N.selectedGraph (N.removeVertex x v)).Reachable w₁ w₂) :
    ∃ c : N.Word, N.IsSubword c x ∧ N.boundary c = 0 ∧ c e₁ ≠ 0 ∧
      ∀ f, (N.src f = v ∨ N.dst f = v) → f ≠ e₁ → f ≠ e₂ → c f = 0 := by
  obtain ⟨j, hj, hbj⟩ := N.exists_join_of_reachable (N.removeVertex x v) hr
  -- `j` has no edge at `v`
  have hjv : ∀ f, (N.src f = v ∨ N.dst f = v) → j f = 0 := by
    intro f hf
    refine Classical.not_not.1 fun hjf => ?_
    have h1 := ((N.removeVertex_ne_zero_iff x v f).1 (hj f hjf)).1
    rcases hf with hf | hf
    · exact h1.1 hf
    · exact h1.2 hf
  refine ⟨j + unitWord e₁ + unitWord e₂, ?_, ?_, ?_, ?_⟩
  · intro f hf
    by_cases hf1 : f = e₁
    · rw [hf1]
      exact hx₁
    · by_cases hf2 : f = e₂
      · rw [hf2]
        exact hx₂
      · have hjf : j f ≠ 0 := by
          intro h0
          apply hf
          show j f + unitWord e₁ f + unitWord e₂ f = 0
          rw [h0, unitWord_apply, unitWord_apply, if_neg (Ne.symm hf1), if_neg (Ne.symm hf2)]
          simp
        exact ((N.removeVertex_ne_zero_iff x v f).1 (hj f hjf)).2
  · rw [map_add, map_add, hbj, N.boundary_unitWord_of_joins h₁,
      N.boundary_unitWord_of_joins h₂]
    have h3 : ∀ a b c : V → Bit, (a + b) + (c + a) + (c + b) = 0 := by
      intro a b c
      have h : (a + b) + (c + a) + (c + b) = (a + a) + (b + b) + (c + c) := by abel
      rw [h, word_add_self a, word_add_self b, word_add_self c, add_zero, add_zero]
    exact h3 _ _ _
  · show j e₁ + unitWord e₁ e₁ + unitWord e₂ e₁ ≠ 0
    rw [hjv e₁ h₁.at_left, unitWord_apply, unitWord_apply, if_pos rfl, if_neg (Ne.symm hne)]
    simp
  · intro f hf hf1 hf2
    show j f + unitWord e₁ f + unitWord e₂ f = 0
    rw [hjv f hf, unitWord_apply, unitWord_apply, if_neg (Ne.symm hf1), if_neg (Ne.symm hf2)]
    simp

/-! ### A minimal even word is a cycle -/

/-- **A minimal even word is a cycle.** Let `x` be a nonzero even word such that every even
sub-word of `x` is zero or `x`. Then `x` is a cycle. -/
theorem isCycleWord_of_minimal (N : Network V E) {x : N.Word} (hne : x ≠ 0)
    (hx : N.boundary x = 0)
    (hmin : ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y = 0 ∨ y = x) :
    N.IsCycleWord x := by
  -- every degree is at most two
  have hdeg : ∀ v, N.deg x v ≤ 2 := by
    intro v
    refine Nat.le_of_not_lt fun h3 => ?_
    have h3' : 2 < (Finset.univ.filter fun e : E =>
        x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)).card := h3
    obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h12, h13, h23⟩ := Finset.two_lt_card.1 h3'
    have he₁ := (Finset.mem_filter.1 he₁).2
    have he₂ := (Finset.mem_filter.1 he₂).2
    have he₃ := (Finset.mem_filter.1 he₃).2
    obtain ⟨w₁, hw₁⟩ := N.exists_joins he₁.2
    obtain ⟨w₂, hw₂⟩ := N.exists_joins he₂.2
    -- `S` is the set of the vertices that are joined to `w₁` by edges of `x` that are not at `v`
    obtain ⟨S, hS⟩ : ∃ S : V → Prop,
        ∀ u, S u ↔ (N.selectedGraph (N.removeVertex x v)).Reachable w₁ u :=
      ⟨_, fun _ => Iff.rfl⟩
    have hSv : ∀ u, u = v → ¬ S u := by
      intro u hu hSu
      rw [hu, hS] at hSu
      exact hw₁.ne (N.eq_of_reachable_removeVertex x hSu.symm)
    have hclosed : ∀ e, x e ≠ 0 → ¬ N.src e = v → ¬ N.dst e = v →
        (S (N.src e) ↔ S (N.dst e)) := by
      intro e he hs hd
      rw [hS, hS]
      exact N.reachable_iff_of_edge ((N.removeVertex_ne_zero_iff x v e).2 ⟨⟨hs, hd⟩, he⟩) w₁
    obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict x fun e => S (N.src e) ∨ S (N.dst e) :=
      ⟨_, rfl⟩
    have hysub : N.IsSubword y x := by
      rw [hy]
      exact N.restrict_isSubword x _
    have hy0 : N.boundary y = 0 := by
      apply eq_zero_of_total_zero_of_off_eq_zero v (N.boundary y) (N.total_boundary y)
      intro u hu
      rw [hy, N.boundary_restrict_of_closed x S (fun u => u = v) hSv hclosed hu, hx]
      simp
    have hye₁ : y e₁ ≠ 0 := by
      rw [hy]
      apply (restrict_ne_zero_iff x _ e₁).2
      refine ⟨?_, he₁.1⟩
      have hSw : S w₁ := (hS w₁).2 (SimpleGraph.Reachable.refl _)
      rcases hw₁.at_right with h | h
      · exact Or.inl (by rw [h]; exact hSw)
      · exact Or.inr (by rw [h]; exact hSw)
    have hyx : y = x := by
      rcases hmin y hysub hy0 with h | h
      · exact absurd (congrFun h e₁) hye₁
      · exact h
    -- so the other end of `e₂` is joined to `w₁`
    have hS₂ : S w₂ := by
      have h2 : y e₂ ≠ 0 := by
        rw [hyx]
        exact he₂.1
      rw [hy] at h2
      have hp := ((restrict_ne_zero_iff x _ e₂).1 h2).1
      rcases hw₂ with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · rcases hp with hp | hp
        · exact absurd hp (hSv _ h1)
        · rw [h2'] at hp
          exact hp
      · rcases hp with hp | hp
        · rw [h1] at hp
          exact hp
        · exact absurd hp (hSv _ h2')
    obtain ⟨c, hcsub, hc0, hce₁, hcv⟩ :=
      N.exists_even_through x h12 he₁.1 he₂.1 hw₁ hw₂ ((hS w₂).1 hS₂)
    rcases hmin c hcsub hc0 with h | h
    · exact hce₁ (congrFun h e₁)
    · have h0 := hcv e₃ he₃.2 (Ne.symm h13) (Ne.symm h23)
      rw [h] at h0
      exact he₃.1 h0
  refine ⟨hne, fun v => N.deg_eq_zero_or_two_of_even hx (hdeg v), ?_⟩
  -- any two vertices of `x` are joined by edges of `x`
  intro u v hu hv
  obtain ⟨S, hS⟩ : ∃ S : V → Prop, ∀ w, S w ↔ (N.selectedGraph x).Reachable u w :=
    ⟨_, fun _ => Iff.rfl⟩
  have hclosed : ∀ e, x e ≠ 0 → ¬ False → ¬ False → (S (N.src e) ↔ S (N.dst e)) := by
    intro e he _ _
    rw [hS, hS]
    exact N.reachable_iff_of_edge he u
  obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict x fun e => S (N.src e) ∨ S (N.dst e) :=
    ⟨_, rfl⟩
  have hdegy : ∀ w, N.deg y w = if S w then N.deg x w else 0 := by
    intro w
    rw [hy]
    exact N.deg_restrict_of_closed x S (fun _ => False) (fun _ h => h.elim) hclosed (fun h => h)
  have hy0 : N.boundary y = 0 := by
    funext w
    rw [hy, N.boundary_restrict_of_closed x S (fun _ => False) (fun _ h => h.elim) hclosed
      (fun h => h), hx]
    simp
  have hyu : N.deg y u = N.deg x u := by
    rw [hdegy u, if_pos ((hS u).2 (SimpleGraph.Reachable.refl u))]
  have hyx : y = x := by
    rcases hmin y (by rw [hy]; exact N.restrict_isSubword x _) hy0 with h | h
    · rw [h, N.deg_zero] at hyu
      omega
    · exact h
  refine Classical.not_not.1 fun hno => ?_
  have h1 := hdegy v
  rw [if_neg (fun hSv => hno ((hS v).1 hSv)), hyx] at h1
  omega

/-- A word is a cycle if and only if it is a minimal nonzero even word. -/
theorem isCycleWord_iff_minimal (N : Network V E) (x : N.Word) :
    N.IsCycleWord x ↔ x ≠ 0 ∧ N.boundary x = 0 ∧
      ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y = 0 ∨ y = x := by
  constructor
  · intro h
    refine ⟨h.1, h.boundary_eq_zero, fun y hsub hy => ?_⟩
    rcases Classical.em (y = 0) with hy0 | hy0
    · exact Or.inl hy0
    · exact Or.inr (h.eq_of_even_subword hsub hy hy0)
  · rintro ⟨h1, h2, h3⟩
    exact N.isCycleWord_of_minimal h1 h2 h3

/-! ### A join without an even sub-word is a path -/

/-- **A join without an even sub-word is a path.** Let `s ≠ t`, and let `x` be a word with odd
degree exactly at `s` and `t` whose even sub-words are all zero. Then `x` is a path from `s` to
`t`. -/
theorem isPathWord_of_minimal (N : Network V E) {s t : V} {x : N.Word} (hst : s ≠ t)
    (hx : N.boundary x = N.pathDemand s t)
    (hmin : ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y = 0) :
    N.IsPathWord s t x := by
  have hdem : ∀ u, u ≠ s → u ≠ t → N.pathDemand s t u = 0 := by
    intro u hs ht
    simp [pathDemand, hs, ht]
  -- every degree is at most two
  have hdeg : ∀ v, N.deg x v ≤ 2 := by
    intro v
    refine Nat.le_of_not_lt fun h3 => ?_
    have h3' : 2 < (Finset.univ.filter fun e : E =>
        x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)).card := h3
    obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h12, h13, h23⟩ := Finset.two_lt_card.1 h3'
    have he₁ := (Finset.mem_filter.1 he₁).2
    have he₂ := (Finset.mem_filter.1 he₂).2
    have he₃ := (Finset.mem_filter.1 he₃).2
    obtain ⟨w₁, hw₁⟩ := N.exists_joins he₁.2
    obtain ⟨w₂, hw₂⟩ := N.exists_joins he₂.2
    obtain ⟨w₃, hw₃⟩ := N.exists_joins he₃.2
    -- the other ends of two edges at `v` are not joined by edges that are not at `v`
    have hsep : ∀ (a b : E) (wa wb : V), a ≠ b → x a ≠ 0 → x b ≠ 0 → N.Joins a v wa →
        N.Joins b v wb → ¬ (N.selectedGraph (N.removeVertex x v)).Reachable wa wb := by
      intro a b wa wb hab ha hb hja hjb hr
      obtain ⟨c, hcsub, hc0, hca, _⟩ := N.exists_even_through x hab ha hb hja hjb hr
      exact hca (congrFun (hmin c hcsub hc0) a)
    -- the other end of an edge at `v` is joined to `s` or to `t` by edges that are not at `v`
    have hreach : ∀ (a : E) (wa : V), x a ≠ 0 → N.Joins a v wa →
        (N.selectedGraph (N.removeVertex x v)).Reachable wa s ∨
        (N.selectedGraph (N.removeVertex x v)).Reachable wa t := by
      intro a wa ha hja
      refine Classical.not_not.1 fun hno => ?_
      have hns : ¬ (N.selectedGraph (N.removeVertex x v)).Reachable wa s :=
        fun h => hno (Or.inl h)
      have hnt : ¬ (N.selectedGraph (N.removeVertex x v)).Reachable wa t :=
        fun h => hno (Or.inr h)
      obtain ⟨S, hS⟩ : ∃ S : V → Prop,
          ∀ u, S u ↔ (N.selectedGraph (N.removeVertex x v)).Reachable wa u :=
        ⟨_, fun _ => Iff.rfl⟩
      have hSv : ∀ u, u = v → ¬ S u := by
        intro u hu hSu
        rw [hu, hS] at hSu
        exact hja.ne (N.eq_of_reachable_removeVertex x hSu.symm)
      have hclosed : ∀ e, x e ≠ 0 → ¬ N.src e = v → ¬ N.dst e = v →
          (S (N.src e) ↔ S (N.dst e)) := by
        intro e he hs hd
        rw [hS, hS]
        exact N.reachable_iff_of_edge ((N.removeVertex_ne_zero_iff x v e).2 ⟨⟨hs, hd⟩, he⟩) wa
      obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict x fun e => S (N.src e) ∨ S (N.dst e) :=
        ⟨_, rfl⟩
      have hy0 : N.boundary y = 0 := by
        apply eq_zero_of_total_zero_of_off_eq_zero v (N.boundary y) (N.total_boundary y)
        intro u hu
        rw [hy, N.boundary_restrict_of_closed x S (fun u => u = v) hSv hclosed hu]
        by_cases hSu : S u
        · rw [if_pos hSu, hx]
          apply hdem
          · intro hus
            rw [hus, hS] at hSu
            exact hns hSu
          · intro hut
            rw [hut, hS] at hSu
            exact hnt hSu
        · rw [if_neg hSu]
      have hya : y a ≠ 0 := by
        rw [hy]
        apply (restrict_ne_zero_iff x _ a).2
        refine ⟨?_, ha⟩
        have hSw : S wa := (hS wa).2 (SimpleGraph.Reachable.refl _)
        rcases hja.at_right with h | h
        · exact Or.inl (by rw [h]; exact hSw)
        · exact Or.inr (by rw [h]; exact hSw)
      exact hya (congrFun (hmin y (by rw [hy]; exact N.restrict_isSubword x _) hy0) a)
    -- three edges at `v`, and only two vertices `s` and `t`
    have r1 := hreach e₁ w₁ he₁.1 hw₁
    have r2 := hreach e₂ w₂ he₂.1 hw₂
    have r3 := hreach e₃ w₃ he₃.1 hw₃
    rcases r1 with r1 | r1 <;> rcases r2 with r2 | r2 <;> rcases r3 with r3 | r3
    · exact hsep e₁ e₂ w₁ w₂ h12 he₁.1 he₂.1 hw₁ hw₂ (r1.trans r2.symm)
    · exact hsep e₁ e₂ w₁ w₂ h12 he₁.1 he₂.1 hw₁ hw₂ (r1.trans r2.symm)
    · exact hsep e₁ e₃ w₁ w₃ h13 he₁.1 he₃.1 hw₁ hw₃ (r1.trans r3.symm)
    · exact hsep e₂ e₃ w₂ w₃ h23 he₂.1 he₃.1 hw₂ hw₃ (r2.trans r3.symm)
    · exact hsep e₂ e₃ w₂ w₃ h23 he₂.1 he₃.1 hw₂ hw₃ (r2.trans r3.symm)
    · exact hsep e₁ e₃ w₁ w₃ h13 he₁.1 he₃.1 hw₁ hw₃ (r1.trans r3.symm)
    · exact hsep e₁ e₂ w₁ w₂ h12 he₁.1 he₂.1 hw₁ hw₂ (r1.trans r2.symm)
    · exact hsep e₁ e₂ w₁ w₂ h12 he₁.1 he₂.1 hw₁ hw₂ (r1.trans r2.symm)
  -- the parities of the degrees
  have hpar : ∀ v, ((N.deg x v : ℕ) : Bit) = N.pathDemand s t v := by
    intro v
    rw [← boundary_eq_deg, hx]
  have hs1 : N.deg x s = 1 := by
    apply eq_one_of_cast_eq_one (hdeg s)
    rw [hpar s]
    simp [pathDemand, hst]
  have ht1 : N.deg x t = 1 := by
    apply eq_one_of_cast_eq_one (hdeg t)
    rw [hpar t]
    simp [pathDemand, hst.symm]
  have hother : ∀ v, v ≠ s → v ≠ t → N.deg x v = 0 ∨ N.deg x v = 2 := by
    intro v hvs hvt
    apply eq_zero_or_two_of_cast_eq_zero (hdeg v)
    rw [hpar v]
    exact hdem v hvs hvt
  refine ⟨hst, hs1, ht1, hother, ?_⟩
  -- every vertex of `x` is joined to `s` by edges of `x`
  intro v hv
  obtain ⟨S, hS⟩ : ∃ S : V → Prop, ∀ w, S w ↔ ¬ (N.selectedGraph x).Reachable s w :=
    ⟨_, fun _ => Iff.rfl⟩
  have hclosed : ∀ e, x e ≠ 0 → ¬ False → ¬ False → (S (N.src e) ↔ S (N.dst e)) := by
    intro e he _ _
    rw [hS, hS]
    exact not_congr (N.reachable_iff_of_edge he s)
  obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict x fun e => S (N.src e) ∨ S (N.dst e) :=
    ⟨_, rfl⟩
  have hdegy : ∀ w, N.deg y w = if S w then N.deg x w else 0 := by
    intro w
    rw [hy]
    exact N.deg_restrict_of_closed x S (fun _ => False) (fun _ h => h.elim) hclosed (fun h => h)
  have hy0 : N.boundary y = 0 := by
    apply eq_zero_of_total_zero_of_off_eq_zero t (N.boundary y) (N.total_boundary y)
    intro u hu
    rw [hy, N.boundary_restrict_of_closed x S (fun _ => False) (fun _ h => h.elim) hclosed
      (fun h => h)]
    by_cases hSu : S u
    · rw [if_pos hSu, hx]
      apply hdem u _ hu
      intro hus
      rw [hus, hS] at hSu
      exact hSu (SimpleGraph.Reachable.refl s)
    · rw [if_neg hSu]
  have hyz : y = 0 := hmin y (by rw [hy]; exact N.restrict_isSubword x _) hy0
  refine Classical.not_not.1 fun hno => ?_
  have h1 := hdegy v
  rw [if_pos ((hS v).2 hno), hyz, N.deg_zero] at h1
  omega

/-- A word is a path from `s` to `t` if and only if `s ≠ t`, the word has odd degree exactly at
`s` and `t`, and it has no nonzero even sub-word. -/
theorem isPathWord_iff_minimal (N : Network V E) (s t : V) (x : N.Word) :
    N.IsPathWord s t x ↔ s ≠ t ∧ N.boundary x = N.pathDemand s t ∧
      ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y = 0 := by
  constructor
  · intro h
    exact ⟨h.1, h.boundary_eq, fun y hsub hy => h.eq_zero_of_even_subword hsub hy⟩
  · rintro ⟨h1, h2, h3⟩
    exact N.isPathWord_of_minimal h1 h2 h3

end Erdos1016.BoundaryTrace.Network

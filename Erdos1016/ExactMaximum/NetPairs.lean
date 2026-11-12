import Erdos1016.ExactMaximum.NetGlue

set_option autoImplicit false

/-!
# Pairs of disjoint paths

A pair of vertex-disjoint paths from `a` to `b` and from `c` to `d` is determined by its sum, and
the sum determines which of the three pairings of `a, b, c, d` the pair realises. This file proves

* `IsPathPair.minimal`: the sum of a path pair has no nonzero even sub-word;
* `exists_pathPair_of_minimal`: a word with odd degree exactly at four vertices, with all degrees
  at most two and without a nonzero even sub-word, is the sum of a path pair for one of the three
  pairings;
* `IsPathPair.eq_of_add_eq` and `IsPathPair.false_of_add_eq`: the path pair and the pairing are
  unique;
* `IsCycleWord.parts_of_crossSet_four`: the parts of a cycle through exactly four crossing edges
  of a cut satisfy the hypotheses of `exists_pathPair_of_minimal`;
* `IsCycleWord.eq_glue_of_subword`: a cycle that contains two crossing edges and a path in each
  side between their ends has no other edge. So the pairings of a cycle through four crossing
  edges in the two sides are different.

These are the steps of Lemma 6.4 of the paper "The maximum number of cycles in a graph of large
rank" that concern a single cycle.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netPairsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Sub-words and the selected graph -/

omit [Fintype V] [Fintype E] in
/-- The graph of a sub-word is a subgraph. -/
theorem IsSubword.selectedGraph_le {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) :
    N.selectedGraph y ≤ N.selectedGraph x := by
  intro u w hadj
  obtain ⟨e, he, hends⟩ := hadj
  exact ⟨e, h e he, hends⟩

omit [Fintype V] [Fintype E] in
/-- A sum of sub-words is a sub-word. -/
theorem IsSubword.add {N : Network V E} {y z x : N.Word} (hy : N.IsSubword y x)
    (hz : N.IsSubword z x) : N.IsSubword (y + z) x :=
  Within.add (p := fun g => x g ≠ 0) hy hz

omit [Fintype V] in
/-- A single edge of `x` is a sub-word of `x`. -/
theorem isSubword_unitWord (N : Network V E) {x : N.Word} {e : E} (h : x e ≠ 0) :
    N.IsSubword (unitWord e) x :=
  within_unitWord (p := fun g => x g ≠ 0) h

omit [Fintype V] [Fintype E] in
/-- If `y` is a sub-word of `x`, then `x + y` is a sub-word of `x`. -/
theorem IsSubword.add_self {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) :
    N.IsSubword (x + y) x := by
  intro g hg
  refine fun hx => hg ?_
  have hy : y g = 0 := Classical.not_not.1 fun hne => h g hne hx
  show x g + y g = 0
  rw [hx, hy, add_zero]

/-! ### The sum of a path pair -/

section PathPair

variable {N : Network V E} {a b c d : V} {A B : N.Word}

omit [Fintype V] in
/-- An edge of the sum of a path pair is an edge of one of the two paths. -/
theorem IsPathPair.edge_cases (_h : N.IsPathPair a b c d A B) {g : E} (hg : (A + B) g ≠ 0) :
    A g ≠ 0 ∨ B g ≠ 0 := by
  refine Classical.not_not.1 fun hno => hg ?_
  have h1 : A g = 0 := Classical.not_not.1 fun h => hno (Or.inl h)
  have h2 : B g = 0 := Classical.not_not.1 fun h => hno (Or.inr h)
  show A g + B g = 0
  rw [h1, h2, add_zero]

omit [Fintype V] in
theorem IsPathPair.isSubword_left (h : N.IsPathPair a b c d A B) : N.IsSubword A (A + B) := by
  intro g hg
  have h0 : B g = 0 := h.2.2.support g hg
  show A g + B g ≠ 0
  rw [h0, add_zero]
  exact hg

omit [Fintype V] in
theorem IsPathPair.isSubword_right (h : N.IsPathPair a b c d A B) : N.IsSubword B (A + B) := by
  intro g hg
  have h0 : A g = 0 := Classical.not_not.1 fun hA => hg (h.2.2.support g hA)
  show A g + B g ≠ 0
  rw [h0, zero_add]
  exact hg

/-- The boundary of the sum of a path pair. -/
theorem IsPathPair.boundary_add (h : N.IsPathPair a b c d A B) :
    N.boundary (A + B) = N.pathDemand a b + N.pathDemand c d := by
  rw [map_add, h.1.boundary_eq, h.2.1.boundary_eq]

omit [Fintype V] in
/-- The degrees of the sum of a path pair are at most two. -/
theorem IsPathPair.deg_add_le (h : N.IsPathPair a b c d A B) (v : V) :
    N.deg (A + B) v ≤ 2 := by
  rw [N.deg_add_of_disjoint h.2.2.support v]
  have hA : N.deg A v ≤ 2 := by
    by_cases h1 : v = a
    · rw [h1, h.1.2.1]
      omega
    · by_cases h2 : v = b
      · rw [h2, h.1.2.2.1]
        omega
      · rcases h.1.2.2.2.1 v h1 h2 with h0 | h0 <;> omega
  have hB : N.deg B v ≤ 2 := by
    by_cases h1 : v = c
    · rw [h1, h.2.1.2.1]
      omega
    · by_cases h2 : v = d
      · rw [h2, h.2.1.2.2.1]
        omega
      · rcases h.2.1.2.2.2.1 v h1 h2 with h0 | h0 <;> omega
  rcases h.2.2 v with h0 | h0 <;> omega

/-- **The sum of a path pair has no nonzero even sub-word.** -/
theorem IsPathPair.minimal (h : N.IsPathPair a b c d A B) :
    ∀ z : N.Word, N.IsSubword z (A + B) → N.boundary z = 0 → z = 0 := by
  intro z hz hz0
  apply N.eq_zero_of_even_of_sides (N.verts A) h.1.minimal h.2.1.minimal hz0
  · intro g hg hc
    rcases h.edge_cases (hz g hg) with hA | hB
    · exact N.not_crosses_of_inside (N.within_inside_verts A g hA) hc
    · exact N.not_crosses_of_outside (h.2.2.within_outside_verts g hB) hc
  · intro g hg hin
    rcases h.edge_cases (hz g hg) with hA | hB
    · exact hA
    · exact absurd hin (N.not_inside_of_outside (h.2.2.within_outside_verts g hB))
  · intro g hg hout
    rcases h.edge_cases (hz g hg) with hA | hB
    · exact absurd hout (N.not_outside_of_inside (N.within_inside_verts A g hA))
    · exact hB

omit [Fintype V] in
/-- The ends of the first path of a path pair are joined in the sum. -/
theorem IsPathPair.reachable (h : N.IsPathPair a b c d A B) :
    (N.selectedGraph (A + B)).Reachable a b := by
  have h1 : (N.selectedGraph A).Reachable a b :=
    h.1.2.2.2.2 b (by rw [h.1.2.2.1]; exact Nat.one_pos)
  exact h1.mono h.isSubword_left.selectedGraph_le

omit [Fintype V] in
/-- In the sum of a path pair, no vertex of the second path is joined to the start of the
first path. -/
theorem IsPathPair.not_reachable (h : N.IsPathPair a b c d A B) {v : V} (hv : 0 < N.deg B v) :
    ¬ (N.selectedGraph (A + B)).Reachable a v := by
  intro hr
  have hwalk : ∀ u w, (N.selectedGraph (A + B)).Walk u w → 0 < N.deg A u → 0 < N.deg A w := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons x y z hadj _ ih =>
      intro hx
      apply ih
      obtain ⟨g, hg, hends⟩ := hadj
      have hgA : A g ≠ 0 := by
        rcases h.edge_cases hg with hA | hB
        · exact hA
        · exfalso
          have hBx : 0 < N.deg B x := by
            rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact h1 ▸ N.deg_src_pos hB
            · exact h2 ▸ N.deg_dst_pos hB
          rcases h.2.2 x with h0 | h0 <;> omega
      rcases hends with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2 ▸ N.deg_dst_pos hgA
      · exact h1 ▸ N.deg_src_pos hgA
  obtain ⟨p⟩ := hr
  have h1 := hwalk a v p (by rw [h.1.2.1]; exact Nat.one_pos)
  rcases h.2.2 v with h0 | h0 <;> omega

/-- **A path pair is determined by its sum.** -/
theorem IsPathPair.eq_of_add_eq {A' B' : N.Word} (h : N.IsPathPair a b c d A B)
    (h' : N.IsPathPair a b c d A' B') (heq : A + B = A' + B') : A = A' ∧ B = B' := by
  have hsubA' : N.IsSubword A' (A + B) := by
    rw [heq]
    exact h'.isSubword_left
  have hz : A + A' = 0 := by
    apply h.minimal (A + A') (h.isSubword_left.add hsubA')
    rw [map_add, h.1.boundary_eq, h'.1.boundary_eq]
    exact word_add_self _
  have hAA : A = A' := word_eq_of_add_eq_zero hz
  refine ⟨hAA, ?_⟩
  rw [hAA] at heq
  exact add_left_cancel heq

omit [Fintype V] in
/-- **The pairing is determined by the sum.** If the partner `b'` of `a` in a second path pair
with the same sum is a vertex of the second path of the first pair, there is a contradiction. -/
theorem IsPathPair.false_of_add_eq {b' c' d' : V} {A' B' : N.Word}
    (h : N.IsPathPair a b c d A B) (h' : N.IsPathPair a b' c' d' A' B')
    (heq : A + B = A' + B') (hb' : 0 < N.deg B b') : False := by
  apply h.not_reachable hb'
  rw [heq]
  exact h'.reachable

omit [Fintype V] in
/-- The two paths of a path pair can be taken in either direction. -/
theorem IsPathPair.swap_right (h : N.IsPathPair a b c d A B) : N.IsPathPair a b d c A B :=
  ⟨h.1, h.2.1.symm, h.2.2⟩

end PathPair

/-! ### A word with four odd vertices -/

/-- Let `W` have odd degree exactly at `a, b, c, d`, all degrees at most two, and no nonzero
even sub-word. If `a` and `b` are joined by edges of `W`, then `W` is the sum of a path from `a`
to `b` and a disjoint path from `c` to `d`. -/
theorem exists_pathPair_of_reachable (N : Network V E) {a b c d : V} (hab : a ≠ b)
    (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) {W : N.Word}
    (hb : N.boundary W = N.pathDemand a b + N.pathDemand c d) (hdeg : ∀ v, N.deg W v ≤ 2)
    (hmin : ∀ z : N.Word, N.IsSubword z W → N.boundary z = 0 → z = 0)
    (hr : (N.selectedGraph W).Reachable a b) :
    ∃ A B : N.Word, N.IsPathPair a b c d A B ∧ W = A + B := by
  obtain ⟨j, hj, hbj⟩ := N.exists_join_of_reachable W hr
  have hBsub : N.IsSubword (W + j) W := IsSubword.add_self hj
  have hbB : N.boundary (W + j) = N.pathDemand c d := by
    rw [map_add, hb, hbj]
    show unitWord a + unitWord b + N.pathDemand c d + (unitWord a + unitWord b) =
      N.pathDemand c d
    have h3 : ∀ p q : V → Bit, p + q + p = q := by
      intro p q
      have h : p + q + p = q + (p + p) := by abel
      rw [h, word_add_self, add_zero]
    exact h3 _ _
  have hA : N.IsPathWord a b j :=
    N.isPathWord_of_minimal hab hbj (fun z hz hz0 => hmin z (fun g hg => hj g (hz g hg)) hz0)
  have hB : N.IsPathWord c d (W + j) :=
    N.isPathWord_of_minimal hcd hbB
      (fun z hz hz0 => hmin z (fun g hg => hBsub g (hz g hg)) hz0)
  have hsupp : ∀ g, j g ≠ 0 → (W + j) g = 0 := by
    intro g hg
    have hW : W g ≠ 0 := hj g hg
    show W g + j g = 0
    rw [bit_eq_one_of_ne_zero hW, bit_eq_one_of_ne_zero hg]
    exact bit_add_self 1
  have hsum : W = j + (W + j) := by
    have h : j + (W + j) = W + (j + j) := by abel
    rw [h, word_add_self, add_zero]
  have hdisj : N.VertexDisjoint j (W + j) := by
    intro v
    have hd := N.deg_add_of_disjoint hsupp v
    rw [← hsum] at hd
    have h2 := hdeg v
    refine Classical.not_not.1 fun hno => ?_
    have hA1 : 0 < N.deg j v := Nat.pos_of_ne_zero fun h => hno (Or.inl h)
    have hB1 : 0 < N.deg (W + j) v := Nat.pos_of_ne_zero fun h => hno (Or.inr h)
    have hva : v = a ∨ v = b := by
      refine Classical.not_not.1 fun hno' => ?_
      rcases hA.2.2.2.1 v (fun h => hno' (Or.inl h)) (fun h => hno' (Or.inr h)) with h | h <;>
        omega
    have hvc : v = c ∨ v = d := by
      refine Classical.not_not.1 fun hno' => ?_
      rcases hB.2.2.2.1 v (fun h => hno' (Or.inl h)) (fun h => hno' (Or.inr h)) with h | h <;>
        omega
    rcases hva with h | h <;> rcases hvc with h' | h'
    · exact hac (h.symm.trans h')
    · exact had (h.symm.trans h')
    · exact hbc (h.symm.trans h')
    · exact hbd (h.symm.trans h')
  exact ⟨j, W + j, ⟨hA, hB, hdisj⟩, hsum⟩

/-- **A word with four odd vertices is a path pair.** Let `W` have odd degree exactly at the
distinct vertices `a, b, c, d`, all degrees at most two, and no nonzero even sub-word. Then `W`
is the sum of two disjoint paths that join the four vertices in pairs, in one of the three
possible ways. -/
theorem exists_pathPair_of_minimal (N : Network V E) {a b c d : V} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {W : N.Word}
    (hb : N.boundary W = N.pathDemand a b + N.pathDemand c d) (hdeg : ∀ v, N.deg W v ≤ 2)
    (hmin : ∀ z : N.Word, N.IsSubword z W → N.boundary z = 0 → z = 0) :
    (∃ A B : N.Word, N.IsPathPair a b c d A B ∧ W = A + B) ∨
    (∃ A B : N.Word, N.IsPathPair a c b d A B ∧ W = A + B) ∨
    (∃ A B : N.Word, N.IsPathPair a d b c A B ∧ W = A + B) := by
  -- `a` is joined to `b`, `c` or `d` by edges of `W`
  have hreach : (N.selectedGraph W).Reachable a b ∨ (N.selectedGraph W).Reachable a c ∨
      (N.selectedGraph W).Reachable a d := by
    refine Classical.not_not.1 fun hno => ?_
    have hnb : ¬ (N.selectedGraph W).Reachable a b := fun h => hno (Or.inl h)
    have hnc : ¬ (N.selectedGraph W).Reachable a c := fun h => hno (Or.inr (Or.inl h))
    have hnd : ¬ (N.selectedGraph W).Reachable a d := fun h => hno (Or.inr (Or.inr h))
    obtain ⟨S, hS⟩ : ∃ S : V → Prop, ∀ w, S w ↔ (N.selectedGraph W).Reachable a w :=
      ⟨_, fun _ => Iff.rfl⟩
    have hSa : S a := (hS a).2 (SimpleGraph.Reachable.refl a)
    have hclosed : ∀ e, W e ≠ 0 → ¬ False → ¬ False → (S (N.src e) ↔ S (N.dst e)) := by
      intro e he _ _
      rw [hS, hS]
      exact N.reachable_iff_of_edge he a
    obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict W fun e => S (N.src e) ∨ S (N.dst e) :=
      ⟨_, rfl⟩
    have hby : N.boundary y = unitWord a := by
      funext u
      rw [hy, N.boundary_restrict_of_closed W S (fun _ => False) (fun _ h => h.elim) hclosed
        (fun h => h)]
      by_cases hSu : S u
      · rw [if_pos hSu, hb]
        have h1 : u ≠ b := fun h => hnb ((hS b).1 (h ▸ hSu))
        have h2 : u ≠ c := fun h => hnc ((hS c).1 (h ▸ hSu))
        have h3 : u ≠ d := fun h => hnd ((hS d).1 (h ▸ hSu))
        simp [pathDemand, unitWord, h1, h2, h3]
      · rw [if_neg hSu]
        have h1 : u ≠ a := fun h => hSu (h ▸ hSa)
        rw [unitWord_apply, if_neg (Ne.symm h1)]
    have htot := N.total_boundary y
    rw [hby, total_unit] at htot
    exact one_ne_zero htot
  rcases hreach with hr | hr | hr
  · exact Or.inl (N.exists_pathPair_of_reachable hab hcd hac had hbc hbd hb hdeg hmin hr)
  · right
    left
    have hb' : N.boundary W = N.pathDemand a c + N.pathDemand b d := by
      rw [hb]
      show unitWord a + unitWord b + (unitWord c + unitWord d) =
        unitWord a + unitWord c + (unitWord b + unitWord d)
      abel
    exact N.exists_pathPair_of_reachable hac hbd hab had hbc.symm hcd hb' hdeg hmin hr
  · right
    right
    have hb' : N.boundary W = N.pathDemand a d + N.pathDemand b c := by
      rw [hb]
      show unitWord a + unitWord b + (unitWord c + unitWord d) =
        unitWord a + unitWord d + (unitWord b + unitWord c)
      abel
    exact N.exists_pathPair_of_reachable had hbc hab hac hbd.symm hcd.symm hb' hdeg hmin hr

/-! ### A cycle through two crossing edges and two given paths -/

/-- Let a cycle `x` contain two crossing edges `e`, `f`, a path of the first side between their
ends in `S`, and a path of the second side between their other ends. Then `x` is the sum of the
two paths and the two edges. -/
theorem IsCycleWord.eq_glue_of_subword {N : Network V E} {S : V → Prop} {e f : E}
    {s₁ s₂ t₁ t₂ : V} (he : N.Joins e s₁ t₁) (hs₁ : S s₁) (ht₁ : ¬ S t₁)
    (hf : N.Joins f s₂ t₂) (hs₂ : S s₂) (ht₂ : ¬ S t₂) (hef : e ≠ f) {x P Q : N.Word}
    (hx : N.IsCycleWord x) (hP : N.IsPathWord s₁ s₂ P) (hPin : Within P (N.inside S))
    (hQ : N.IsPathWord t₁ t₂ Q) (hQout : Within Q (N.outside S)) (hPx : N.IsSubword P x)
    (hQx : N.IsSubword Q x) (hxe : x e ≠ 0) (hxf : x f ≠ 0) :
    P + Q + (unitWord e + unitWord f) = x := by
  have hz := (N.isCycleWord_glue S he hs₁ ht₁ hf hs₂ ht₂ hef hP hPin hQ hQout).1
  exact hx.eq_of_even_subword
    ((hPx.add hQx).add ((N.isSubword_unitWord hxe).add (N.isSubword_unitWord hxf)))
    hz.boundary_eq_zero hz.1

/-! ### The word of four edges -/

section Quad

variable {e₁ e₂ e₃ e₄ : E}

theorem unitQuad_apply_of_ne {g : E} (h1 : g ≠ e₁) (h2 : g ≠ e₂) (h3 : g ≠ e₃) (h4 : g ≠ e₄) :
    (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) g = 0 := by
  show unitWord e₁ g + unitWord e₂ g + (unitWord e₃ g + unitWord e₄ g) = 0
  rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply, if_neg (Ne.symm h1),
    if_neg (Ne.symm h2), if_neg (Ne.symm h3), if_neg (Ne.symm h4), add_zero, add_zero]

theorem unitQuad_apply_one (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h14 : e₁ ≠ e₄) :
    (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) e₁ = 1 := by
  show unitWord e₁ e₁ + unitWord e₂ e₁ + (unitWord e₃ e₁ + unitWord e₄ e₁) = 1
  rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply, if_pos rfl,
    if_neg (Ne.symm h12), if_neg (Ne.symm h13), if_neg (Ne.symm h14), add_zero, add_zero,
    add_zero]

theorem unitQuad_apply_two (h12 : e₁ ≠ e₂) (h23 : e₂ ≠ e₃) (h24 : e₂ ≠ e₄) :
    (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) e₂ = 1 := by
  show unitWord e₁ e₂ + unitWord e₂ e₂ + (unitWord e₃ e₂ + unitWord e₄ e₂) = 1
  rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply, if_neg h12, if_pos rfl,
    if_neg (Ne.symm h23), if_neg (Ne.symm h24), zero_add, add_zero, add_zero]

theorem unitQuad_apply_three (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (h34 : e₃ ≠ e₄) :
    (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) e₃ = 1 := by
  show unitWord e₁ e₃ + unitWord e₂ e₃ + (unitWord e₃ e₃ + unitWord e₄ e₃) = 1
  rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply, if_neg h13, if_neg h23,
    if_pos rfl, if_neg (Ne.symm h34), zero_add, add_zero, zero_add]

theorem unitQuad_apply_four (h14 : e₁ ≠ e₄) (h24 : e₂ ≠ e₄) (h34 : e₃ ≠ e₄) :
    (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) e₄ = 1 := by
  show unitWord e₁ e₄ + unitWord e₂ e₄ + (unitWord e₃ e₄ + unitWord e₄ e₄) = 1
  rw [unitWord_apply, unitWord_apply, unitWord_apply, unitWord_apply, if_neg h14, if_neg h24,
    if_neg h34, if_pos rfl, zero_add, zero_add, zero_add]

end Quad

/-! ### The parts of a cycle through four crossing edges -/

/-- **The parts of a cycle through four crossing edges.** Let the edge `eᵢ` join `sᵢ ∈ S` and
`tᵢ ∉ S`, with distinct `sᵢ`, and let `x` be a cycle whose crossing edges are exactly these four
edges. Then `x` is the sum of its parts in the two sides and of the four edges. Each part has odd
degree exactly at the four ends, all its degrees are at most two, and it has no nonzero even
sub-word. -/
theorem IsCycleWord.parts_of_crossSet_four {N : Network V E} {S : V → Prop} {e₁ e₂ e₃ e₄ : E}
    {s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : V} (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂)
    (h₃ : N.Joins e₃ s₃ t₃) (h₄ : N.Joins e₄ s₄ t₄) (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃)
    (hs₄ : S s₄) (ht₁ : ¬ S t₁) (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃) (ht₄ : ¬ S t₄)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs14 : s₁ ≠ s₄) (hs23 : s₂ ≠ s₃) (hs24 : s₂ ≠ s₄)
    (hs34 : s₃ ≠ s₄) {T : Finset E} (hT : ∀ g, g ∈ T ↔ g = e₁ ∨ g = e₂ ∨ g = e₃ ∨ g = e₄)
    {x : N.Word} (hx : N.IsCycleWord x) (hcs : N.crossSet S x = T) :
    x = restrict x (N.inside S) + restrict x (N.outside S) +
        (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) ∧
      N.boundary (restrict x (N.inside S)) = N.pathDemand s₁ s₂ + N.pathDemand s₃ s₄ ∧
      N.boundary (restrict x (N.outside S)) = N.pathDemand t₁ t₂ + N.pathDemand t₃ t₄ ∧
      (∀ z : N.Word, N.IsSubword z (restrict x (N.inside S)) → N.boundary z = 0 → z = 0) ∧
      (∀ z : N.Word, N.IsSubword z (restrict x (N.outside S)) → N.boundary z = 0 → z = 0) ∧
      (∀ v, N.deg (restrict x (N.inside S)) v ≤ 2) ∧
      (∀ v, N.deg (restrict x (N.outside S)) v ≤ 2) := by
  have hc₁ : N.crosses S e₁ := N.crosses_of_joins h₁ hs₁ ht₁
  have hc₂ : N.crosses S e₂ := N.crosses_of_joins h₂ hs₂ ht₂
  have hc₃ : N.crosses S e₃ := N.crosses_of_joins h₃ hs₃ ht₃
  have hc₄ : N.crosses S e₄ := N.crosses_of_joins h₄ hs₄ ht₄
  have h12 : e₁ ≠ e₂ := N.ne_of_joins h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12
  have h13 : e₁ ≠ e₃ := N.ne_of_joins h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13
  have h14 : e₁ ≠ e₄ := N.ne_of_joins h₁ hs₁ ht₁ h₄ hs₄ ht₄ hs14
  have h23 : e₂ ≠ e₃ := N.ne_of_joins h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23
  have h24 : e₂ ≠ e₄ := N.ne_of_joins h₂ hs₂ ht₂ h₄ hs₄ ht₄ hs24
  have h34 : e₃ ≠ e₄ := N.ne_of_joins h₃ hs₃ ht₃ h₄ hs₄ ht₄ hs34
  have hmem : ∀ g, (N.crosses S g ∧ x g ≠ 0) ↔ (g = e₁ ∨ g = e₂ ∨ g = e₃ ∨ g = e₄) := by
    intro g
    rw [← N.mem_crossSet, hcs, hT]
  have hxe₁ : x e₁ = 1 := bit_eq_one_of_ne_zero ((hmem e₁).2 (Or.inl rfl)).2
  have hxe₂ : x e₂ = 1 := bit_eq_one_of_ne_zero ((hmem e₂).2 (Or.inr (Or.inl rfl))).2
  have hxe₃ : x e₃ = 1 := bit_eq_one_of_ne_zero ((hmem e₃).2 (Or.inr (Or.inr (Or.inl rfl)))).2
  have hxe₄ : x e₄ = 1 := bit_eq_one_of_ne_zero ((hmem e₄).2 (Or.inr (Or.inr (Or.inr rfl)))).2
  have hcross : restrict x (N.crosses S) =
      unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄) := by
    funext g
    by_cases hg1 : g = e₁
    · rw [hg1, restrict_apply_of_pos x hc₁, hxe₁]
      exact (unitQuad_apply_one h12 h13 h14).symm
    · by_cases hg2 : g = e₂
      · rw [hg2, restrict_apply_of_pos x hc₂, hxe₂]
        exact (unitQuad_apply_two h12 h23 h24).symm
      · by_cases hg3 : g = e₃
        · rw [hg3, restrict_apply_of_pos x hc₃, hxe₃]
          exact (unitQuad_apply_three h13 h23 h34).symm
        · by_cases hg4 : g = e₄
          · rw [hg4, restrict_apply_of_pos x hc₄, hxe₄]
            exact (unitQuad_apply_four h14 h24 h34).symm
          · rw [unitQuad_apply_of_ne hg1 hg2 hg3 hg4]
            refine Classical.not_not.1 fun hne => ?_
            obtain ⟨hc, hxg⟩ := (restrict_ne_zero_iff x _ g).1 hne
            rcases (hmem g).1 ⟨hc, hxg⟩ with h | h | h | h
            · exact hg1 h
            · exact hg2 h
            · exact hg3 h
            · exact hg4 h
  have hsum : x = restrict x (N.inside S) + restrict x (N.outside S) +
      (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) := by
    rw [← hcross]
    exact (N.restrict_add_restrict_add_restrict S x).symm
  have hbR : N.boundary (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) =
      N.pathDemand s₁ s₂ + N.pathDemand s₃ s₄ + (N.pathDemand t₁ t₂ + N.pathDemand t₃ t₄) := by
    rw [map_add, map_add, map_add, N.boundary_unitWord_of_joins h₁,
      N.boundary_unitWord_of_joins h₂, N.boundary_unitWord_of_joins h₃,
      N.boundary_unitWord_of_joins h₄]
    show unitWord s₁ + unitWord t₁ + (unitWord s₂ + unitWord t₂) +
        (unitWord s₃ + unitWord t₃ + (unitWord s₄ + unitWord t₄)) =
      unitWord s₁ + unitWord s₂ + (unitWord s₃ + unitWord s₄) +
        (unitWord t₁ + unitWord t₂ + (unitWord t₃ + unitWord t₄))
    abel
  have hb : N.boundary (restrict x (N.inside S)) + N.boundary (restrict x (N.outside S)) =
      N.pathDemand s₁ s₂ + N.pathDemand s₃ s₄ + (N.pathDemand t₁ t₂ + N.pathDemand t₃ t₄) := by
    apply word_eq_of_add_eq_zero
    rw [← hbR, ← map_add N.boundary, ← map_add N.boundary, ← hsum]
    exact hx.boundary_eq_zero
  have ha1 : ∀ v, ¬ S v → (N.pathDemand s₁ s₂ + N.pathDemand s₃ s₄) v = 0 := by
    intro v hv
    have k1 : v ≠ s₁ := fun h => hv (h ▸ hs₁)
    have k2 : v ≠ s₂ := fun h => hv (h ▸ hs₂)
    have k3 : v ≠ s₃ := fun h => hv (h ▸ hs₃)
    have k4 : v ≠ s₄ := fun h => hv (h ▸ hs₄)
    simp [pathDemand, k1, k2, k3, k4]
  have hb1 : ∀ v, S v → (N.pathDemand t₁ t₂ + N.pathDemand t₃ t₄) v = 0 := by
    intro v hv
    have k1 : v ≠ t₁ := fun h => ht₁ (h ▸ hv)
    have k2 : v ≠ t₂ := fun h => ht₂ (h ▸ hv)
    have k3 : v ≠ t₃ := fun h => ht₃ (h ▸ hv)
    have k4 : v ≠ t₄ := fun h => ht₄ (h ▸ hv)
    simp [pathDemand, k1, k2, k3, k4]
  obtain ⟨hbP, hbQ⟩ := N.boundary_split (within_restrict x (N.inside S))
    (within_restrict x (N.outside S)) ha1 hb1 hb
  have hdegx : ∀ v, N.deg x v ≤ 2 := by
    intro v
    rcases hx.2.1 v with h | h <;> omega
  have hminP : ∀ z : N.Word, N.IsSubword z (restrict x (N.inside S)) → N.boundary z = 0 →
      z = 0 := by
    intro z hsub hz0
    refine Classical.not_not.1 fun hne => ?_
    have hzx : z = x :=
      hx.eq_of_even_subword (fun g hg => N.restrict_isSubword x _ g (hsub g hg)) hz0 hne
    have k1 : z e₁ ≠ 0 := by
      rw [hzx, hxe₁]
      exact one_ne_zero
    exact N.not_inside_of_crosses hc₁ (within_restrict x (N.inside S) e₁ (hsub e₁ k1))
  have hminQ : ∀ z : N.Word, N.IsSubword z (restrict x (N.outside S)) → N.boundary z = 0 →
      z = 0 := by
    intro z hsub hz0
    refine Classical.not_not.1 fun hne => ?_
    have hzx : z = x :=
      hx.eq_of_even_subword (fun g hg => N.restrict_isSubword x _ g (hsub g hg)) hz0 hne
    have k1 : z e₁ ≠ 0 := by
      rw [hzx, hxe₁]
      exact one_ne_zero
    exact N.not_outside_of_crosses hc₁ (within_restrict x (N.outside S) e₁ (hsub e₁ k1))
  exact ⟨hsum, hbP, hbQ, hminP, hminQ,
    fun v => le_trans ((N.restrict_isSubword x _).deg_le v) (hdegx v),
    fun v => le_trans ((N.restrict_isSubword x _).deg_le v) (hdegx v)⟩

end Erdos1016.BoundaryTrace.Network

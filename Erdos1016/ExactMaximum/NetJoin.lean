import Erdos1016.ExactMaximum.NetPairs

set_option autoImplicit false

/-!
# Joining disjoint paths by edges

The files `NetCut.lean` and `NetGlue.lean` glue paths across a given cut. For an explicit graph,
such as a ring of the paper "The maximum number of cycles in a graph of large rank", it is easier
to say that two paths have no common vertex. This file restates the gluing lemmas in this form
and adds the cases in which one of the pieces is a single edge.

* `isPathWord_unitWord`: an edge is a path between its ends.
* `IsPathWord.add_pendant`: a path and an edge from its end to a new vertex form a path.
* `IsPathWord.add_closing`: a path and another edge between its ends form a cycle.
* `IsPathWord.glue`: two disjoint paths and an edge between an end of each form a path.
* `IsPathWord.glue_three`: three disjoint paths and two edges that join them in a row form a
  path.
* `IsPathWord.glue_cycle`: two disjoint paths and two edges between their ends form a cycle.
* `IsPathPair.glue`: two path pairs and two edges that join them form a path pair.

The cut in each proof is the set of the vertices of one of the paths.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netJoinDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Degrees of sums and of single edges -/

omit [Fintype V] in
/-- The degree of a sum is at most the sum of the degrees. -/
theorem deg_add_le (N : Network V E) (x y : N.Word) (v : V) :
    N.deg (x + y) v ≤ N.deg x v + N.deg y v := by
  unfold deg
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro e he
  have h := (Finset.mem_filter.1 he).2
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  rcases Classical.em (x e = 0) with h0 | h0
  · right
    refine ⟨Finset.mem_univ e, ?_, h.2⟩
    intro hy
    apply h.1
    show x e + y e = 0
    rw [h0, hy, add_zero]
  · exact Or.inl ⟨Finset.mem_univ e, h0, h.2⟩

omit [Fintype V] in
/-- A single edge has degree one at each of its ends. -/
theorem deg_unitWord_eq_one (N : Network V E) {e : E} {v : V}
    (hv : N.src e = v ∨ N.dst e = v) : N.deg (unitWord e) v = 1 := by
  unfold deg
  rw [Finset.card_eq_one]
  refine ⟨e, ?_⟩
  ext g
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hg, _⟩
    refine Classical.not_not.1 fun hne => hg ?_
    rw [unitWord_apply, if_neg (Ne.symm hne)]
  · intro hg
    rw [hg]
    refine ⟨Finset.mem_univ e, ?_, hv⟩
    rw [unitWord_apply, if_pos rfl]
    exact one_ne_zero

omit [Fintype V] in
/-- A single edge has degree zero at every vertex that is not one of its ends. -/
theorem deg_unitWord_eq_zero (N : Network V E) {e : E} {v : V} (h1 : N.src e ≠ v)
    (h2 : N.dst e ≠ v) : N.deg (unitWord e) v = 0 := by
  apply N.deg_eq_zero_of_forall
  intro g hg
  rw [unitWord_apply, if_neg]
  intro heg
  rw [← heg] at hg
  rcases hg with hg | hg
  · exact h1 hg
  · exact h2 hg

omit [Fintype V] in
/-- A single edge that joins `s` and `t` has degree zero at every other vertex. -/
theorem deg_unitWord_of_joins (N : Network V E) {e : E} {s t v : V} (h : N.Joins e s t)
    (hs : v ≠ s) (ht : v ≠ t) : N.deg (unitWord e) v = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact N.deg_unitWord_eq_zero (fun h' => hs (h'.symm.trans h1)) (fun h' => ht (h'.symm.trans h2))
  · exact N.deg_unitWord_eq_zero (fun h' => ht (h'.symm.trans h1)) (fun h' => hs (h'.symm.trans h2))

omit [Fintype V] in
/-- A word without a vertex at `v` has no edge at `v`. -/
theorem eq_zero_of_deg_eq_zero (N : Network V E) {x : N.Word} {v : V} (h : N.deg x v = 0)
    {g : E} (hg : N.src g = v ∨ N.dst g = v) : x g = 0 := by
  refine Classical.not_not.1 fun hne => ?_
  rcases hg with hg | hg
  · have h1 := N.deg_src_pos hne
    rw [hg] at h1
    omega
  · have h1 := N.deg_dst_pos hne
    rw [hg] at h1
    omega

/-! ### Words without a common vertex -/

omit [Fintype V] in
theorem VertexDisjoint.add_right {N : Network V E} {A X Y : N.Word}
    (h1 : N.VertexDisjoint A X) (h2 : N.VertexDisjoint A Y) : N.VertexDisjoint A (X + Y) := by
  intro v
  rcases h1 v with h | h
  · exact Or.inl h
  · rcases h2 v with h' | h'
    · exact Or.inl h'
    · right
      have h3 := N.deg_add_le X Y v
      omega

omit [Fintype V] in
theorem VertexDisjoint.add_left {N : Network V E} {A X Y : N.Word}
    (h1 : N.VertexDisjoint X A) (h2 : N.VertexDisjoint Y A) : N.VertexDisjoint (X + Y) A :=
  (h1.symm.add_right h2.symm).symm

omit [Fintype V] in
/-- A word is vertex-disjoint from an edge whose two ends are not vertices of the word. -/
theorem vertexDisjoint_unitWord (N : Network V E) {A : N.Word} {e : E} {s t : V}
    (he : N.Joins e s t) (hs : N.deg A s = 0) (ht : N.deg A t = 0) :
    N.VertexDisjoint A (unitWord e) := by
  intro v
  by_cases h1 : v = s
  · left
    rw [h1]
    exact hs
  · by_cases h2 : v = t
    · left
      rw [h2]
      exact ht
    · right
      exact N.deg_unitWord_of_joins he h1 h2

omit [Fintype V] in
/-- A vertex of the first word is not a vertex of the second word. -/
theorem VertexDisjoint.deg_right_eq_zero {N : Network V E} {A B : N.Word}
    (h : N.VertexDisjoint A B) {v : V} (hv : 0 < N.deg A v) : N.deg B v = 0 := by
  rcases h v with h0 | h0
  · omega
  · exact h0

omit [Fintype V] in
/-- A vertex of the second word is not a vertex of the first word. -/
theorem VertexDisjoint.deg_left_eq_zero {N : Network V E} {A B : N.Word}
    (h : N.VertexDisjoint A B) {v : V} (hv : 0 < N.deg B v) : N.deg A v = 0 := by
  rcases h v with h0 | h0
  · exact h0
  · omega

/-! ### The ends of a path -/

omit [Fintype V] in
theorem IsPathWord.deg_left_pos {N : Network V E} {a b : V} {P : N.Word}
    (h : N.IsPathWord a b P) : 0 < N.deg P a := by
  rw [h.2.1]
  exact Nat.one_pos

omit [Fintype V] in
theorem IsPathWord.deg_right_pos {N : Network V E} {a b : V} {P : N.Word}
    (h : N.IsPathWord a b P) : 0 < N.deg P b := by
  rw [h.2.2.1]
  exact Nat.one_pos

/-! ### Single edges -/

omit [Fintype V] in
/-- **An edge is a path between its ends.** -/
theorem isPathWord_unitWord (N : Network V E) {e : E} {a b : V} (h : N.Joins e a b) :
    N.IsPathWord a b (unitWord e) := by
  refine ⟨h.ne, N.deg_unitWord_eq_one h.at_left, N.deg_unitWord_eq_one h.at_right,
    fun v hva hvb => Or.inl (N.deg_unitWord_of_joins h hva hvb), fun v hv => ?_⟩
  by_cases hva : v = a
  · rw [hva]
  · by_cases hvb : v = b
    · rw [hvb]
      have hadj : (N.selectedGraph (unitWord e)).Adj a b := by
        refine ⟨e, ?_, h⟩
        rw [unitWord_apply, if_pos rfl]
        exact one_ne_zero
      exact hadj.reachable
    · have h0 := N.deg_unitWord_of_joins h hva hvb
      omega

/-- **A path and a pendant edge.** Let `P` be a path from `a` to `b`, and let the edge `e` join
`b` and a vertex `v` that is not on `P`. Then `P` and `e` form a path from `a` to `v`. -/
theorem IsPathWord.add_pendant {N : Network V E} {a b v : V} {P : N.Word} {e : E}
    (hP : N.IsPathWord a b P) (he : N.Joins e b v) (hv : N.deg P v = 0) :
    N.IsPathWord a v (P + unitWord e) := by
  have hav : a ≠ v := by
    intro h
    have h1 := hP.2.1
    rw [h] at h1
    omega
  have hPe : P e = 0 := N.eq_zero_of_deg_eq_zero hv he.at_right
  -- the values of the sum away from `e`
  have hval : ∀ g, g ≠ e → (P + unitWord e) g = P g := by
    intro g hg
    show P g + unitWord e g = P g
    rw [unitWord_apply, if_neg (Ne.symm hg), add_zero]
  apply N.isPathWord_of_minimal hav
  · rw [map_add, hP.boundary_eq, N.boundary_unitWord_of_joins he]
    show unitWord a + unitWord b + (unitWord b + unitWord v) = unitWord a + unitWord v
    have h3 : ∀ p q w : V → Bit, p + q + (q + w) = p + w := by
      intro p q w
      have h : p + q + (q + w) = p + w + (q + q) := by abel
      rw [h, word_add_self q, add_zero]
    exact h3 _ _ _
  · intro y hsub hy0
    -- the cut around the vertex `v`
    have hce : N.crosses (fun u => u = v) e :=
      N.crosses_of_joins he.symm rfl (fun h => he.ne h)
    have hyother : ∀ g, N.crosses (fun u => u = v) g → g ≠ e → y g = 0 := by
      intro g hg hne
      refine Classical.not_not.1 fun hy => hsub g hy ?_
      rw [hval g hne]
      -- a crossing edge is at `v`
      have hat : N.src g = v ∨ N.dst g = v := by
        refine Classical.not_not.1 fun hno => hg ?_
        exact ⟨fun h => absurd (Or.inl h) hno, fun h => absurd (Or.inr h) hno⟩
      exact N.eq_zero_of_deg_eq_zero hv hat
    have hye : y e = 0 := by
      have hsum : (∑ g, if N.crosses (fun u => u = v) g then y g else 0) = y e := by
        rw [Finset.sum_eq_single e]
        · rw [if_pos hce]
        · intro g _ hg
          by_cases hc : N.crosses (fun u => u = v) g
          · rw [if_pos hc]
            exact hyother g hc hg
          · rw [if_neg hc]
        · intro h
          exact absurd (Finset.mem_univ e) h
      rw [← hsum, ← N.cut_parity (fun u => u = v) y, hy0]
      simp
    apply hP.minimal y _ hy0
    intro g hg
    have hne : g ≠ e := fun h => hg (h ▸ hye)
    rw [← hval g hne]
    exact hsub g hg

/-- **A path and a closing edge.** Let `P` be a path from `a` to `b`, and let `e` be an edge
that joins `a` and `b` and is not an edge of `P`. Then `P` and `e` form a cycle. -/
theorem IsPathWord.add_closing {N : Network V E} {a b : V} {P : N.Word} {e : E}
    (hP : N.IsPathWord a b P) (he : N.Joins e a b) (hPe : P e = 0) :
    N.IsCycleWord (P + unitWord e) := by
  obtain ⟨x, hxdef⟩ : ∃ x : N.Word, x = P + unitWord e := ⟨_, rfl⟩
  rw [← hxdef]
  have hxe : x e = 1 := by
    rw [hxdef]
    show P e + unitWord e e = 1
    rw [hPe, unitWord_apply, if_pos rfl, zero_add]
  have hval : ∀ g, g ≠ e → x g = P g := by
    intro g hg
    rw [hxdef]
    show P g + unitWord e g = P g
    rw [unitWord_apply, if_neg (Ne.symm hg), add_zero]
  have hx0 : N.boundary x = 0 := by
    rw [hxdef, map_add, hP.boundary_eq, N.boundary_unitWord_of_joins he]
    exact word_add_self _
  -- an even sub-word without `e` is a sub-word of `P`
  have hstar : ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y e = 0 → y = 0 := by
    intro y hsub hy0 hye
    apply hP.minimal y _ hy0
    intro g hg
    have hne : g ≠ e := fun h => hg (h ▸ hye)
    rw [← hval g hne]
    exact hsub g hg
  apply N.isCycleWord_of_minimal
  · intro h
    rw [h] at hxe
    exact zero_ne_one hxe
  · exact hx0
  · intro y hsub hy0
    rcases bit_cases (y e) with hye | hye
    · exact Or.inl (hstar y hsub hy0 hye)
    · right
      have hz : x + y = 0 := by
        apply hstar (x + y) (IsSubword.add_self hsub)
        · rw [map_add, hx0, hy0, add_zero]
        · show x e + y e = 0
          rw [hxe, hye]
          exact bit_add_self 1
      exact (word_eq_of_add_eq_zero hz).symm

/-! ### Joining disjoint paths -/

/-- **Two disjoint paths and an edge.** Let `A` be a path from `a` to `s` and `Q` a path from `t`
to `b` without a common vertex, and let the edge `e` join `s` and `t`. Then `A`, `Q` and `e` form
a path from `a` to `b`. -/
theorem IsPathWord.glue {N : Network V E} {a s t b : V} {A Q : N.Word} {e : E}
    (hA : N.IsPathWord a s A) (hQ : N.IsPathWord t b Q) (he : N.Joins e s t)
    (hd : N.VertexDisjoint A Q) : N.IsPathWord a b (A + Q + unitWord e) := by
  have hs : N.verts A s := hA.deg_right_pos
  have ht : ¬ N.verts A t := by
    intro h
    have h' : 0 < N.deg A t := h
    have h0 := hd.deg_left_eq_zero hQ.deg_left_pos
    omega
  exact N.isPathWord_glue (N.verts A) he hs ht hA (N.within_inside_verts A) hQ
    hd.within_outside_verts

/-- **Three disjoint paths in a row.** Let `A` be a path from `a₁` to `s₁`, `Q` a path from `t₁`
to `t₂`, and `B` a path from `s₂` to `a₂`, pairwise without a common vertex. Let `e₁` join `s₁`
and `t₁`, and let `e₂` join `t₂` and `s₂`. Then the three paths and the two edges form a path
from `a₁` to `a₂`. -/
theorem IsPathWord.glue_three {N : Network V E} {a₁ s₁ t₁ t₂ s₂ a₂ : V} {A Q B : N.Word}
    {e₁ e₂ : E} (hA : N.IsPathWord a₁ s₁ A) (hQ : N.IsPathWord t₁ t₂ Q)
    (hB : N.IsPathWord s₂ a₂ B) (he₁ : N.Joins e₁ s₁ t₁) (he₂ : N.Joins e₂ t₂ s₂)
    (hAQ : N.VertexDisjoint A Q) (hAB : N.VertexDisjoint A B) (hQB : N.VertexDisjoint Q B) :
    N.IsPathWord a₁ a₂ (A + Q + unitWord e₁ + B + unitWord e₂) := by
  have h1 : N.IsPathWord a₁ t₂ (A + Q + unitWord e₁) := hA.glue hQ he₁ hAQ
  have hd : N.VertexDisjoint (A + Q + unitWord e₁) B :=
    VertexDisjoint.add_left (VertexDisjoint.add_left hAB hQB)
      (N.vertexDisjoint_unitWord he₁ (hAB.deg_right_eq_zero hA.deg_right_pos)
        (hQB.deg_right_eq_zero hQ.deg_left_pos)).symm
  exact h1.glue hB he₂ hd

/-- **Two disjoint paths and two edges.** Let `P` be a path from `s₁` to `s₂` and `Q` a path
from `t₁` to `t₂` without a common vertex. Let `e` join `s₁` and `t₁`, and let `f` join `s₂` and
`t₂`. Then the two paths and the two edges form a cycle. -/
theorem IsPathWord.glue_cycle {N : Network V E} {s₁ s₂ t₁ t₂ : V} {P Q : N.Word} {e f : E}
    (hP : N.IsPathWord s₁ s₂ P) (hQ : N.IsPathWord t₁ t₂ Q) (he : N.Joins e s₁ t₁)
    (hf : N.Joins f s₂ t₂) (hd : N.VertexDisjoint P Q) :
    N.IsCycleWord (P + Q + (unitWord e + unitWord f)) := by
  have hs₁ : N.verts P s₁ := hP.deg_left_pos
  have hs₂ : N.verts P s₂ := hP.deg_right_pos
  have ht₁ : ¬ N.verts P t₁ := by
    intro h
    have h' : 0 < N.deg P t₁ := h
    have h0 := hd.deg_left_eq_zero hQ.deg_left_pos
    omega
  have ht₂ : ¬ N.verts P t₂ := by
    intro h
    have h' : 0 < N.deg P t₂ := h
    have h0 := hd.deg_left_eq_zero hQ.deg_right_pos
    omega
  have hef : e ≠ f := N.ne_of_joins he hs₁ ht₁ hf hs₂ ht₂ hP.1
  exact (N.isCycleWord_glue (N.verts P) he hs₁ ht₁ hf hs₂ ht₂ hef hP
    (N.within_inside_verts P) hQ hd.within_outside_verts).1

/-- **Two path pairs and two edges.** Let `A`, `B` be disjoint paths from `a₁` to `s₁` and from
`a₂` to `s₂`, and let `C`, `D` be disjoint paths from `t₁` to `r₁` and from `t₂` to `r₂`, such
that no path of the first pair has a common vertex with a path of the second pair. Let `e₁` join
`s₁` and `t₁`, and let `e₂` join `s₂` and `t₂`. Then `A`, `e₁`, `C` and `B`, `e₂`, `D` are
disjoint paths from `a₁` to `r₁` and from `a₂` to `r₂`. -/
theorem IsPathPair.glue {N : Network V E} {a₁ s₁ t₁ r₁ a₂ s₂ t₂ r₂ : V} {A B C D : N.Word}
    {e₁ e₂ : E} (hAB : N.IsPathPair a₁ s₁ a₂ s₂ A B) (hCD : N.IsPathPair t₁ r₁ t₂ r₂ C D)
    (he₁ : N.Joins e₁ s₁ t₁) (he₂ : N.Joins e₂ s₂ t₂) (hAC : N.VertexDisjoint A C)
    (hAD : N.VertexDisjoint A D) (hBC : N.VertexDisjoint B C) (hBD : N.VertexDisjoint B D) :
    N.IsPathPair a₁ r₁ a₂ r₂ (A + C + unitWord e₁) (B + D + unitWord e₂) := by
  obtain ⟨hA, hB, hABd⟩ := hAB
  obtain ⟨hC, hD, hCDd⟩ := hCD
  refine ⟨hA.glue hC he₁ hAC, hB.glue hD he₂ hBD, ?_⟩
  -- the second path is disjoint from `A`, from `C` and from the edge `e₁`
  have hY : ∀ X : N.Word, N.VertexDisjoint X B → N.VertexDisjoint X D → N.deg X s₂ = 0 →
      N.deg X t₂ = 0 → N.VertexDisjoint X (B + D + unitWord e₂) := by
    intro X h1 h2 h3 h4
    exact (h1.add_right h2).add_right (N.vertexDisjoint_unitWord he₂ h3 h4)
  have hAY : N.VertexDisjoint A (B + D + unitWord e₂) :=
    hY A hABd hAD (hABd.deg_left_eq_zero hB.deg_right_pos)
      (hAD.deg_left_eq_zero hD.deg_left_pos)
  have hCY : N.VertexDisjoint C (B + D + unitWord e₂) :=
    hY C hBC.symm hCDd (hBC.deg_right_eq_zero hB.deg_right_pos)
      (hCDd.deg_left_eq_zero hD.deg_left_pos)
  -- the ends of `e₁` are not vertices of the second path
  have hdeg : ∀ u, N.deg B u = 0 → N.deg D u = 0 → u ≠ s₂ → u ≠ t₂ →
      N.deg (B + D + unitWord e₂) u = 0 := by
    intro u h1 h2 h3 h4
    have k1 := N.deg_add_le (B + D) (unitWord e₂) u
    have k2 := N.deg_add_le B D u
    have k3 := N.deg_unitWord_of_joins he₂ h3 h4
    omega
  have hs₁ : N.deg (B + D + unitWord e₂) s₁ = 0 := by
    apply hdeg s₁ (hABd.deg_right_eq_zero hA.deg_right_pos)
      (hAD.deg_right_eq_zero hA.deg_right_pos)
    · intro h
      have h0 := hABd.deg_right_eq_zero hA.deg_right_pos
      rw [h, hB.2.2.1] at h0
      omega
    · intro h
      have h0 := hAD.deg_right_eq_zero hA.deg_right_pos
      rw [h, hD.2.1] at h0
      omega
  have ht₁ : N.deg (B + D + unitWord e₂) t₁ = 0 := by
    apply hdeg t₁ (hBC.deg_left_eq_zero hC.deg_left_pos)
      (hCDd.deg_right_eq_zero hC.deg_left_pos)
    · intro h
      have h0 := hBC.deg_left_eq_zero hC.deg_left_pos
      rw [h, hB.2.2.1] at h0
      omega
    · intro h
      have h0 := hCDd.deg_right_eq_zero hC.deg_left_pos
      rw [h, hD.2.1] at h0
      omega
  exact VertexDisjoint.add_left (VertexDisjoint.add_left hAY hCY)
    (N.vertexDisjoint_unitWord he₁ hs₁ ht₁).symm

end Erdos1016.BoundaryTrace.Network

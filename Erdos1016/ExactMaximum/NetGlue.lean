import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# Gluing paths across a cut

This file continues `NetCut.lean`. It proves two statements about a cut `S` of a network.

* `isPathWord_glue`: a path of the first side that ends in `s`, a crossing edge from `s` to `t`,
  and a path of the second side that starts in `t` form a path.
* `isCycleWord_glue4`: let four crossing edges join `sᵢ ∈ S` and `tᵢ ∉ S`. Two disjoint paths of
  the first side from `s₁` to `s₂` and from `s₃` to `s₄`, two disjoint paths of the second side
  from `t₁` to `t₃` and from `t₂` to `t₄`, and the four edges form a cycle. This is one half of
  Lemma 6.4 of the paper "The maximum number of cycles in a graph of large rank": if the
  pairings of the ends in the two sides are different, the union is one cycle.

The second statement follows from the first one and from `isCycleWord_glue`, applied to cuts
that are the vertex sets of the paths.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netGlueDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Words within a set of edges -/

omit [Fintype E] in
theorem Within.add {x y : E → Bit} {p : E → Prop} (hx : Within x p) (hy : Within y p) :
    Within (x + y) p := by
  intro g hg
  rcases Classical.em (x g = 0) with h0 | h0
  · apply hy g
    intro hy0
    apply hg
    show x g + y g = 0
    rw [h0, hy0, add_zero]
  · exact hx g h0

theorem within_unitWord {p : E → Prop} {e : E} (h : p e) : Within (unitWord e) p := by
  intro g hg
  rcases Classical.em (g = e) with h0 | h0
  · rw [h0]
    exact h
  · exfalso
    apply hg
    rw [unitWord_apply, if_neg (Ne.symm h0)]

omit [Fintype V] [Fintype E] in
/-- An edge that joins two vertices outside `S` is outside. -/
theorem outside_of_joins (N : Network V E) {S : V → Prop} {e : E} {s t : V}
    (h : N.Joins e s t) (hs : ¬ S s) (ht : ¬ S t) : N.outside S e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1]; exact hs, by rw [h2]; exact ht⟩
  · exact ⟨by rw [h1]; exact ht, by rw [h2]; exact hs⟩

/-! ### The vertices of a word -/

/-- The vertices of the word `x`: the ends of its edges. -/
def verts (N : Network V E) (x : N.Word) : V → Prop := fun v => 0 < N.deg x v

omit [Fintype V] in
/-- A word is within the first side of the cut that its vertices define. -/
theorem within_inside_verts (N : Network V E) (x : N.Word) :
    Within x (N.inside (N.verts x)) :=
  fun _ he => ⟨N.deg_src_pos he, N.deg_dst_pos he⟩

omit [Fintype V] in
theorem VertexDisjoint.symm {N : Network V E} {A C : N.Word} (h : N.VertexDisjoint A C) :
    N.VertexDisjoint C A := fun v => (h v).symm

omit [Fintype V] in
/-- A word that is vertex-disjoint from `A` is within the second side of the cut that the
vertices of `A` define. -/
theorem VertexDisjoint.within_outside_verts {N : Network V E} {A C : N.Word}
    (h : N.VertexDisjoint A C) : Within C (N.outside (N.verts A)) := by
  intro g hg
  constructor
  · intro hA
    have h1 := N.deg_src_pos hg
    have hA' : 0 < N.deg A (N.src g) := hA
    rcases h (N.src g) with h0 | h0 <;> omega
  · intro hA
    have h1 := N.deg_dst_pos hg
    have hA' : 0 < N.deg A (N.dst g) := hA
    rcases h (N.dst g) with h0 | h0 <;> omega

omit [Fintype V] in
/-- A vertex of a word within the first side is in `S`. -/
theorem mem_of_within_inside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.inside S)) {v : V} (hv : 0 < N.deg x v) : S v := by
  obtain ⟨g, hg, hat⟩ := N.exists_edge_of_deg_pos hv
  rcases hat with hat | hat
  · rw [← hat]
    exact (h g hg).1
  · rw [← hat]
    exact (h g hg).2

omit [Fintype V] in
/-- A vertex of a word within the second side is not in `S`. -/
theorem not_mem_of_within_outside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.outside S)) {v : V} (hv : 0 < N.deg x v) : ¬ S v := by
  obtain ⟨g, hg, hat⟩ := N.exists_edge_of_deg_pos hv
  rcases hat with hat | hat
  · rw [← hat]
    exact (h g hg).1
  · rw [← hat]
    exact (h g hg).2

omit [Fintype V] in
/-- Words within different sides have no common vertex. -/
theorem vertexDisjoint_of_within (N : Network V E) {S : V → Prop} {A C : N.Word}
    (hA : Within A (N.inside S)) (hC : Within C (N.outside S)) : N.VertexDisjoint A C := by
  intro v
  rcases Nat.eq_zero_or_pos (N.deg A v) with h0 | h0
  · exact Or.inl h0
  · right
    rcases Nat.eq_zero_or_pos (N.deg C v) with h1 | h1
    · exact h1
    · exact absurd (N.mem_of_within_inside hA h0) (N.not_mem_of_within_outside hC h1)

/-! ### Paths -/

omit [Fintype V] in
/-- A path from `s` to `t` is a path from `t` to `s`. -/
theorem IsPathWord.symm {N : Network V E} {s t : V} {x : N.Word} (h : N.IsPathWord s t x) :
    N.IsPathWord t s x := by
  refine ⟨h.1.symm, h.2.2.1, h.2.1, fun v hvt hvs => h.2.2.2.1 v hvs hvt, fun v hv => ?_⟩
  have h1 : (N.selectedGraph x).Reachable s t :=
    h.2.2.2.2 t (by rw [h.2.2.1]; exact Nat.one_pos)
  exact h1.symm.trans (h.2.2.2.2 v hv)

/-- A path has no nonzero even sub-word. -/
theorem IsPathWord.minimal {N : Network V E} {s t : V} {x : N.Word} (h : N.IsPathWord s t x) :
    ∀ z : N.Word, N.IsSubword z x → N.boundary z = 0 → z = 0 :=
  fun _ hz hz0 => h.eq_zero_of_even_subword hz hz0

/-- Let `P` and `Q` have no nonzero even sub-word. Let `y` be an even word without a crossing
edge, whose edges in the first side are edges of `P` and whose edges in the second side are
edges of `Q`. Then `y` is zero. -/
theorem eq_zero_of_even_of_sides (N : Network V E) (S : V → Prop) {P Q y : N.Word}
    (hPmin : ∀ z : N.Word, N.IsSubword z P → N.boundary z = 0 → z = 0)
    (hQmin : ∀ z : N.Word, N.IsSubword z Q → N.boundary z = 0 → z = 0)
    (hy0 : N.boundary y = 0) (hnc : ∀ g, y g ≠ 0 → ¬ N.crosses S g)
    (hin : ∀ g, y g ≠ 0 → N.inside S g → P g ≠ 0)
    (hout : ∀ g, y g ≠ 0 → N.outside S g → Q g ≠ 0) : y = 0 := by
  have hclosed : ∀ g, y g ≠ 0 → ¬ False → ¬ False → (S (N.src g) ↔ S (N.dst g)) :=
    fun g hg _ _ => Classical.not_not.1 (hnc g hg)
  have h1 : restrict y (fun g => S (N.src g) ∨ S (N.dst g)) = 0 := by
    apply hPmin
    · intro g hg
      obtain ⟨hor, hyg⟩ := (restrict_ne_zero_iff y _ g).1 hg
      have hiff := hclosed g hyg (fun h => h) (fun h => h)
      have hing : N.inside S g := by
        rcases hor with h | h
        · exact ⟨h, hiff.1 h⟩
        · exact ⟨hiff.2 h, h⟩
      exact hin g hyg hing
    · funext w
      rw [N.boundary_restrict_of_closed y S (fun _ => False) (fun _ h => h.elim) hclosed
        (fun h => h), hy0]
      simp
  have hclosed' : ∀ g, y g ≠ 0 → ¬ False → ¬ False → (¬ S (N.src g) ↔ ¬ S (N.dst g)) :=
    fun g hg h1 h2 => not_congr (hclosed g hg h1 h2)
  have h2 : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) = 0 := by
    apply hQmin
    · intro g hg
      obtain ⟨hor, hyg⟩ := (restrict_ne_zero_iff y _ g).1 hg
      have hiff := hclosed' g hyg (fun h => h) (fun h => h)
      have houtg : N.outside S g := by
        rcases hor with h | h
        · exact ⟨h, hiff.1 h⟩
        · exact ⟨hiff.2 h, h⟩
      exact hout g hyg houtg
    · funext w
      rw [N.boundary_restrict_of_closed y (fun v => ¬ S v) (fun _ => False)
        (fun _ h => h.elim) hclosed' (fun h => h), hy0]
      simp
  funext g
  refine Classical.not_not.1 fun hg => ?_
  by_cases hS : S (N.src g)
  · have h3 : restrict y (fun g => S (N.src g) ∨ S (N.dst g)) g ≠ 0 :=
      (restrict_ne_zero_iff y _ g).2 ⟨Or.inl hS, hg⟩
    exact h3 (congrFun h1 g)
  · have h3 : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) g ≠ 0 :=
      (restrict_ne_zero_iff y _ g).2 ⟨Or.inl hS, hg⟩
    exact h3 (congrFun h2 g)

/-- **Gluing two paths across a cut.** Let the edge `e` join `s ∈ S` and `t ∉ S`. A path of the
first side from `a` to `s`, the edge `e`, and a path of the second side from `t` to `b` form a
path from `a` to `b`. -/
theorem isPathWord_glue (N : Network V E) (S : V → Prop) {e : E} {a s t b : V}
    (he : N.Joins e s t) (hs : S s) (ht : ¬ S t) {P Q : N.Word} (hP : N.IsPathWord a s P)
    (hPin : Within P (N.inside S)) (hQ : N.IsPathWord t b Q)
    (hQout : Within Q (N.outside S)) : N.IsPathWord a b (P + Q + unitWord e) := by
  have hce : N.crosses S e := N.crosses_of_joins he hs ht
  have hSa : S a := N.mem_of_within_inside hPin (by rw [hP.2.1]; exact Nat.one_pos)
  have hSb : ¬ S b := N.not_mem_of_within_outside hQout (by rw [hQ.2.2.1]; exact Nat.one_pos)
  have hab : a ≠ b := fun h => hSb (h ▸ hSa)
  obtain ⟨x, hxdef⟩ : ∃ x : N.Word, x = P + Q + unitWord e := ⟨_, rfl⟩
  rw [← hxdef]
  have hxin : ∀ g, N.inside S g → x g = P g := by
    intro g hg
    have h1 : Q g = 0 := hQout.eq_zero (N.not_outside_of_inside hg)
    have h2 : unitWord e g = 0 := by
      rw [unitWord_apply, if_neg]
      intro h
      exact N.not_crosses_of_inside hg (h ▸ hce)
    rw [hxdef]
    show P g + Q g + unitWord e g = P g
    rw [h1, h2, add_zero, add_zero]
  have hxout : ∀ g, N.outside S g → x g = Q g := by
    intro g hg
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_outside hg)
    have h2 : unitWord e g = 0 := by
      rw [unitWord_apply, if_neg]
      intro h
      exact N.not_crosses_of_outside hg (h ▸ hce)
    rw [hxdef]
    show P g + Q g + unitWord e g = Q g
    rw [h1, h2, zero_add, add_zero]
  have hxcr : ∀ g, N.crosses S g → g ≠ e → x g = 0 := by
    intro g hg hne
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_crosses hg)
    have h2 : Q g = 0 := hQout.eq_zero (N.not_outside_of_crosses hg)
    rw [hxdef]
    show P g + Q g + unitWord e g = 0
    rw [h1, h2, unitWord_apply, if_neg (Ne.symm hne), add_zero, add_zero]
  apply N.isPathWord_of_minimal hab
  · rw [hxdef, map_add, map_add, hP.boundary_eq, hQ.boundary_eq,
      N.boundary_unitWord_of_joins he]
    show unitWord a + unitWord s + (unitWord t + unitWord b) + (unitWord s + unitWord t) =
      unitWord a + unitWord b
    have h3 : ∀ p q r w : V → Bit, p + q + (r + w) + (q + r) = p + w := by
      intro p q r w
      have h : p + q + (r + w) + (q + r) = p + w + (q + q) + (r + r) := by abel
      rw [h, word_add_self q, word_add_self r, add_zero, add_zero]
    exact h3 _ _ _ _
  · intro y hsub hy0
    have hyother : ∀ g, N.crosses S g → g ≠ e → y g = 0 := by
      intro g hg hne
      exact Classical.not_not.1 fun hy => hsub g hy (hxcr g hg hne)
    have hye : y e = 0 := by
      have hsum : (∑ g, if N.crosses S g then y g else 0) = y e := by
        rw [Finset.sum_eq_single e]
        · rw [if_pos hce]
        · intro g _ hg
          by_cases hc : N.crosses S g
          · rw [if_pos hc]
            exact hyother g hc hg
          · rw [if_neg hc]
        · intro h
          exact absurd (Finset.mem_univ e) h
      rw [← hsum, ← N.cut_parity S y, hy0]
      simp
    apply N.eq_zero_of_even_of_sides S hP.minimal hQ.minimal hy0
    · intro g hg hc
      by_cases h1 : g = e
      · exact hg (h1 ▸ hye)
      · exact hg (hyother g hc h1)
    · intro g hg hing
      rw [← hxin g hing]
      exact hsub g hg
    · intro g hg houtg
      rw [← hxout g houtg]
      exact hsub g hg

/-! ### Pairs of disjoint paths -/

/-- Two vertex-disjoint paths, from `a` to `b` and from `c` to `d`. -/
def IsPathPair (N : Network V E) (a b c d : V) (A B : N.Word) : Prop :=
  N.IsPathWord a b A ∧ N.IsPathWord c d B ∧ N.VertexDisjoint A B

/-- **Gluing two pairs of disjoint paths.** Let the edge `eᵢ` join `sᵢ ∈ S` and `tᵢ ∉ S` for
`i = 1, 2, 3, 4`. Let `A`, `B` be disjoint paths of the first side from `s₁` to `s₂` and from
`s₃` to `s₄`. Let `C`, `D` be disjoint paths of the second side from `t₁` to `t₃` and from `t₂`
to `t₄`. Then these four paths and the four edges form a cycle. -/
theorem isCycleWord_glue4 (N : Network V E) (S : V → Prop) {e₁ e₂ e₃ e₄ : E}
    {s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : V} (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂)
    (h₃ : N.Joins e₃ s₃ t₃) (h₄ : N.Joins e₄ s₄ t₄) (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃)
    (hs₄ : S s₄) (ht₁ : ¬ S t₁) (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃) (ht₄ : ¬ S t₄)
    {A B C D : N.Word} (hAB : N.IsPathPair s₁ s₂ s₃ s₄ A B) (hAin : Within A (N.inside S))
    (hBin : Within B (N.inside S)) (hCD : N.IsPathPair t₁ t₃ t₂ t₄ C D)
    (hCout : Within C (N.outside S)) (hDout : Within D (N.outside S)) :
    N.IsCycleWord
      (A + B + (C + D) + (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄))) := by
  obtain ⟨hA, hB, hABd⟩ := hAB
  obtain ⟨hC, hD, hCDd⟩ := hCD
  have dA₁ : 0 < N.deg A s₁ := by rw [hA.2.1]; exact Nat.one_pos
  have dA₂ : 0 < N.deg A s₂ := by rw [hA.2.2.1]; exact Nat.one_pos
  have dB₃ : 0 < N.deg B s₃ := by rw [hB.2.1]; exact Nat.one_pos
  have dB₄ : 0 < N.deg B s₄ := by rw [hB.2.2.1]; exact Nat.one_pos
  have dC₃ : 0 < N.deg C t₃ := by rw [hC.2.2.1]; exact Nat.one_pos
  have dD₄ : 0 < N.deg D t₄ := by rw [hD.2.2.1]; exact Nat.one_pos
  -- the path from `s₄` to `t₁` through `B`, `e₃` and `C`
  have hQ₁ : N.IsPathWord s₄ t₁ (B + C + unitWord e₃) :=
    N.isPathWord_glue S h₃ hs₃ ht₃ hB.symm hBin hC.symm hCout
  -- the cut that the vertices of `D` define
  have hnD_s : ∀ v, S v → ¬ N.verts D v :=
    fun v hv hD' => N.not_mem_of_within_outside hDout hD' hv
  have hnD_t₃ : ¬ N.verts D t₃ := by
    intro h
    have h' : 0 < N.deg D t₃ := h
    rcases hCDd t₃ with h0 | h0 <;> omega
  have hQ₁out : Within (B + C + unitWord e₃) (N.outside (N.verts D)) :=
    ((N.vertexDisjoint_of_within hBin hDout).symm.within_outside_verts.add
      hCDd.symm.within_outside_verts).add
      (within_unitWord (N.outside_of_joins h₃ (hnD_s s₃ hs₃) hnD_t₃))
  -- the path from `t₂` to `t₁` through `D`, `e₄`, `B`, `e₃` and `C`
  have hQ₂ : N.IsPathWord t₂ t₁ (D + (B + C + unitWord e₃) + unitWord e₄) :=
    N.isPathWord_glue (N.verts D) h₄.symm dD₄ (hnD_s s₄ hs₄) hD (N.within_inside_verts D) hQ₁
      hQ₁out
  -- the cut that the vertices of `A` define
  have hnA_t : ∀ v, ¬ S v → ¬ N.verts A v :=
    fun v hv hA' => hv (N.mem_of_within_inside hAin hA')
  have hnA_s₃ : ¬ N.verts A s₃ := by
    intro h
    have h' : 0 < N.deg A s₃ := h
    rcases hABd s₃ with h0 | h0 <;> omega
  have hnA_s₄ : ¬ N.verts A s₄ := by
    intro h
    have h' : 0 < N.deg A s₄ := h
    rcases hABd s₄ with h0 | h0 <;> omega
  have hQ₂out : Within (D + (B + C + unitWord e₃) + unitWord e₄) (N.outside (N.verts A)) :=
    ((N.vertexDisjoint_of_within hAin hDout).within_outside_verts.add
      ((hABd.within_outside_verts.add
        (N.vertexDisjoint_of_within hAin hCout).within_outside_verts).add
        (within_unitWord (N.outside_of_joins h₃ hnA_s₃ (hnA_t t₃ ht₃))))).add
      (within_unitWord (N.outside_of_joins h₄ hnA_s₄ (hnA_t t₄ ht₄)))
  have h12 : e₁ ≠ e₂ := N.ne_of_joins h₁ hs₁ ht₁ h₂ hs₂ ht₂ hA.1
  have hcyc := (N.isCycleWord_glue (N.verts A) h₁ dA₁ (hnA_t t₁ ht₁) h₂ dA₂ (hnA_t t₂ ht₂) h12
    hA (N.within_inside_verts A) hQ₂.symm hQ₂out).1
  have heq : A + B + (C + D) + (unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄)) =
      A + (D + (B + C + unitWord e₃) + unitWord e₄) + (unitWord e₁ + unitWord e₂) := by
    abel
  rw [heq]
  exact hcyc

end Erdos1016.BoundaryTrace.Network

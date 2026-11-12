import Erdos1016.ExactMaximum.NetPaths

set_option autoImplicit false

/-!
# Cycles and paths contain no smaller even word

Let `y` be a sub-word of `x`: every edge of `y` is an edge of `x`.

* If `x` is a cycle and `y` is even and not zero, then `y = x`.
* If `x` is a path and `y` is even, then `y = 0`.

In the paper "The maximum number of cycles in a graph of large rank" these facts are used
without a name: a proper subset of a cycle contains no cycle, and the part of a cycle in one side
of a cut is a set of paths. They let the later proofs work with parities in place of walks.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netMinimalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype E]

/-- Every edge of `y` is an edge of `x`. -/
def IsSubword (_N : Network V E) (y x : E → Bit) : Prop := ∀ e, y e ≠ 0 → x e ≠ 0

/-- A sub-word has smaller degrees. -/
theorem IsSubword.deg_le {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) (v : V) :
    N.deg y v ≤ N.deg x v := by
  apply Finset.card_le_card
  intro e he
  have h1 := (Finset.mem_filter.1 he).2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ e, h e h1.1, h1.2⟩

/-- If a sub-word has the same degree at `v`, it contains every edge of the word at `v`. -/
theorem IsSubword.edge_of_deg_eq {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) {v : V}
    (hd : N.deg x v ≤ N.deg y v) {e : E} (hx : x e ≠ 0) (hv : N.src e = v ∨ N.dst e = v) :
    y e ≠ 0 := by
  have hsub : (Finset.univ.filter fun e : E => y e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)) ⊆
      (Finset.univ.filter fun e : E => x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)) := by
    intro f hf
    have h1 := (Finset.mem_filter.1 hf).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ f, h f h1.1, h1.2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub hd
  have he : e ∈ (Finset.univ.filter fun e : E => x e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ e, hx, hv⟩
  rw [← heq] at he
  exact (Finset.mem_filter.1 he).2.1

omit [Fintype E] in
/-- Two words with the same edges are equal. -/
theorem word_eq_of_support {x y : E → Bit} (h1 : ∀ e, y e ≠ 0 → x e ≠ 0)
    (h2 : ∀ e, x e ≠ 0 → y e ≠ 0) : y = x := by
  funext e
  rcases bit_cases (x e) with hx | hx <;> rcases bit_cases (y e) with hy | hy
  · rw [hx, hy]
  · exact absurd hx (h1 e (by rw [hy]; exact one_ne_zero))
  · exact absurd hy (h2 e (by rw [hx]; exact one_ne_zero))
  · rw [hx, hy]

section

variable [Fintype V]

/-- An even word has an even degree at every vertex. In the form that is used below: a degree
of at most two is zero or two. -/
theorem deg_eq_zero_or_two_of_even (N : Network V E) {y : N.Word} (hy : N.boundary y = 0)
    {v : V} (h2 : N.deg y v ≤ 2) : N.deg y v = 0 ∨ N.deg y v = 2 := by
  have hb : ((N.deg y v : ℕ) : Bit) = 0 := by
    rw [← boundary_eq_deg, hy]
    rfl
  have h3 : N.deg y v = 0 ∨ N.deg y v = 1 ∨ N.deg y v = 2 := by omega
  rcases h3 with h | h | h
  · exact Or.inl h
  · rw [h] at hb
    exact absurd hb (by decide)
  · exact Or.inr h

/-- **A cycle contains no smaller even word.** If `y` is a nonzero even sub-word of a cycle `x`,
then `y = x`. -/
theorem IsCycleWord.eq_of_even_subword {N : Network V E} {x y : N.Word} (hx : N.IsCycleWord x)
    (hsub : N.IsSubword y x) (hy : N.boundary y = 0) (hne : y ≠ 0) : y = x := by
  have hdeg2 : ∀ v, N.deg x v ≤ 2 := by
    intro v
    rcases hx.2.1 v with h | h <;> omega
  have hyd : ∀ v, N.deg y v = 0 ∨ N.deg y v = 2 := fun v =>
    N.deg_eq_zero_or_two_of_even hy (le_trans (hsub.deg_le v) (hdeg2 v))
  -- at a vertex of degree two in `y`, all edges of `x` are edges of `y`
  have hfull : ∀ v, N.deg y v = 2 → ∀ e, x e ≠ 0 → (N.src e = v ∨ N.dst e = v) → y e ≠ 0 := by
    intro v hv e he hev
    exact hsub.edge_of_deg_eq (by rw [hv]; exact hdeg2 v) he hev
  -- the vertices of degree two in `y` are closed under the edges of `x`
  have hwalk : ∀ u w, (N.selectedGraph x).Walk u w → N.deg y u = 2 → N.deg y w = 2 := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons a b c hadj _ ih =>
      intro ha
      apply ih
      obtain ⟨e, he, hends⟩ := hadj
      have hye : y e ≠ 0 := hfull a ha e he (by
        rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2)
      have hb : 0 < N.deg y b := by
        rcases hends with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2 ▸ N.deg_dst_pos hye
        · exact h1 ▸ N.deg_src_pos hye
      rcases hyd b with h | h
      · omega
      · exact h
  -- a first vertex of `y`
  obtain ⟨e₀, he₀⟩ : ∃ e, y e ≠ 0 := by
    rcases Classical.em (∃ e, y e ≠ 0) with h | h
    · exact h
    · exfalso
      apply hne
      funext e
      exact Classical.not_not.1 fun hn => h ⟨e, hn⟩
  have hv₀ : N.deg y (N.src e₀) = 2 := by
    have := N.deg_src_pos he₀
    rcases hyd (N.src e₀) with h | h
    · omega
    · exact h
  have hxv₀ : 0 < N.deg x (N.src e₀) := by
    have := hsub.deg_le (N.src e₀)
    omega
  -- every edge of `x` is an edge of `y`
  refine word_eq_of_support hsub ?_
  intro e he
  obtain ⟨p⟩ := hx.2.2 (N.src e₀) (N.src e) hxv₀ (N.deg_src_pos he)
  exact hfull (N.src e) (hwalk _ _ p hv₀) e he (Or.inl rfl)

/-- **A path contains no even word.** If `y` is an even sub-word of a path `x`, then `y = 0`. -/
theorem IsPathWord.eq_zero_of_even_subword {N : Network V E} {s t : V} {x y : N.Word}
    (hx : N.IsPathWord s t x) (hsub : N.IsSubword y x) (hy : N.boundary y = 0) : y = 0 := by
  refine Classical.not_not.1 fun hne => ?_
  have hdeg2 : ∀ v, N.deg x v ≤ 2 := by
    intro v
    by_cases hs : v = s
    · rw [hs, hx.2.1]
      omega
    · by_cases ht : v = t
      · rw [ht, hx.2.2.1]
        omega
      · rcases hx.2.2.2.1 v hs ht with h | h <;> omega
  have hyd : ∀ v, N.deg y v = 0 ∨ N.deg y v = 2 := fun v =>
    N.deg_eq_zero_or_two_of_even hy (le_trans (hsub.deg_le v) (hdeg2 v))
  have hys : N.deg y s = 0 := by
    have h1 := hsub.deg_le s
    rw [hx.2.1] at h1
    rcases hyd s with h | h <;> omega
  have hfull : ∀ v, N.deg y v = 2 → ∀ e, x e ≠ 0 → (N.src e = v ∨ N.dst e = v) → y e ≠ 0 := by
    intro v hv e he hev
    exact hsub.edge_of_deg_eq (by rw [hv]; exact hdeg2 v) he hev
  have hwalk : ∀ u w, (N.selectedGraph x).Walk u w → N.deg y u = 2 → N.deg y w = 2 := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons a b c hadj _ ih =>
      intro ha
      apply ih
      obtain ⟨e, he, hends⟩ := hadj
      have hye : y e ≠ 0 := hfull a ha e he (by
        rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inl h1
        · exact Or.inr h2)
      have hb : 0 < N.deg y b := by
        rcases hends with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2 ▸ N.deg_dst_pos hye
        · exact h1 ▸ N.deg_src_pos hye
      rcases hyd b with h | h
      · omega
      · exact h
  obtain ⟨e₀, he₀⟩ : ∃ e, y e ≠ 0 := by
    rcases Classical.em (∃ e, y e ≠ 0) with h | h
    · exact h
    · exfalso
      apply hne
      funext e
      exact Classical.not_not.1 fun hn => h ⟨e, hn⟩
  have hv₀ : N.deg y (N.src e₀) = 2 := by
    have := N.deg_src_pos he₀
    rcases hyd (N.src e₀) with h | h
    · omega
    · exact h
  have hxv₀ : 0 < N.deg x (N.src e₀) := by
    have := hsub.deg_le (N.src e₀)
    omega
  -- the first vertex of `y` is joined to `s` by edges of `x`, so `s` has degree two in `y`
  obtain ⟨p⟩ := (hx.2.2.2.2 (N.src e₀) hxv₀).symm
  have := hwalk _ _ p hv₀
  omega

end

end Erdos1016.BoundaryTrace.Network

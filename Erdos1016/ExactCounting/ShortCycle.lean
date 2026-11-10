import Erdos1016.ExactCounting.Suppression
import Mathlib.Data.Sym.Sym2

set_option autoImplicit false

/-!
# A short cycle in a small multigraph of minimum degree three

Let all degrees be at least three, and let there be at most nine vertices.
Then some set of at most four edges touches at most as many vertices as it has
edges. So it contains a nonempty even set, by the pigeonhole lemma.

The proof is the Moore bound. A loop gives one edge on one vertex. Two parallel
edges give two edges on two vertices. Otherwise take a vertex `a`, three of its
neighbours, and two further neighbours of each. A coincidence among these ten
vertices gives a triangle or a four-cycle. Without a coincidence there are ten
vertices.
-/

namespace Erdos1016.ExactCounting.Multi

open Finset

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- The unordered pair of ends of an edge. -/
def pair (ends : ι → V × V) (e : ι) : Sym2 V := s((ends e).1, (ends e).2)

/-- The end of `e` that is not `x`, for an edge `e` at `x`. -/
def oth (ends : ι → V × V) (x : V) (e : ι) : V :=
  if (ends e).1 = x then (ends e).2 else (ends e).1

/-- The neighbours of `x`. -/
def nb (ends : ι → V × V) (A : Finset ι) (x : V) : Finset V :=
  (star ends A x).image (oth ends x)

omit [DecidableEq V] [DecidableEq ι] in
theorem sym2_ne {a b c d : V} (h1 : a ≠ c ∨ b ≠ d) (h2 : a ≠ d ∨ b ≠ c) :
    s(a, b) ≠ s(c, d) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨x, y⟩ | ⟨x, y⟩
  · rcases h1 with h1 | h1
    · exact h1 x
    · exact h1 y
  · rcases h2 with h2 | h2
    · exact h2 x
    · exact h2 y

omit [DecidableEq V] [DecidableEq ι] in
theorem ends_mem_of_pair {ends : ι → V × V} {e : ι} {x y : V} (h : pair ends e = s(x, y))
    (W : Finset V) (hx : x ∈ W) (hy : y ∈ W) : (ends e).1 ∈ W ∧ (ends e).2 ∈ W := by
  unfold pair at h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ hx, h2 ▸ hy⟩
  · exact ⟨h1 ▸ hy, h2 ▸ hx⟩

omit [DecidableEq ι] in
theorem pair_of_mem_star (ends : ι → V × V) (A : Finset ι) (x : V) {e : ι}
    (he : e ∈ star ends A x) : pair ends e = s(x, oth ends x e) := by
  have he' := (mem_filter.1 he).2
  unfold pair oth
  by_cases h1 : (ends e).1 = x
  · rw [if_pos h1, h1]
  · have h2 : (ends e).2 = x := he'.resolve_left h1
    rw [if_neg h1, h2]
    exact Sym2.eq_swap

omit [DecidableEq ι] in
theorem mem_nb_iff (ends : ι → V × V) (A : Finset ι)
    (hloop : ∀ e ∈ A, (ends e).1 ≠ (ends e).2) (x y : V) :
    y ∈ nb ends A x ↔ ∃ e ∈ A, pair ends e = s(x, y) := by
  constructor
  · intro hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact ⟨e, (mem_filter.1 he).1, pair_of_mem_star ends A x he⟩
  · rintro ⟨e, he, hp⟩
    have hl := hloop e he
    unfold pair at hp
    rcases Sym2.eq_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine mem_image.2 ⟨e, mem_filter.2 ⟨he, Or.inl h1⟩, ?_⟩
      unfold oth
      rw [if_pos h1, h2]
    · refine mem_image.2 ⟨e, mem_filter.2 ⟨he, Or.inr h2⟩, ?_⟩
      have hne : (ends e).1 ≠ x := fun h => hl (h.trans h2.symm)
      unfold oth
      rw [if_neg hne, h1]

omit [DecidableEq ι] in
/-- In a multigraph without loops and parallel edges, a vertex has as many
neighbours as its degree. -/
theorem card_nb (ends : ι → V × V) (A : Finset ι)
    (hloop : ∀ e ∈ A, (ends e).1 ≠ (ends e).2)
    (hpar : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → pair ends e ≠ pair ends f) (x : V) :
    (nb ends A x).card = deg ends A x := by
  have hinj : Set.InjOn (oth ends x) ↑(star ends A x) := by
    intro e he f hf h
    by_contra hne
    have h1 := hpar e (mem_filter.1 (mem_coe.1 he)).1 f (mem_filter.1 (mem_coe.1 hf)).1 hne
    rw [pair_of_mem_star ends A x (mem_coe.1 he), pair_of_mem_star ends A x (mem_coe.1 hf),
      h] at h1
    exact h1 rfl
  have hstar : (star ends A x).card = deg ends A x := by
    rw [deg_eq_sum_star, card_eq_sum_ones]
    apply sum_congr rfl
    intro e he
    have he' := (mem_filter.1 he).2
    have hl := hloop e (mem_filter.1 he).1
    unfold inc
    by_cases h1 : (ends e).1 = x
    · have h2 : (ends e).2 ≠ x := fun h => hl (h1.trans h.symm)
      rw [if_pos h1, if_neg h2]
    · have h2 : (ends e).2 = x := he'.resolve_left h1
      rw [if_neg h1, if_pos h2]
  unfold nb
  rw [card_image_of_injOn hinj, hstar]

/-- A set of at most four edges that touches at most as many vertices. -/
theorem exists_small_dense (ends : ι → V × V) (A : Finset ι) (U : Finset V)
    (hU : EndsIn ends A U) (hdeg : ∀ v ∈ U, 3 ≤ deg ends A v) (hUne : U.Nonempty)
    (hUcard : U.card ≤ 9) :
    ∃ (B : Finset ι) (W : Finset V),
      B ⊆ A ∧ B.Nonempty ∧ B.card ≤ 4 ∧ EndsIn ends B W ∧ W.card ≤ B.card := by
  by_cases hloop : ∃ e ∈ A, (ends e).1 = (ends e).2
  · obtain ⟨e, he, hl⟩ := hloop
    refine ⟨{e}, {(ends e).1}, singleton_subset_iff.2 he, singleton_nonempty e, by simp, ?_,
      by simp⟩
    intro g hg
    rw [mem_singleton] at hg
    subst hg
    exact ⟨mem_singleton_self _, by rw [← hl]; exact mem_singleton_self _⟩
  by_cases hpar : ∃ e ∈ A, ∃ f ∈ A, e ≠ f ∧ pair ends e = pair ends f
  · obtain ⟨e, he, f, hf, hne, hp⟩ := hpar
    refine ⟨{e, f}, {(ends e).1, (ends e).2}, ?_, ⟨e, by simp⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases mem_insert.1 hg with rfl | hg
      · exact he
      · rw [mem_singleton] at hg
        exact hg ▸ hf
    · rw [card_pair hne]
      norm_num
    · intro g hg
      rcases mem_insert.1 hg with rfl | hg
      · simp
      · rw [mem_singleton] at hg
        subst hg
        exact ends_mem_of_pair (x := (ends e).1) (y := (ends e).2) hp.symm _ (by simp) (by simp)
    · rw [card_pair hne]
      exact card_le_two
  push_neg at hloop hpar
  have hNbne : ∀ x y, y ∈ nb ends A x → y ≠ x := by
    intro x y hy hxy
    obtain ⟨e, he, hp⟩ := (mem_nb_iff ends A hloop x y).1 hy
    subst hxy
    unfold pair at hp
    rcases Sym2.eq_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact hloop e he (h1.trans h2.symm)
  have hNbU : ∀ x y, y ∈ nb ends A x → y ∈ U := by
    intro x y hy
    obtain ⟨e, he, hp⟩ := (mem_nb_iff ends A hloop x y).1 hy
    unfold pair at hp
    rcases Sym2.eq_iff.1 hp with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 ▸ (hU e he).2
    · exact h1 ▸ (hU e he).1
  have hNbsymm : ∀ x y, y ∈ nb ends A x → x ∈ nb ends A y := by
    intro x y hy
    obtain ⟨e, he, hp⟩ := (mem_nb_iff ends A hloop x y).1 hy
    exact (mem_nb_iff ends A hloop y x).2 ⟨e, he, hp.trans Sym2.eq_swap⟩
  have hedge : ∀ x y, y ∈ nb ends A x → ∃ e ∈ A, pair ends e = s(x, y) :=
    fun x y h => (mem_nb_iff ends A hloop x y).1 h
  obtain ⟨a, ha⟩ := hUne
  have hNba : 3 ≤ (nb ends A a).card := by
    rw [card_nb ends A hloop hpar]
    exact hdeg a ha
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hNba
  have hMcard : ∀ b ∈ T, 2 ≤ ((nb ends A b).erase a).card := by
    intro b hb
    have hbU := hNbU a b (hTsub hb)
    have haNb : a ∈ nb ends A b := hNbsymm a b (hTsub hb)
    rw [card_erase_of_mem haNb, card_nb ends A hloop hpar]
    have := hdeg b hbU
    omega
  by_cases htri : ∃ b ∈ T, ∃ c ∈ (nb ends A b).erase a, c ∈ T
  · obtain ⟨b, hb, c, hc, hcT⟩ := htri
    have hcNb : c ∈ nb ends A b := mem_of_mem_erase hc
    have hba : b ≠ a := hNbne a b (hTsub hb)
    have hca : c ≠ a := hNbne a c (hTsub hcT)
    have hcb : c ≠ b := hNbne b c hcNb
    obtain ⟨e₁, he₁, hp₁⟩ := hedge a b (hTsub hb)
    obtain ⟨e₂, he₂, hp₂⟩ := hedge a c (hTsub hcT)
    obtain ⟨e₃, he₃, hp₃⟩ := hedge b c hcNb
    have h12 : e₁ ≠ e₂ := fun h =>
      sym2_ne (Or.inr hcb.symm) (Or.inl hca.symm) (by rw [← hp₁, ← hp₂, h])
    have h13 : e₁ ≠ e₃ := fun h =>
      sym2_ne (Or.inl hba.symm) (Or.inl hca.symm) (by rw [← hp₁, ← hp₃, h])
    have h23 : e₂ ≠ e₃ := fun h =>
      sym2_ne (Or.inl hba.symm) (Or.inl hca.symm) (by rw [← hp₂, ← hp₃, h])
    have hB : ({e₁, e₂, e₃} : Finset ι).card = 3 := by
      rw [card_insert_of_not_mem (by simp [h12, h13]), card_pair h23]
    refine ⟨{e₁, e₂, e₃}, {a, b, c}, ?_, ⟨e₁, by simp⟩, by rw [hB]; norm_num, ?_, ?_⟩
    · intro g hg
      simp only [mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl | rfl <;> assumption
    · intro g hg
      simp only [mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl | rfl
      · exact ends_mem_of_pair hp₁ _ (by simp) (by simp)
      · exact ends_mem_of_pair hp₂ _ (by simp) (by simp)
      · exact ends_mem_of_pair hp₃ _ (by simp) (by simp)
    · rw [hB]
      exact card_le_three
  by_cases hquad : ∃ b ∈ T, ∃ b' ∈ T, b ≠ b' ∧
      ∃ c ∈ (nb ends A b).erase a, c ∈ (nb ends A b').erase a
  · obtain ⟨b, hb, b', hb', hbb', c, hc, hc'⟩ := hquad
    have hcNb : c ∈ nb ends A b := mem_of_mem_erase hc
    have hcNb' : c ∈ nb ends A b' := mem_of_mem_erase hc'
    have hba : b ≠ a := hNbne a b (hTsub hb)
    have hba' : b' ≠ a := hNbne a b' (hTsub hb')
    have hca : c ≠ a := (mem_erase.1 hc).1
    have hcb : c ≠ b := hNbne b c hcNb
    have hcb' : c ≠ b' := hNbne b' c hcNb'
    obtain ⟨e₁, he₁, hp₁⟩ := hedge a b (hTsub hb)
    obtain ⟨e₂, he₂, hp₂⟩ := hedge a b' (hTsub hb')
    obtain ⟨e₃, he₃, hp₃⟩ := hedge b c hcNb
    obtain ⟨e₄, he₄, hp₄⟩ := hedge b' c hcNb'
    have h12 : e₁ ≠ e₂ := fun h =>
      sym2_ne (Or.inr hbb') (Or.inl hba'.symm) (by rw [← hp₁, ← hp₂, h])
    have h13 : e₁ ≠ e₃ := fun h =>
      sym2_ne (Or.inl hba.symm) (Or.inl hca.symm) (by rw [← hp₁, ← hp₃, h])
    have h14 : e₁ ≠ e₄ := fun h =>
      sym2_ne (Or.inl hba'.symm) (Or.inl hca.symm) (by rw [← hp₁, ← hp₄, h])
    have h23 : e₂ ≠ e₃ := fun h =>
      sym2_ne (Or.inl hba.symm) (Or.inl hca.symm) (by rw [← hp₂, ← hp₃, h])
    have h24 : e₂ ≠ e₄ := fun h =>
      sym2_ne (Or.inl hba'.symm) (Or.inl hca.symm) (by rw [← hp₂, ← hp₄, h])
    have h34 : e₃ ≠ e₄ := fun h =>
      sym2_ne (Or.inl hbb') (Or.inl hcb.symm) (by rw [← hp₃, ← hp₄, h])
    have hB : ({e₁, e₂, e₃, e₄} : Finset ι).card = 4 := by
      rw [card_insert_of_not_mem (by simp [h12, h13, h14]),
        card_insert_of_not_mem (by simp [h23, h24]), card_pair h34]
    refine ⟨{e₁, e₂, e₃, e₄}, {a, b, b', c}, ?_, ⟨e₁, by simp⟩, by rw [hB], ?_, ?_⟩
    · intro g hg
      simp only [mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> assumption
    · intro g hg
      simp only [mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ends_mem_of_pair hp₁ _ (by simp) (by simp)
      · exact ends_mem_of_pair hp₂ _ (by simp) (by simp)
      · exact ends_mem_of_pair hp₃ _ (by simp) (by simp)
      · exact ends_mem_of_pair hp₄ _ (by simp) (by simp)
    · rw [hB]
      exact card_le_four
  push_neg at htri hquad
  exfalso
  have haT : a ∉ T := fun h => hNbne a a (hTsub h) rfl
  have hdisj1 : Disjoint T (T.biUnion fun b => (nb ends A b).erase a) := by
    rw [disjoint_left]
    intro c hcT hc
    obtain ⟨b, hb, hcM⟩ := mem_biUnion.1 hc
    exact htri b hb c hcM hcT
  have hpw : (↑T : Set V).PairwiseDisjoint fun b => (nb ends A b).erase a := by
    intro b hb b' hb' hne
    show Disjoint ((nb ends A b).erase a) ((nb ends A b').erase a)
    rw [disjoint_left]
    intro c hc hc'
    exact hquad b (mem_coe.1 hb) b' (mem_coe.1 hb') hne c hc hc'
  have hbi : (T.biUnion fun b => (nb ends A b).erase a).card =
      ∑ b ∈ T, ((nb ends A b).erase a).card := card_biUnion hpw
  have hsum : 6 ≤ ∑ b ∈ T, ((nb ends A b).erase a).card := by
    calc 6 = ∑ _b ∈ T, 2 := by simp [hTcard]
      _ ≤ ∑ b ∈ T, ((nb ends A b).erase a).card := sum_le_sum hMcard
  have haU : a ∉ T ∪ T.biUnion fun b => (nb ends A b).erase a := by
    intro h
    rcases mem_union.1 h with h | h
    · exact haT h
    · obtain ⟨b, _, hb⟩ := mem_biUnion.1 h
      exact (mem_erase.1 hb).1 rfl
  have hsubU : insert a (T ∪ T.biUnion fun b => (nb ends A b).erase a) ⊆ U := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact ha
    · rcases mem_union.1 hx with h | h
      · exact hNbU a x (hTsub h)
      · obtain ⟨b, _, hb⟩ := mem_biUnion.1 h
        exact hNbU b x (mem_of_mem_erase hb)
  have hcard := card_le_card hsubU
  rw [card_insert_of_not_mem haU, card_union_of_disjoint hdisj1, hbi, hTcard] at hcard
  omega

end Erdos1016.ExactCounting.Multi

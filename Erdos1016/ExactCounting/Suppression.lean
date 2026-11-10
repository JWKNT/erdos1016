import Erdos1016.ExactCounting.Multigraph

set_option autoImplicit false

/-!
# Intersecting edge sets and the suppression of a vertex

An edge set `A` is intersecting if any two nonempty even subsets of `A` share
an edge. This is the statement that the multigraph has no two edge-disjoint
cycles, in the language of even sets.

The property passes to subsets. It also survives the suppression of a vertex
`v` of degree two: the two edges at `v` are replaced by one edge between their
other ends. This file proves both facts, and the facts about the edges at a
vertex that the induction needs.
-/

namespace Erdos1016.ExactCounting.Multi

open Finset

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- Any two nonempty even subsets of `A` share an edge. -/
def Intersecting (ends : ι → V × V) (A : Finset ι) : Prop :=
  ∀ X Y, X ⊆ A → Y ⊆ A → X.Nonempty → Y.Nonempty → MEven ends X → MEven ends Y →
    (X ∩ Y).Nonempty

theorem Intersecting.mono {ends : ι → V × V} {A A' : Finset ι} (h : A' ⊆ A)
    (hI : Intersecting ends A) : Intersecting ends A' :=
  fun X Y hX hY => hI X Y (hX.trans h) (hY.trans h)

/-- The edges of `A` at the vertex `v`. -/
def star (ends : ι → V × V) (A : Finset ι) (v : V) : Finset ι :=
  A.filter fun e => (ends e).1 = v ∨ (ends e).2 = v

omit [DecidableEq ι] in
theorem inc_pos_iff (ends : ι → V × V) (e : ι) (v : V) :
    0 < inc ends e v ↔ ((ends e).1 = v ∨ (ends e).2 = v) := by
  unfold inc
  by_cases h1 : (ends e).1 = v <;> by_cases h2 : (ends e).2 = v <;> simp [h1, h2]

omit [DecidableEq ι] in
theorem deg_eq_sum_star (ends : ι → V × V) (A : Finset ι) (v : V) :
    deg ends A v = ∑ e ∈ star ends A v, inc ends e v := by
  unfold deg star
  rw [Finset.sum_filter_of_ne]
  intro e _ he
  exact (inc_pos_iff ends e v).1 (Nat.pos_of_ne_zero he)

omit [DecidableEq ι] in
theorem card_star_le_deg (ends : ι → V × V) (A : Finset ι) (v : V) :
    (star ends A v).card ≤ deg ends A v := by
  rw [deg_eq_sum_star, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  exact (inc_pos_iff ends e v).2 (Finset.mem_filter.1 he).2

/-- The edges that do not touch `v` have their ends in `U` without `v`. -/
theorem endsIn_sdiff_star {ends : ι → V × V} {A : Finset ι} {U : Finset V}
    (h : EndsIn ends A U) (v : V) : EndsIn ends (A \ star ends A v) (U.erase v) := by
  intro e he
  rw [Finset.mem_sdiff] at he
  have hnot : ¬((ends e).1 = v ∨ (ends e).2 = v) := fun h' =>
    he.2 (Finset.mem_filter.2 ⟨he.1, h'⟩)
  push_neg at hnot
  exact ⟨Finset.mem_erase.2 ⟨hnot.1, (h e he.1).1⟩, Finset.mem_erase.2 ⟨hnot.2, (h e he.1).2⟩⟩

omit [DecidableEq ι] in
/-- An edge with exactly one end at `v` joins `v` to another vertex `u`. -/
theorem inc_of_inc_eq_one (ends : ι → V × V) (e : ι) (v : V) (h : inc ends e v = 1) :
    ∃ u, u ≠ v ∧ (u = (ends e).1 ∨ u = (ends e).2) ∧
      ∀ x, inc ends e x = (if v = x then 1 else 0) + (if u = x then 1 else 0) := by
  unfold inc at h ⊢
  by_cases h1 : (ends e).1 = v
  · by_cases h2 : (ends e).2 = v
    · simp [h1, h2] at h
    · refine ⟨(ends e).2, h2, Or.inr rfl, fun x => ?_⟩
      rw [h1]
  · by_cases h2 : (ends e).2 = v
    · refine ⟨(ends e).1, h1, Or.inl rfl, fun x => ?_⟩
      rw [h2, add_comm]
    · simp [h1, h2] at h

/-- Suppression of a vertex of degree two keeps the edge set intersecting. The
edges `e` and `f` join `v` to `u` and to `w`. The new edge `e` joins `u` to `w`,
and `f` is removed. -/
theorem intersecting_suppress (ends : ι → V × V) (A : Finset ι) (v u w : V) (e f : ι)
    (hf : f ∈ A)
    (hince : ∀ x, inc ends e x = (if v = x then 1 else 0) + (if u = x then 1 else 0))
    (hincf : ∀ x, inc ends f x = (if v = x then 1 else 0) + (if w = x then 1 else 0))
    (hI : Intersecting ends A) :
    Intersecting (Function.update ends e (u, w)) (A.erase f) := by
  intro X' Y' hX' hY' hXne hYne hXev hYev
  have lift : ∀ Z : Finset ι, Z ⊆ A.erase f →
      MEven (Function.update ends e (u, w)) Z →
      MEven ends (if e ∈ Z then insert f Z else Z) := by
    intro Z hZ hZev x
    have hfZ : f ∉ Z := fun h => (Finset.mem_erase.1 (hZ h)).1 rfl
    by_cases heZ : e ∈ Z
    · rw [if_pos heZ, deg_insert ends hfZ]
      have h1 : deg ends Z x = inc ends e x + deg ends (Z.erase e) x :=
        (Finset.add_sum_erase Z _ heZ).symm
      have h2 : deg (Function.update ends e (u, w)) Z x =
          inc (Function.update ends e (u, w)) e x +
            deg (Function.update ends e (u, w)) (Z.erase e) x :=
        (Finset.add_sum_erase Z _ heZ).symm
      have h3 : deg (Function.update ends e (u, w)) (Z.erase e) x =
          deg ends (Z.erase e) x := by
        apply Finset.sum_congr rfl
        intro g hg
        have hge : g ≠ e := (Finset.mem_erase.1 hg).1
        simp [inc, Function.update_of_ne hge]
      have h4 : inc (Function.update ends e (u, w)) e x =
          (if u = x then 1 else 0) + (if w = x then 1 else 0) := by
        simp [inc]
      have h5 := hZev x
      rw [h2, h3, h4] at h5
      rw [hincf x, h1, hince x]
      split_ifs at h5 ⊢ <;> omega
    · rw [if_neg heZ]
      have h1 : deg ends Z x = deg (Function.update ends e (u, w)) Z x := by
        apply Finset.sum_congr rfl
        intro g hg
        have hge : g ≠ e := fun h => heZ (h ▸ hg)
        simp [inc, Function.update_of_ne hge]
      rw [h1]
      exact hZev x
  have liftsub : ∀ Z : Finset ι, Z ⊆ A.erase f →
      (if e ∈ Z then insert f Z else Z) ⊆ A := by
    intro Z hZ g hg
    by_cases h : e ∈ Z
    · rw [if_pos h] at hg
      rcases Finset.mem_insert.1 hg with rfl | hg'
      · exact hf
      · exact Finset.mem_of_mem_erase (hZ hg')
    · rw [if_neg h] at hg
      exact Finset.mem_of_mem_erase (hZ hg)
  have liftne : ∀ Z : Finset ι, Z.Nonempty → (if e ∈ Z then insert f Z else Z).Nonempty := by
    intro Z hZ
    by_cases h : e ∈ Z
    · rw [if_pos h]
      exact Finset.insert_nonempty _ _
    · rw [if_neg h]
      exact hZ
  have liftmem : ∀ Z : Finset ι, Z ⊆ A.erase f → ∀ g,
      g ∈ (if e ∈ Z then insert f Z else Z) → (g = f ∧ e ∈ Z) ∨ g ∈ Z := by
    intro Z _ g hg
    by_cases h : e ∈ Z
    · rw [if_pos h] at hg
      rcases Finset.mem_insert.1 hg with rfl | hg'
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr hg'
    · rw [if_neg h] at hg
      exact Or.inr hg
  obtain ⟨g, hg⟩ := hI _ _ (liftsub X' hX') (liftsub Y' hY') (liftne X' hXne)
    (liftne Y' hYne) (lift X' hX' hXev) (lift Y' hY' hYev)
  rw [Finset.mem_inter] at hg
  have hfX : f ∉ X' := fun h => (Finset.mem_erase.1 (hX' h)).1 rfl
  have hfY : f ∉ Y' := fun h => (Finset.mem_erase.1 (hY' h)).1 rfl
  rcases liftmem X' hX' g hg.1 with ⟨hgf, heX⟩ | hgX
  · rcases liftmem Y' hY' g hg.2 with ⟨_, heY⟩ | hgY
    · exact ⟨e, Finset.mem_inter.2 ⟨heX, heY⟩⟩
    · exact absurd (hgf ▸ hgY) hfY
  · rcases liftmem Y' hY' g hg.2 with ⟨hgf, _⟩ | hgY
    · exact absurd (hgf ▸ hgX) hfX
    · exact ⟨g, Finset.mem_inter.2 ⟨hgX, hgY⟩⟩

end Erdos1016.ExactCounting.Multi

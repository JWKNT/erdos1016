import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.SymmDiff
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Edge sets of a multigraph

A multigraph is given by a map `ends` from edge labels to ordered pairs of
vertices. Loops and parallel edges are allowed. An edge set is a finite set of
labels. The degree of a vertex counts a loop twice.

This file proves three facts. The degree is additive modulo two for the
symmetric difference. The degrees of an edge set sum to twice its size. If an
edge set has at least as many edges as it has vertices, then it contains a
nonempty even set.
-/

namespace Erdos1016.ExactCounting.Multi

open Finset

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- The number of ends of the edge `e` at the vertex `v`. -/
def inc (ends : ι → V × V) (e : ι) (v : V) : ℕ :=
  (if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0)

/-- The degree of `v` in the edge set `X`. A loop counts twice. -/
def deg (ends : ι → V × V) (X : Finset ι) (v : V) : ℕ := ∑ e ∈ X, inc ends e v

/-- Every vertex has even degree in `X`. -/
def MEven (ends : ι → V × V) (X : Finset ι) : Prop := ∀ v, deg ends X v % 2 = 0

/-- All ends of the edges of `X` lie in `U`. -/
def EndsIn (ends : ι → V × V) (X : Finset ι) (U : Finset V) : Prop :=
  ∀ e ∈ X, (ends e).1 ∈ U ∧ (ends e).2 ∈ U

theorem deg_union_of_disjoint (ends : ι → V × V) {X Y : Finset ι} (h : Disjoint X Y) (v : V) :
    deg ends (X ∪ Y) v = deg ends X v + deg ends Y v :=
  Finset.sum_union h

theorem deg_insert (ends : ι → V × V) {X : Finset ι} {e : ι} (he : e ∉ X) (v : V) :
    deg ends (insert e X) v = inc ends e v + deg ends X v :=
  Finset.sum_insert he

/-- The degree is additive modulo two for the symmetric difference. -/
theorem deg_symmDiff (ends : ι → V × V) (X Y : Finset ι) (v : V) :
    deg ends (symmDiff X Y) v + 2 * deg ends (X ∩ Y) v = deg ends X v + deg ends Y v := by
  have hX : deg ends X v = deg ends (X \ Y) v + deg ends (X ∩ Y) v := by
    conv_lhs => rw [← Finset.sdiff_union_inter X Y]
    exact deg_union_of_disjoint ends (Finset.disjoint_sdiff_inter X Y) v
  have hY : deg ends Y v = deg ends (Y \ X) v + deg ends (X ∩ Y) v := by
    conv_lhs => rw [← Finset.sdiff_union_inter Y X]
    rw [Finset.inter_comm Y X]
    exact deg_union_of_disjoint ends
      (by rw [Finset.inter_comm X Y]; exact Finset.disjoint_sdiff_inter Y X) v
  have hD : deg ends (symmDiff X Y) v = deg ends (X \ Y) v + deg ends (Y \ X) v := by
    have : symmDiff X Y = (X \ Y) ∪ (Y \ X) := rfl
    rw [this]
    exact deg_union_of_disjoint ends disjoint_sdiff_sdiff v
  omega

theorem MEven.symmDiff {ends : ι → V × V} {X Y : Finset ι} (hX : MEven ends X)
    (hY : MEven ends Y) : MEven ends (symmDiff X Y) := by
  intro v
  have h := deg_symmDiff ends X Y v
  have h1 := hX v
  have h2 := hY v
  omega

omit [DecidableEq ι] in
/-- An edge with both ends in `U` has exactly two ends in `U`. -/
theorem sum_inc (ends : ι → V × V) (U : Finset V) (e : ι)
    (h : (ends e).1 ∈ U ∧ (ends e).2 ∈ U) : ∑ v ∈ U, inc ends e v = 2 := by
  unfold inc
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos h.1, if_pos h.2]

omit [DecidableEq ι] in
/-- The degrees of an edge set sum to twice its size. -/
theorem sum_deg (ends : ι → V × V) (X : Finset ι) (U : Finset V) (h : EndsIn ends X U) :
    ∑ v ∈ U, deg ends X v = 2 * X.card := by
  unfold deg
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun e he => sum_inc ends U e (h e he))]
  simp [mul_comm]

omit [DecidableEq ι] in
/-- A vertex outside `U` has degree zero. -/
theorem deg_eq_zero_of_not_mem (ends : ι → V × V) (X : Finset ι) (U : Finset V)
    (h : EndsIn ends X U) {v : V} (hv : v ∉ U) : deg ends X v = 0 := by
  unfold deg
  apply Finset.sum_eq_zero
  intro e he
  have h1 : (ends e).1 ≠ v := fun h' => hv (h' ▸ (h e he).1)
  have h2 : (ends e).2 ≠ v := fun h' => hv (h' ▸ (h e he).2)
  simp [inc, h1, h2]

/-- If an edge set has at least as many edges as vertices, it contains a
nonempty even set. -/
theorem exists_even_subset (ends : ι → V × V) (B : Finset ι) (U : Finset V)
    (hU : EndsIn ends B U) (hB : B.Nonempty) (hcard : U.card ≤ B.card) :
    ∃ Y, Y ⊆ B ∧ Y.Nonempty ∧ MEven ends Y := by
  obtain ⟨e₀, he₀⟩ := hB
  have hu₀ : (ends e₀).1 ∈ U := (hU e₀ he₀).1
  set u₀ := (ends e₀).1 with hu₀def
  have hlt : (U.erase u₀).powerset.card < B.powerset.card := by
    rw [card_powerset, card_powerset, card_erase_of_mem hu₀]
    have hpos : 0 < U.card := Finset.card_pos.2 ⟨u₀, hu₀⟩
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨X₁, hX₁, X₂, hX₂, hne, hEq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun X => (U.erase u₀).filter fun v => deg ends X v % 2 = 1)
      (fun X _ => mem_powerset.2 (filter_subset _ _))
  have hX₁' := mem_powerset.1 hX₁
  have hX₂' := mem_powerset.1 hX₂
  have hYB : symmDiff X₁ X₂ ⊆ B := by
    intro e he
    rcases mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hX₁' h
    · exact hX₂' h
  have hYU : EndsIn ends (symmDiff X₁ X₂) U := fun e he => hU e (hYB he)
  have hrest : ∀ v ∈ U.erase u₀, deg ends (symmDiff X₁ X₂) v % 2 = 0 := by
    intro v hv
    have h1 : v ∈ (U.erase u₀).filter (fun v => deg ends X₁ v % 2 = 1) ↔
        v ∈ (U.erase u₀).filter (fun v => deg ends X₂ v % 2 = 1) := by
      have hEq' : ((U.erase u₀).filter fun v => deg ends X₁ v % 2 = 1) =
          (U.erase u₀).filter fun v => deg ends X₂ v % 2 = 1 := hEq
      rw [hEq']
    simp only [mem_filter, hv, true_and] at h1
    have h2 := deg_symmDiff ends X₁ X₂ v
    omega
  refine ⟨symmDiff X₁ X₂, hYB, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (symmDiff_eq_bot.1 h)
  · intro v
    by_cases hvU : v ∈ U
    · by_cases hv : v = u₀
      · subst hv
        have hsum := sum_deg ends (symmDiff X₁ X₂) U hYU
        rw [← Finset.add_sum_erase U _ hu₀] at hsum
        have hmod : (∑ w ∈ U.erase u₀, deg ends (symmDiff X₁ X₂) w) % 2 = 0 := by
          rw [Finset.sum_nat_mod, Finset.sum_eq_zero hrest]
          rfl
        omega
      · exact hrest v (mem_erase.2 ⟨hv, hvU⟩)
    · rw [deg_eq_zero_of_not_mem ends _ U hYU hvU]

end Erdos1016.ExactCounting.Multi

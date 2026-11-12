import Erdos1016.ExactMaximum.NetCut
import Erdos1016.Graph.ConnectedRegionBoundary
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A cycle crosses each intermediate level twice

Cuts count physical edge labels, including parallel copies.
Evenness and connected selected support give at least two crossings per level.
A one-Lipschitz integer level function gives disjoint crossing sets.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.CycleLayerSpan
open BoundaryTrace BoundaryTrace.Network

local instance layerSpanDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (level : V → ℤ)

/-- Every intermediate level has two selected physical crossing labels. -/
theorem two_le_crossing_card (x : N.Word) (hx : N.IsCycleWord x)
    (u v : V) (hu : 0 < N.deg x u) (hv : 0 < N.deg x v)
    (j : ℤ) (huj : level u ≤ j) (hjv : j < level v) :
    2 ≤ (N.crossSet (fun w => level w ≤ j) x).card := by
  obtain ⟨p⟩ := hx.2.2 u v hu hv
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Proof.ConnectedRegionBoundary.Walk.exists_adj_boundary (S := {w | level w ≤ j})
      p huj (not_le_of_gt hjv)
  obtain ⟨e, he, hend⟩ := hab
  have hc : N.crosses (fun w => level w ≤ j) e := by
    unfold crosses
    rcases hend with h | h
    · rw [h.1, h.2]
      exact fun hh => hb (hh.mp ha)
    · rw [h.1, h.2]
      exact fun hh => hb (hh.mpr ha)
  have hpos : 0 < (N.crossSet (fun w => level w ≤ j) x).card :=
    Finset.card_pos.mpr ⟨e, (N.mem_crossSet).mpr ⟨hc, he⟩⟩
  obtain ⟨k, hk⟩ := N.even_card_crossSet (fun w => level w ≤ j) hx.boundary_eq_zero
  omega

omit [Fintype V] [Fintype E] in
/-- An edge with level difference at most one crosses only one threshold. -/
theorem crossing_level_unique (e : E)
    (he : level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (i j : ℤ) (hi : N.crosses (fun w => level w ≤ i) e)
    (hj : N.crosses (fun w => level w ≤ j) e) : i = j := by
  unfold crosses at hi hj
  by_cases hsi : level (N.src e) ≤ i <;>
    by_cases hti : level (N.dst e) ≤ i <;>
    by_cases hsj : level (N.src e) ≤ j <;>
    by_cases htj : level (N.dst e) ≤ j <;>
    simp only [hsi, hti, hsj, htj, iff_self, not_true_eq_false] at hi hj <;> omega

omit [Fintype V] in
/-- Different thresholds use disjoint selected physical edges. -/
theorem crossing_disjoint (x : N.Word)
    (hlevel : ∀ e, x e ≠ 0 → level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (i j : ℤ) (hij : i ≠ j) :
    Disjoint (N.crossSet (fun w => level w ≤ i) x)
      (N.crossSet (fun w => level w ≤ j) x) := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  have hi' := N.mem_crossSet.mp hi
  have hj' := N.mem_crossSet.mp hj
  exact hij (crossing_level_unique N level e (hlevel e hi'.2) i j hi'.1 hj'.1)

/-- The physical support of a cycle is at least twice the separation of any two levels. -/
theorem twice_level_difference_le_support (x : N.Word) (hx : N.IsCycleWord x)
    (hlevel : ∀ e, x e ≠ 0 → level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (u v : V) (hu : 0 < N.deg x u) (hv : 0 < N.deg x v) :
    2 * (level v - level u).toNat ≤ (Finset.univ.filter fun e => x e ≠ 0).card := by
  let I := Finset.Ico (level u) (level v)
  let F : ℤ → Finset E := fun j => N.crossSet (fun w => level w ≤ j) x
  have hpair : (↑I : Set ℤ).PairwiseDisjoint F := by
    intro i _ j _ hij
    exact crossing_disjoint N level x hlevel i j hij
  have hsub : I.biUnion F ⊆ Finset.univ.filter (fun e => x e ≠ 0) := by
    intro e he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (N.mem_crossSet.mp hj).2⟩
  calc
    2 * (level v - level u).toNat = ∑ _j ∈ I, 2 := by
      simp [I, Int.card_Ico, Nat.mul_comm]
    _ ≤ ∑ j ∈ I, (F j).card := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      exact two_le_crossing_card N level x hx u v hu hv j hj'.1 hj'.2
    _ = (I.biUnion F).card := (Finset.card_biUnion hpair).symm
    _ ≤ _ := Finset.card_le_card hsub

end Erdos1016.ExactMaximumSupport.CycleLayerSpan

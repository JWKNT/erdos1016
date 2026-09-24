import Erdos1016.Cycles.Geometry.ContactGraph
import Erdos1016.Nonbacktracking.Walks.WeightedPrefixes

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.WalkWindowPositions

open Erdos1016.Proof.CyclicRunCollisionGeometry

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Positions in a simple-walk window are distinct. -/
theorem window_positions_injective
    {V : Type*} {J : SimpleGraph V} {a b : V}
    (p : J.Walk a b) (hp : p.IsPath) (start m : ℕ) (hend : start + m ≤ p.length + 1) :
    Function.Injective (fun i : Fin m => p.getVert (start + i.val)) := by
  intro i j hij
  have hi : start + i.val ≤ p.length := by omega
  have hj : start + j.val ≤ p.length := by omega
  have h := hp.getVert_injOn hi hj hij
  apply Fin.ext
  omega

private theorem take_support_subset
    {V : Type*} {J : SimpleGraph V} {a b : V} (p : J.Walk a b) (i : ℕ) :
    (p.take i).support ⊆ p.support := by
  have h := take_append_drop_at_index p i
  intro z hz
  rw [← h, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hz

private theorem drop_support_subset
    {V : Type*} {J : SimpleGraph V} {a b : V} (p : J.Walk a b) (i : ℕ) :
    (p.drop i).support ⊆ p.support := by
  have h := take_append_drop_at_index p i
  intro z hz
  rw [← h, SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr hz

/-- Two ordered positions of any walk are joined by its corresponding
segment, with exactly the difference in their indices. -/
theorem window_segment
    {V : Type*} {J : SimpleGraph V} {a b : V}
    (p : J.Walk a b) (start m : ℕ) (hend : start + m ≤ p.length + 1)
    (i j : Fin m) (hij : i.val < j.val) :
    ∃ q : J.Walk (p.getVert (start + i.val)) (p.getVert (start + j.val)),
      q.length = j.val - i.val ∧ q.support ⊆ p.support := by
  let q₀ := (p.drop (start + i.val)).take (j.val - i.val)
  have hlast : (p.drop (start + i.val)).getVert (j.val - i.val) =
      p.getVert (start + j.val) := by
    rw [getVert_drop_at_index]
    congr 1
    omega
  let q := q₀.copy rfl hlast
  have hlen : q.length = j.val - i.val := by
    simp only [q, SimpleGraph.Walk.length_copy, q₀, take_length_at_index,
      drop_length_at_index]
    omega
  have hsup : q.support ⊆ p.support := by
    simp only [q, SimpleGraph.Walk.support_copy, q₀]
    exact (take_support_subset (p.drop (start + i.val)) _).trans (drop_support_subset p _)
  exact ⟨q, hlen, hsup⟩

/-- Every finite predicate count loses at most one position on deleting the
last index. This is the final extra position in the conditional suffix bound. -/
theorem filter_fin_card_le_pred_add_one
    (m : ℕ) (P : Fin (m + 1) → Prop) :
    (Finset.univ.filter P).card ≤
      (Finset.univ.filter (fun i : Fin m => P i.castSucc)).card + 1 := by
  have hsum : (Finset.univ.filter P).card =
      ∑ i : Fin (m + 1), if P i then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsum' : (Finset.univ.filter (fun i : Fin m => P i.castSucc)).card =
      ∑ i : Fin m, if P i.castSucc then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum, hsum', Fin.sum_univ_castSucc]
  split_ifs <;> omega

/-- Predicate counts on a list are exactly the counts on its indexed
positions. -/
theorem countP_eq_filter_positions {V : Type*} (l : List V) (P : V → Prop) :
    l.countP (fun v => decide (P v)) =
      (Finset.univ.filter (fun i : Fin l.length => P l[i.val])).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ih]
    have hsum : (Finset.univ.filter (fun i : Fin (a :: l).length => P (a :: l)[i.val])).card =
        ∑ i : Fin (l.length + 1), if P (a :: l)[i.val] then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rfl
    rw [hsum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [decide_eq_true_eq, Nat.add_comm]

theorem countP_bool_eq_filter_positions {V : Type*} (l : List V) (P : V → Bool) :
    l.countP P = (Finset.univ.filter (fun i : Fin l.length => P l[i.val])).card := by
  have h := countP_eq_filter_positions l (fun v => P v = true)
  convert h using 1
  · congr 1
    funext v
    cases hPv : P v <;> simp [hPv]
  · congr 1
    ext i
    simp

/-- Internal positions of a walk are the positive indices before its end. -/
theorem internal_get_eq_getVert
    {V : Type*} {J : SimpleGraph V} {a b : V} (p : J.Walk a b)
    (i : Fin p.support.tail.dropLast.length) :
    p.support.tail.dropLast[i.val] = p.getVert (i.val + 1) := by
  have hi : i.val < p.support.tail.length := by
    have := i.isLt
    simp only [List.length_dropLast] at this
    omega
  have h := support_tail_get_eq_getVert p ⟨i.val, hi⟩
  simpa only [List.getElem_dropLast, List.get_eq_getElem] using h

/-- For a run, the heads contributing internal weights are precisely the
internal vertices of its underlying walk. -/
theorem run_internal_heads_eq
    (G : PhysicalGraph) (k : ℕ) {d e : Erdos1016.Nonbacktracking.Dart G}
    (r : Erdos1016.Nonbacktracking.Run G k d e) :
    (Erdos1016.Nonbacktracking.runDarts G k r).dropLast.map
      (Erdos1016.Nonbacktracking.head G) =
      (Erdos1016.Nonbacktracking.runWalk G k r).support.tail.dropLast := by
  rw [List.map_dropLast, ← Erdos1016.Nonbacktracking.walkDarts_runWalk]
  rw [Erdos1016.Proof.WeightedWalkPrefix.walkDarts_map_head]

end Erdos1016.Proof.WalkWindowPositions

end

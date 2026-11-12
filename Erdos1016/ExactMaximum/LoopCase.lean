import Erdos1016.ExactMaximum.Cycles
import Erdos1016.ExactMaximum.HorakKim

set_option autoImplicit false

/-!
# Case 1 of the exact maximum: a multigraph with a loop

Let `e` be a loop of a multigraph of cycle rank `r`. The only cycle through `e` is `e` itself.
Every other cycle is an element of the cycle space that avoids `e`, and exactly half of the
cycle space avoids `e`. So the multigraph has at most `2^(r-1)` cycles.

This is Case 1 in Section 9 of the paper "The maximum number of cycles in a graph of large
rank".
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.FiniteMultiGraph

variable {G : FiniteMultiGraph}

/-- The word of a loop is in the cycle space. -/
theorem boundary_single_of_loop {e : G.Edge} (he : G.src e = G.dst e) :
    G.boundary (Pi.single e (1 : F₂)) = 0 := by
  classical
  funext v
  rw [boundary_apply_eq_selectedDegree, G.selectedDegree_eq_sum_endpoints, Nat.cast_sum]
  rw [Finset.sum_eq_single e]
  · rw [← he]
    by_cases h : G.src e = v
    · simp [h]
      rfl
    · simp [h]
  · intro f _ hf
    simp [Pi.single_eq_of_ne hf]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- A cycle through a loop is the loop. -/
theorem IsCycleWord.eq_single_of_loop {x : G.EdgeWord} (hx : G.IsCycleWord x) {e : G.Edge}
    (he : G.src e = G.dst e) (hxe : x e ≠ 0) : x = Pi.single e (1 : F₂) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, G.src e = v := ⟨_, rfl⟩
  have hv' : G.dst e = v := he ▸ hv
  -- every other selected edge avoids `v`
  have hterm : ∀ f, f ≠ e → x f ≠ 0 → G.src f ≠ v ∧ G.dst f ≠ v := by
    intro f hfe hxf
    have hdeg := hx.2.1 v
    rw [G.selectedDegree_eq_sum_endpoints] at hdeg
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ e)] at hdeg
    rw [if_pos hxe, if_pos hv, if_pos hv'] at hdeg
    have hrest : ∑ g ∈ Finset.univ.erase e, (if x g ≠ 0 then
        (if G.src g = v then 1 else 0) + (if G.dst g = v then 1 else 0) else 0) = 0 := by
      rcases hdeg with h | h <;> omega
    have hf0 := (Finset.sum_eq_zero_iff.1 hrest) f (Finset.mem_erase.2 ⟨hfe, Finset.mem_univ f⟩)
    rw [if_pos hxf] at hf0
    constructor
    · intro h
      rw [if_pos h] at hf0
      omega
    · intro h
      rw [if_pos h] at hf0
      omega
  -- `v` has no neighbour among the selected edges
  have hno : ∀ w, ¬ (G.selectedGraph x).Adj v w := by
    rintro w ⟨hvw, f, hxf, hf⟩
    by_cases hfe : f = e
    · rw [hfe] at hf
      rcases hf with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hvw (hv'.symm.trans h2)
      · exact hvw (hv.symm.trans h1)
    · have h := hterm f hfe hxf
      rcases hf with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h.1 h1
      · exact h.2 h2
  -- so every selected edge is `e`
  have hall : ∀ f, x f ≠ 0 → f = e := by
    intro f hxf
    by_cases hfe : f = e
    · exact hfe
    · exfalso
      have hpos : 0 < G.selectedDegree x (G.src f) := selectedDegree_src_pos hxf
      have hposv : 0 < G.selectedDegree x v := hv ▸ selectedDegree_src_pos hxe
      have hreach := hx.2.2 v (G.src f) hposv hpos
      have hsrc : G.src f = v := by
        obtain ⟨p⟩ := hreach
        cases p with
        | nil => rfl
        | cons h _ => exact absurd h (hno _)
      exact (hterm f hfe hxf).1 hsrc
  funext f
  by_cases hfe : f = e
  · rw [hfe, Pi.single_eq_same]
    rcases f2_eq_zero_or_one (x e) with h | h
    · exact absurd h hxe
    · exact h
  · rw [Pi.single_eq_of_ne hfe]
    exact Classical.not_not.1 fun h => hfe (hall f h)

/-- Exactly half of the cycle space avoids a given loop. -/
theorem two_mul_card_cycleSpace_avoiding_loop {e : G.Edge} (he : G.src e = G.dst e) :
    2 * Nat.card {y : G.CycleSpace // y.1 e = 0} = 2 ^ G.cycleRank := by
  classical
  let l : G.CycleSpace := ⟨Pi.single e 1, LinearMap.mem_ker.2 (boundary_single_of_loop he)⟩
  have hl : l.1 e = 1 := by simp [l]
  have hadd : ∀ y : G.CycleSpace, (y + l).1 e = y.1 e + 1 := by
    intro y
    show y.1 e + l.1 e = y.1 e + 1
    rw [hl]
  have hll : ∀ y : G.CycleSpace, y + l + l = y := by
    intro y
    apply Subtype.ext
    funext f
    show y.1 f + l.1 f + l.1 f = y.1 f
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  let φ : {y : G.CycleSpace // y.1 e = 0} ≃ {y : G.CycleSpace // ¬ y.1 e = 0} :=
    { toFun := fun y => ⟨y.1 + l, by rw [hadd, y.2]; decide⟩
      invFun := fun y => ⟨y.1 + l, by
        rw [hadd]
        rcases f2_eq_zero_or_one (y.1.1 e) with h | h
        · exact absurd h y.2
        · rw [h]; rfl⟩
      left_inv := fun y => Subtype.ext (hll y.1)
      right_inv := fun y => Subtype.ext (hll y.1) }
  have h1 : Fintype.card {y : G.CycleSpace // y.1 e = 0} =
      Fintype.card {y : G.CycleSpace // ¬ y.1 e = 0} := Fintype.card_congr φ
  have h2 := Fintype.card_subtype_compl (fun y : G.CycleSpace => y.1 e = 0)
  have h3 := Fintype.card_subtype_le (fun y : G.CycleSpace => y.1 e = 0)
  have h4 : Fintype.card G.CycleSpace = 2 ^ G.cycleRank := cycleSpace_card G
  rw [Nat.card_eq_fintype_card]
  omega

/-- A multigraph with a loop has at most `2^(r-1)` cycles, where `r` is its cycle rank. -/
theorem numCycles_le_of_loop (G : FiniteMultiGraph) (h : G.HasLoop) :
    G.numCycles ≤ 2 ^ (G.cycleRank - 1) := by
  classical
  obtain ⟨e, he⟩ := h
  -- map a cycle that avoids `e` to itself, and the cycle `e` to zero
  let ψ : {x : G.EdgeWord // G.IsCycleWord x} → {y : G.CycleSpace // y.1 e = 0} := fun x =>
    if hx : x.1 e = 0 then ⟨x.2.toCycleSpace, hx⟩ else ⟨0, rfl⟩
  have hψ : Function.Injective ψ := by
    intro a b hab
    by_cases ha : a.1 e = 0 <;> by_cases hb : b.1 e = 0
    · simp only [ψ, ha, hb, dif_pos] at hab
      have h1 := congrArg (fun y : {y : G.CycleSpace // y.1 e = 0} => y.1.1) hab
      exact Subtype.ext h1
    · simp only [ψ, ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 := congrArg (fun y : {y : G.CycleSpace // y.1 e = 0} => y.1.1) hab
      exact absurd h1 a.2.1
    · simp only [ψ, ha, hb, dif_pos, dif_neg, not_false_eq_true] at hab
      have h1 := congrArg (fun y : {y : G.CycleSpace // y.1 e = 0} => y.1.1) hab
      exact absurd h1.symm b.2.1
    · apply Subtype.ext
      rw [a.2.eq_single_of_loop he ha, b.2.eq_single_of_loop he hb]
  have hcard := Nat.card_le_card_of_injective ψ hψ
  have hhalf := two_mul_card_cycleSpace_avoiding_loop (G := G) he
  have hr : 1 ≤ G.cycleRank := by
    by_contra hr0
    have h0 : G.cycleRank = 0 := by omega
    rw [h0] at hhalf
    omega
  obtain ⟨k, hk⟩ : ∃ k, G.cycleRank = k + 1 := ⟨G.cycleRank - 1, by omega⟩
  rw [hk, pow_succ] at hhalf
  rw [hk, Nat.add_sub_cancel]
  unfold numCycles
  omega

end Erdos1016.FiniteMultiGraph

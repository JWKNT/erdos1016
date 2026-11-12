import Erdos1016.ExactMaximum.FourCutNumbering
import Erdos1016.ExactMaximum.FourPorts
import Erdos1016.ExactMaximum.FullPairs
import Erdos1016.ExactMaximum.Gadgets
import Erdos1016.ExactMaximum.ThreeCut

set_option autoImplicit false

/-!
# The numbers of a pole with four ports

Let `M` be a pole of rank `h` with four different ports `p 0, …, p 3`. Section 6.2 of the paper
"The maximum number of cycles in a graph of large rank" uses nine numbers: `a i j`, the number of
paths between the ports `i` and `j` divided by `2^h` (`pathShare`), and `u α`, the number of
pairs of disjoint paths for the pairing `α` divided by `2^h` (`pairShare`).

This file proves that these numbers satisfy the hypotheses of the arithmetic statement of
`FourCutArithmetic.lean`:

* `fourState_of_pole`: `FourState`, for every pole with four ports, from the gap theorem
  (`GapStatement`, a hypothesis), from `F ≤ 1` (`numPathPairs_add_le`) and from Lemma 6.7
  (`two_mul_numPathPairs_le_of_full`);
* `largeState_of_pole`: `LargeState`, for a pole of large rank, from Lemma 5.7 (b), (c), (d)
  (`gadget_third_pair`, `gadget_cross_pairs`, `gadget_opposite_pair`);
* `pairShare_le_half_of_rank_one`: `u α ≤ 1/2` for a side of rank one.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance fourCutSidesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type} [Fintype V] [Fintype E]

/-- The number of paths between the ports `i` and `j`, as a proportion of `2^h`. -/
def pathShare (M : Network V E) (p : Fin 4 → V) (i j : Fin 4) : ℝ :=
  (M.numPaths (p i) (p j) : ℝ) / 2 ^ networkRank M

/-- The number of pairs of disjoint paths for the pairings `01|23`, `02|13`, `03|12`. -/
def pairCount (M : Network V E) (p : Fin 4 → V) : Fin 3 → ℕ :=
  ![M.numPathPairs (p 0) (p 1) (p 2) (p 3), M.numPathPairs (p 0) (p 2) (p 1) (p 3),
    M.numPathPairs (p 0) (p 3) (p 1) (p 2)]

/-- The number of pairs of disjoint paths for the pairing `α`, as a proportion of `2^h`. -/
def pairShare (M : Network V E) (p : Fin 4 → V) (α : Fin 3) : ℝ :=
  (pairCount M p α : ℝ) / 2 ^ networkRank M

omit [Fintype V] in
/-- The pairs of disjoint paths between four different ports, in every order of the ports. -/
theorem numPathPairs_eq_pairCount (M : Network V E) (p : Fin 4 → V) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    M.numPathPairs (p i) (p j) (p k) (p l) = pairCount M p (pairingOf i j) :=
  quad_canon (fun i j k l => M.numPathPairs (p i) (p j) (p k) (p l))
    (fun _ _ _ _ => M.numPathPairs_swap_left _ _ _ _)
    (fun _ _ _ _ => M.numPathPairs_swap_right _ _ _ _)
    (fun _ _ _ _ => M.numPathPairs_comm _ _ _ _) (pairCount M p) rfl rfl rfl i j k l hij hik hil
    hjk hjl hkl

omit [Fintype V] in
/-- A pair of ports with share one is full. -/
theorem isFullPair_of_pathShare_eq_one (M : Network V E) (p : Fin 4 → V) {i j : Fin 4}
    (h : pathShare M p i j = 1) : M.IsFullPair (p i) (p j) := by
  have hD : (0 : ℝ) < 2 ^ networkRank M := by positivity
  unfold pathShare at h
  rw [div_eq_one_iff_eq hD.ne'] at h
  have h2 : M.numPaths (p i) (p j) = 2 ^ networkRank M := by exact_mod_cast h
  exact h2

/-- **The numbers of a pole with four ports.** They satisfy `FourState`: the gap, `F ≤ 1`, and
Lemma 6.7 of the paper. -/
theorem fourState_of_pole (hgap : GapStatement) (M : Network V E) (hM : M.IsWeakPole)
    (p : Fin 4 → V) (hp : Function.Injective p) (hport : ∀ i, M.IsPort (p i)) :
    FourState (pathShare M p) (pairShare M p) := by
  have hD : (0 : ℝ) < 2 ^ networkRank M := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    unfold pathShare
    rw [numPaths_symm M (p i) (p j)]
  · intro i j
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  · intro i j
    unfold pathShare
    rw [div_le_one hD]
    exact_mod_cast M.numPaths_le_two_pow (p i) (p j)
  · intro α
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  · unfold pairShare
    rw [← add_div, ← add_div, div_le_one hD]
    have h := M.numPathPairs_add_le (p 0) (p 1) (p 2) (p 3)
    have h' : pairCount M p 0 + pairCount M p 1 + pairCount M p 2 ≤ 2 ^ networkRank M := h
    exact_mod_cast h'
  · intro i j hij
    unfold pathShare
    rcases hgap V E M hM (p i) (p j) (hport i) (hport j) (fun h => hij (hp h)) with h | h
    · left
      rw [h, Nat.cast_pow, Nat.cast_ofNat]
      exact div_self hD.ne'
    · right
      rw [div_le_iff₀ hD]
      have h' : (16 : ℝ) * (M.numPaths (p i) (p j) : ℝ) ≤ 15 * 2 ^ networkRank M := by
        exact_mod_cast h
      linarith
  · intro i hi α
    obtain ⟨j, k, l, hij, hik, hil, hjk, hjl, hkl, hα⟩ := exists_pairing i α
    have hfull : ∀ m, m ≠ i → M.IsFullPair (p i) (p m) := fun m hm =>
      isFullPair_of_pathShare_eq_one M p (hi m hm)
    have h1 := two_mul_numPathPairs_le_of_full hM (p l) (hport k) (hfull j (Ne.symm hij))
      (hfull k (Ne.symm hik))
    rw [numPathPairs_eq_pairCount M p i j k l hij hik hil hjk hjl hkl, hα] at h1
    unfold pairShare
    rw [div_le_iff₀ hD]
    have h2 : (2 : ℝ) * (pairCount M p α : ℝ) ≤ 2 ^ networkRank M := by exact_mod_cast h1
    linarith

/-- **The numbers of a pole with four ports and large rank.** They satisfy `LargeState`: Lemma
5.7 (b), (c), (d) of the paper with `κ = 1/1000`. -/
theorem largeState_of_pole (hgap : GapStatement) {K : ℕ} (hF : FewCyclesWith K)
    (M : Network V E) (hM : M.IsWeakPole) (p : Fin 4 → V) (hp : Function.Injective p)
    (hport : ∀ i, M.IsPort (p i)) (hlarge : 4000000 * K ≤ 2 ^ networkRank M) :
    LargeState (pathShare M p) (pairShare M p) := by
  have hD : (0 : ℝ) < 2 ^ networkRank M := by positivity
  have hne : ∀ {i j : Fin 4}, i ≠ j → p i ≠ p j := fun h h' => h (hp h')
  refine { toFourState := fourState_of_pole hgap M hM p hp hport, t1 := ?_, t2 := ?_, t3 := ?_ }
  · intro i j k hij hik hjk hsum
    have hmany : 1002 * 2 ^ networkRank M ≤
        1000 * (M.numPaths (p i) (p k) + M.numPaths (p j) (p k)) := by
      unfold pathShare at hsum
      rw [← add_div, le_div_iff₀ hD] at hsum
      have h' : (1002 : ℝ) * 2 ^ networkRank M ≤
          1000 * ((M.numPaths (p i) (p k) : ℝ) + (M.numPaths (p j) (p k) : ℝ)) := by linarith
      exact_mod_cast h'
    have h1 := gadget_third_pair hF M hM (hport i) (hport j) (hport k) (hne hij)
      (hne (Ne.symm hik)) (hne (Ne.symm hjk)) hmany
    have h2 := thousand_mul_le h1 (by omega)
    unfold pathShare
    rw [div_le_iff₀ hD]
    have h3 : (1000 : ℝ) * (M.numPaths (p i) (p j) : ℝ) ≤ 2 ^ networkRank M := by
      exact_mod_cast h2
    linarith
  · intro i j k l hij hik hil hjk hjl hkl hsum
    have hmany : 2004 * 2 ^ networkRank M ≤
        1000 * (M.numPaths (p i) (p k) + M.numPaths (p j) (p k) +
          (M.numPaths (p i) (p l) + M.numPaths (p j) (p l))) := by
      unfold pathShare at hsum
      rw [← add_div, ← add_div, ← add_div, le_div_iff₀ hD] at hsum
      have h' : (2004 : ℝ) * 2 ^ networkRank M ≤
          1000 * ((M.numPaths (p i) (p k) : ℝ) + (M.numPaths (p j) (p k) : ℝ) +
            ((M.numPaths (p i) (p l) : ℝ) + (M.numPaths (p j) (p l) : ℝ))) := by linarith
      exact_mod_cast h'
    have h1 := gadget_cross_pairs hF M hM (hport i) (hport j) (hport k) (hport l) (hne hij)
      (hne hkl) (hne (Ne.symm hik)) (hne (Ne.symm hjk)) (hne (Ne.symm hil)) (hne (Ne.symm hjl))
      hmany
    rw [numPathPairs_eq_pairCount M p k i j l (Ne.symm hik) (Ne.symm hjk) hkl hij hil hjl,
      numPathPairs_eq_pairCount M p k j i l (Ne.symm hjk) (Ne.symm hik) hkl (Ne.symm hij) hjl hil,
      pairingOf_comm k i,
      pairingOf_opposite i l k j hil hik hij (Ne.symm hkl) (Ne.symm hjl) (Ne.symm hjk)] at h1
    have h1' : (pairCount M p (pairingOf i k) + pairCount M p (pairingOf i l)) ^ 2 ≤
        2 * (2 * K) * 2 ^ networkRank M := by
      have e : 2 * (2 * K) * 2 ^ networkRank M = 4 * K * 2 ^ networkRank M := by ring
      rw [e]
      exact h1
    have h2 := thousand_mul_le h1' (by omega)
    unfold pairShare
    rw [← add_div, div_le_iff₀ hD]
    have h3 : (1000 : ℝ) * ((pairCount M p (pairingOf i k) : ℝ) +
        (pairCount M p (pairingOf i l) : ℝ)) ≤ 2 ^ networkRank M := by exact_mod_cast h2
    linarith
  · intro i j k l hij hik hil hjk hjl hkl hsum
    have hmany : 1002 * 2 ^ networkRank M ≤
        1000 * (M.numPaths (p i) (p j) + M.numPathPairs (p i) (p k) (p l) (p j) +
          M.numPathPairs (p i) (p l) (p k) (p j)) := by
      rw [numPathPairs_eq_pairCount M p i k l j hik hil hij hkl (Ne.symm hjk) (Ne.symm hjl),
        numPathPairs_eq_pairCount M p i l k j hil hik hij (Ne.symm hkl) (Ne.symm hjl)
          (Ne.symm hjk)]
      unfold pathShare pairShare at hsum
      rw [← add_div, ← add_div, le_div_iff₀ hD] at hsum
      have h' : (1002 : ℝ) * 2 ^ networkRank M ≤
          1000 * ((M.numPaths (p i) (p j) : ℝ) + (pairCount M p (pairingOf i k) : ℝ) +
            (pairCount M p (pairingOf i l) : ℝ)) := by linarith
      exact_mod_cast h'
    have h1 := gadget_opposite_pair hF M hM (hport k) (hport l) (hport i) (hport j) (hne hkl)
      (hne hij) (hne hik) (hne hil) (hne hjk) (hne hjl) hmany
    have h2 := thousand_mul_le h1 (by omega)
    unfold pathShare
    rw [div_le_iff₀ hD]
    have h3 : (1000 : ℝ) * (M.numPaths (p k) (p l) : ℝ) ≤ 2 ^ networkRank M := by
      exact_mod_cast h2
    linarith

/-- **A side of rank one.** If every vertex has even degree and the rank is one, then
`u α ≤ 1/2` for every pairing. -/
theorem pairShare_le_half_of_rank_one (M : Network V E) (p : Fin 4 → V)
    (heven : M.boundary (fun _ => 1) = 0) (h1 : networkRank M = 1) (α : Fin 3) :
    pairShare M p α ≤ 1 / 2 := by
  have h : pairCount M p α ≤ 1 := by
    fin_cases α
    · exact M.numPathPairs_le_one_of_rank_one heven h1 _ _ _ _
    · exact M.numPathPairs_le_one_of_rank_one heven h1 _ _ _ _
    · exact M.numPathPairs_le_one_of_rank_one heven h1 _ _ _ _
  unfold pairShare
  rw [h1, pow_one]
  have h' : (pairCount M p α : ℝ) ≤ 1 := by exact_mod_cast h
  linarith

end Erdos1016.ExactMaximum

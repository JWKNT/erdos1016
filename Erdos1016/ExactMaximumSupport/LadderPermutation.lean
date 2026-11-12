import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

/-!
# The finite permutation step in the capped-ladder classification

The two forbidden triples in Lemma 5.8 force the matching permutation to
consist of fixed points and disjoint exchanges of consecutive indices.
The argument uses actual finite permutations, with no graph assumptions.
-/

namespace Erdos1016.ExactMaximumSupport.LadderPermutation

variable {n : ℕ}

/-- The two forbidden order patterns obtained from a disjoint cycle and path. -/
def AvoidsLadderPatterns (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k, i < j → j < k →
    ¬ (π k < π i ∧ π k < π j) ∧ ¬ (π j < π i ∧ π k < π i)

/-- An inversion cannot span an intermediate index. -/
theorem inversion_adjacent {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    {i j : Fin n} (hij : i < j) (hinv : π j < π i) :
    j.val = i.val + 1 := by
  by_contra hgap
  have hklt : i.val + 1 < j.val := by omega
  let k : Fin n := ⟨i.val + 1, by omega⟩
  have hik : i < k := by change i.val < i.val + 1; omega
  have hkj : k < j := hklt
  have hp := hπ i k j hik hkj
  by_cases hlow : π j < π k
  · exact hp.1 ⟨hinv, hlow⟩
  · have hki : π k < π i := by omega
    exact hp.2 ⟨hki, hinv⟩

private theorem eq_of_lower_preimage (π : Equiv.Perm (Fin n)) (i j : Fin n)
    (h : ∀ k, k < i ↔ π k < j) : i = j := by
  classical
  have hc := Fintype.card_congr
    (π.subtypeEquiv (p := fun k => k < i) (q := fun k => k < j) h)
  simp only [Fintype.card_subtype] at hc
  have hi (a : Fin n) : (Finset.univ.filter fun k => k < a) = Finset.Iio a := by
    ext k
    simp
  have hv : i.val = j.val := by simpa only [hi, Fin.card_Iio] using hc
  exact Fin.ext hv

/-- Each inversion is precisely the exchange of its two consecutive indices. -/
theorem inversion_exchange {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    {i j : Fin n} (hij : i < j) (hinv : π j < π i) :
    π i = j ∧ π j = i ∧ j.val = i.val + 1 := by
  have hadj := inversion_adjacent hπ hij hinv
  have hbefore : ∀ k, k < i → π k < π j := by
    intro k hki
    have hne : π k ≠ π j := fun h => (ne_of_lt (hki.trans hij)) (π.injective h)
    by_contra hnot
    have hrev : π j < π k := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
    have hbad := inversion_adjacent hπ (hki.trans hij) hrev
    omega
  have hiff : ∀ k, k < i ↔ π k < π j := by
    intro k
    refine ⟨hbefore k, ?_⟩
    intro hkj
    by_contra hnot
    have hkni : k ≠ i := by intro h; subst k; exact (not_lt_of_ge hinv.le) hkj
    have hknj : k ≠ j := by intro h; subst k; exact (lt_irrefl _) hkj
    have hjk : j < k := by
      have hki : i ≤ k := le_of_not_gt hnot
      have hkin : k.val ≠ i.val := fun h => hkni (Fin.ext h)
      have hkjn : k.val ≠ j.val := fun h => hknj (Fin.ext h)
      omega
    have hbad := inversion_adjacent hπ (hij.trans hjk) (hkj.trans hinv)
    omega
  have hji : π j = i := (eq_of_lower_preimage π i (π j) hiff).symm
  have hij' : π i = j := by
    by_contra hne
    have hgreater : j < π i := by
      have hvalne : (π i).val ≠ j.val := fun h => hne (Fin.ext h)
      rw [hji] at hinv
      omega
    let k := π.symm j
    have hk : π k = j := π.apply_symm_apply j
    have hkni : k ≠ i := by intro h; exact hne (h ▸ hk)
    have hknj : k ≠ j := by
      intro h
      have he : i = j := hji.symm.trans (h ▸ hk)
      exact (ne_of_lt hij) he
    by_cases hki : k < i
    · have hb := hbefore k hki
      rw [hk, hji] at hb
      exact (not_lt_of_ge hij.le) hb
    · have hjk : j < k := by
        have hki' : i ≤ k := le_of_not_gt hki
        have hkin : k.val ≠ i.val := fun h => hkni (Fin.ext h)
        have hkjn : k.val ≠ j.val := fun h => hknj (Fin.ext h)
        omega
      have hbad := inversion_adjacent hπ (hij.trans hjk) (hk ▸ hgreater)
      omega
  exact ⟨hij', hji, hadj⟩

/-- Every index is fixed or belongs to a reciprocal exchange with an adjacent index. -/
theorem fixed_or_adjacent_exchange {π : Equiv.Perm (Fin n)}
    (hπ : AvoidsLadderPatterns π) (i : Fin n) :
    π i = i ∨ ∃ j, π i = j ∧ π j = i ∧
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  classical
  by_cases hleft : ∃ j, j < i ∧ π i < π j
  · obtain ⟨j, hji, hinv⟩ := hleft
    obtain ⟨hji', hij', hadj⟩ := inversion_exchange hπ hji hinv
    exact Or.inr ⟨j, hij', hji', Or.inr hadj.symm⟩
  · by_cases hright : ∃ j, i < j ∧ π j < π i
    · obtain ⟨j, hij, hinv⟩ := hright
      obtain ⟨hij', hji', hadj⟩ := inversion_exchange hπ hij hinv
      exact Or.inr ⟨j, hij', hji', Or.inl hadj.symm⟩
    · left
      apply Eq.symm
      apply eq_of_lower_preimage π i (π i)
      intro k
      constructor
      · intro hki
        have hne : π k ≠ π i := fun h => (ne_of_lt hki) (π.injective h)
        have hn : ¬ π i < π k := fun h => hleft ⟨k, hki, h⟩
        exact lt_of_le_of_ne (le_of_not_gt hn) hne
      · intro hki
        by_contra hn
        have hne : k ≠ i := fun h => (lt_irrefl (π i)) (h ▸ hki)
        have hik : i < k := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
        exact hright ⟨k, hik, hki⟩

/-- The matching permutation is an involution. -/
theorem involutive {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    Function.Involutive π := by
  intro i
  rcases fixed_or_adjacent_exchange hπ i with h | ⟨j, hij, hji, _⟩
  · rw [h, h]
  · rw [hij, hji]

/-- Every index moves at most one place in either direction. -/
theorem displacement_le_one {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    (i : Fin n) : (π i).val ≤ i.val + 1 ∧ i.val ≤ (π i).val + 1 := by
  rcases fixed_or_adjacent_exchange hπ i with h | ⟨j, hij, _, hadj⟩
  · rw [h]; omega
  · rw [hij]; rcases hadj with h | h <;> omega

/-- The first index of each canonical singleton or adjacent-pair tile. -/
def tileStarts (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≤ π i

/-- The indices occupied by the tile starting at `i`. -/
def tile (π : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) := {i, π i}

/-- A fixed point gives a rung, and an adjacent exchange gives a square. -/
def tileWeight (π : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  if π i = i then 1 else 2

/-- Every canonical tile is a singleton or an interval of two consecutive indices. -/
theorem tile_shape {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    {i : Fin n} (hi : i ∈ tileStarts π) :
    tile π i = {i} ∨ ∃ j, j.val = i.val + 1 ∧ tile π i = {i, j} := by
  have hstart : i ≤ π i := (Finset.mem_filter.mp hi).2
  rcases fixed_or_adjacent_exchange hπ i with h | ⟨j, hij, _, hadj⟩
  · left
    simp [tile, h]
  · right
    refine ⟨j, ?_, by simp only [tile, hij]⟩
    rw [hij] at hstart
    rcases hadj with h | h <;> omega

/-- Distinct canonical tile starts have disjoint index sets. -/
theorem tiles_pairwise_disjoint {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    (↑(tileStarts π) : Set (Fin n)).PairwiseDisjoint (tile π) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi' : i ≤ π i := (Finset.mem_filter.mp hi).2
  have hj' : j ≤ π j := (Finset.mem_filter.mp hj).2
  have hinv := involutive hπ
  simp only [tile, Finset.mem_insert, Finset.mem_singleton] at hxi hxj
  rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
  · exact hij (hxi.symm.trans hxj)
  · have he : i = π j := hxi.symm.trans hxj
    have he' : π i = j := by rw [he, hinv]
    exact hij (le_antisymm (he' ▸ hi') (he ▸ hj'))
  · have he : j = π i := hxj.symm.trans hxi
    have he' : π j = i := by rw [he, hinv]
    exact hij (le_antisymm (he ▸ hi') (he' ▸ hj'))
  · exact hij (π.injective (hxi.symm.trans hxj))

/-- The canonical tiles cover all indices. -/
theorem tiles_cover {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    (tileStarts π).biUnion (tile π) = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  by_cases hx : x ≤ π x
  · apply Finset.mem_biUnion.mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, by simp [tile]⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨π x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [involutive hπ x]
      exact (lt_of_not_ge hx).le
    · simp [tile, involutive hπ x]

/-- The tile weight is its actual number of indices. -/
theorem tile_card (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (tile π i).card = tileWeight π i := by
  by_cases h : π i = i
  · simp [tile, tileWeight, h]
  · simp [tile, tileWeight, h, Ne.symm h]

/-- The weights of the canonical ordered tiles sum to the original number of indices. -/
theorem sum_tileWeights {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    ∑ i ∈ tileStarts π, tileWeight π i = n := by
  have hc := Finset.card_biUnion (tiles_pairwise_disjoint hπ)
  rw [tiles_cover hπ, Finset.card_univ, Fintype.card_fin] at hc
  simpa only [tile_card] using hc.symm

end Erdos1016.ExactMaximumSupport.LadderPermutation

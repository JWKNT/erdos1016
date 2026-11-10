import Erdos1016.ExactCounting.ShortCycle

set_option autoImplicit false

/-!
# The lemma of Erdős and Pósa on two edge-disjoint cycles

Let a multigraph have its edges in `A` and its vertices in `U`. If any two
nonempty even subsets of `A` share an edge, then `A` has at most `|U| + 3`
edges. Equivalently, a multigraph with `n` vertices and at least `n + 4` edges
contains two edge-disjoint cycles.

The proof is by induction on the number of edges and vertices. A vertex with
at most one edge is deleted. A vertex of degree two is suppressed. If all
degrees are at least three and there are `n + 4` edges, then `n ≤ 8`. Then a
set of at most four edges contains an even set, and the remaining `n` edges
contain a second one.
-/

namespace Erdos1016.ExactCounting.Multi

open Finset

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem card_le_of_intersecting_aux : ∀ (N : ℕ) (ends : ι → V × V) (A : Finset ι)
    (U : Finset V), A.card + U.card = N → EndsIn ends A U → Intersecting ends A →
    A.card ≤ U.card + 3 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ends A U hN hU hI
    by_cases hlow : ∃ v ∈ U, deg ends A v ≤ 2
    · obtain ⟨v, hvU, hdv⟩ := hlow
      have hUpos : 0 < U.card := card_pos.2 ⟨v, hvU⟩
      have hstar_le : (star ends A v).card ≤ deg ends A v := card_star_le_deg ends A v
      by_cases hsmall : (star ends A v).card ≤ 1
      · -- Delete `v` and the edges at `v`.
        have hsub : star ends A v ⊆ A := filter_subset _ _
        have hcard : (A \ star ends A v).card = A.card - (star ends A v).card :=
          card_sdiff hsub
        have hle := card_le_card hsub
        have hrec := ih ((A \ star ends A v).card + (U.erase v).card)
          (by rw [hcard, card_erase_of_mem hvU]; omega)
          ends (A \ star ends A v) (U.erase v) rfl (endsIn_sdiff_star hU v)
          (hI.mono sdiff_subset)
        rw [hcard, card_erase_of_mem hvU] at hrec
        omega
      · -- Suppress `v`.
        have h2 : (star ends A v).card = 2 := by omega
        obtain ⟨e, f, hef, hstar⟩ := card_eq_two.1 h2
        have heS : e ∈ star ends A v := by rw [hstar]; simp
        have hfS : f ∈ star ends A v := by rw [hstar]; simp
        have heA := (mem_filter.1 heS).1
        have hfA := (mem_filter.1 hfS).1
        have hdeg2 : deg ends A v = inc ends e v + inc ends f v := by
          rw [deg_eq_sum_star, hstar, sum_pair hef]
        have hie : 1 ≤ inc ends e v := (inc_pos_iff ends e v).2 (mem_filter.1 heS).2
        have hif : 1 ≤ inc ends f v := (inc_pos_iff ends f v).2 (mem_filter.1 hfS).2
        have hie1 : inc ends e v = 1 := by omega
        have hif1 : inc ends f v = 1 := by omega
        obtain ⟨u, huv, huend, hince⟩ := inc_of_inc_eq_one ends e v hie1
        obtain ⟨w, hwv, hwend, hincf⟩ := inc_of_inc_eq_one ends f v hif1
        have hI' := intersecting_suppress ends A v u w e f hfA hince hincf hI
        have huU : u ∈ U := by
          rcases huend with h | h
          · exact h ▸ (hU e heA).1
          · exact h ▸ (hU e heA).2
        have hwU : w ∈ U := by
          rcases hwend with h | h
          · exact h ▸ (hU f hfA).1
          · exact h ▸ (hU f hfA).2
        have hU' : EndsIn (Function.update ends e (u, w)) (A.erase f) (U.erase v) := by
          intro g hg
          have hgA := mem_of_mem_erase hg
          have hgf := ne_of_mem_erase hg
          by_cases hge : g = e
          · subst hge
            rw [Function.update_self]
            exact ⟨mem_erase.2 ⟨huv, huU⟩, mem_erase.2 ⟨hwv, hwU⟩⟩
          · rw [Function.update_of_ne hge]
            have hnot : g ∉ star ends A v := by
              rw [hstar]
              simp [hge, hgf]
            have hnot' : ¬((ends g).1 = v ∨ (ends g).2 = v) := fun h =>
              hnot (mem_filter.2 ⟨hgA, h⟩)
            push_neg at hnot'
            exact ⟨mem_erase.2 ⟨hnot'.1, (hU g hgA).1⟩, mem_erase.2 ⟨hnot'.2, (hU g hgA).2⟩⟩
        have hApos : 0 < A.card := card_pos.2 ⟨f, hfA⟩
        have hrec := ih ((A.erase f).card + (U.erase v).card)
          (by rw [card_erase_of_mem hfA, card_erase_of_mem hvU]; omega)
          _ _ _ rfl hU' hI'
        rw [card_erase_of_mem hfA, card_erase_of_mem hvU] at hrec
        omega
    · push_neg at hlow
      by_contra hgt
      push_neg at hgt
      have hsum := sum_deg ends A U hU
      have h3 : 3 * U.card ≤ 2 * A.card := by
        rw [← hsum]
        calc 3 * U.card = ∑ _v ∈ U, 3 := by simp [mul_comm]
          _ ≤ ∑ v ∈ U, deg ends A v := sum_le_sum fun v hv => by
            have := hlow v hv
            omega
      have hAne : A.Nonempty := card_pos.1 (by omega)
      by_cases h5 : U.card + 5 ≤ A.card
      · obtain ⟨e, he⟩ := hAne
        have hApos : 0 < A.card := card_pos.2 ⟨e, he⟩
        have hrec := ih ((A.erase e).card + U.card)
          (by rw [card_erase_of_mem he]; omega)
          ends (A.erase e) U rfl (fun g hg => hU g (mem_of_mem_erase hg))
          (hI.mono (erase_subset _ _))
        rw [card_erase_of_mem he] at hrec
        omega
      · have hUne : U.Nonempty := by
          obtain ⟨e, he⟩ := hAne
          exact ⟨(ends e).1, (hU e he).1⟩
        have hUpos : 0 < U.card := card_pos.2 hUne
        obtain ⟨B, W, hBA, hBne, hB4, hBW, hWB⟩ := exists_small_dense ends A U hU
          (fun v hv => by have := hlow v hv; omega) hUne (by omega)
        obtain ⟨Y₁, hY₁B, hY₁ne, hY₁ev⟩ := exists_even_subset ends B W hBW hBne hWB
        have hrest : U.card ≤ (A \ B).card := by
          rw [card_sdiff hBA]
          omega
        have hrestne : (A \ B).Nonempty := card_pos.1 (by omega)
        obtain ⟨Y₂, hY₂, hY₂ne, hY₂ev⟩ := exists_even_subset ends (A \ B) U
          (fun g hg => hU g (mem_sdiff.1 hg).1) hrestne hrest
        obtain ⟨g, hg⟩ := hI Y₁ Y₂ (hY₁B.trans hBA) (hY₂.trans sdiff_subset) hY₁ne hY₂ne
          hY₁ev hY₂ev
        rw [mem_inter] at hg
        exact (mem_sdiff.1 (hY₂ hg.2)).2 (hY₁B hg.1)

/-- If any two nonempty even subsets of `A` share an edge, then `A` has at most
`|U| + 3` edges. This is the lemma of Erdős and Pósa. -/
theorem card_le_of_intersecting (ends : ι → V × V) (A : Finset ι) (U : Finset V)
    (hU : EndsIn ends A U) (hI : Intersecting ends A) : A.card ≤ U.card + 3 :=
  card_le_of_intersecting_aux _ ends A U rfl hU hI

end Erdos1016.ExactCounting.Multi

import Erdos1016.ExactMaximum.GirthFive.TwoTerminal
import Erdos1016.ExactMaximumSupport.LargeGirth.SimpleRealization
import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProductWords
import Erdos1016.Graph.PhysicalDegree
import Erdos1016.PolynomialBound.Separation

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Words of a multigraph inside a region

`N` is a finite multigraph without cycles of length less than five, and `K = N.toSimpleGraph`.
This file connects the edge words of `N` with the simple graph `K`:

* `girthGreater_toSimpleGraph`: every cycle of `K` has more than four edges;
* `card_nbrs_eq_degree`: the number of neighbours in `K` is the degree in `N`;
* `walkWord_support`: the word of a walk uses edges between vertices of the walk;
* `card_internalEdges_le`: a region without a nonzero even word has at most as many internal
  edges as vertices;
* `sum_card_nbrs_le`: the neighbours inside a region, summed over the region, are at most twice
  the number of internal edges;
* `exists_word_of_sides_even`: if a demand vanishes on a set `X` and has even sum on every
  component of the complement of `X`, then it is the boundary of a word on edges without an end
  in `X`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph FiniteMultiGraph Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.ExactMaximumSupport.LargeGirth Erdos1016.PolynomialBound.Separation

local instance regionWordsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (N : FiniteMultiGraph)

/-- Every cycle of the underlying simple graph has more than four edges. -/
theorem girthGreater_toSimpleGraph (h5 : ¬ N.HasCycleShorterThan 5) :
    GirthGreater N.toSimpleGraph 4 := by
  have h3 := no_short_three_of_le N 5 (by norm_num) h5
  have hg := realization_girthGreater N h3 4 h5
  rwa [realization_toSimpleGraph] at hg

/-- The number of neighbours in the underlying simple graph is the degree. -/
theorem card_nbrs_eq_degree (h3 : ¬ N.HasCycleShorterThan 3) (v : N.Vertex) :
    (nbrs N.toSimpleGraph v).card = N.degree v := by
  have h := Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card
    (realization N h3) v
  rw [realization_degree] at h
  rw [h]
  apply congrArg Finset.card
  ext u
  simp only [mem_nbrs, SimpleGraph.mem_neighborFinset]
  rw [realization_toSimpleGraph]

/-- The word of a walk uses only edges between vertices of the walk. -/
theorem walkWord_support {u v : N.Vertex} (p : N.toSimpleGraph.Walk u v) (e : N.Edge)
    (he : N.walkWord p e ≠ 0) : N.src e ∈ p.support ∧ N.dst e ∈ p.support := by
  induction p with
  | nil => exact absurd rfl he
  | @cons a b c hab p ih =>
    by_cases hee : e = N.edgeForAdj hab
    · have hb : b ∈ p.support := p.start_mem_support
      rcases N.edgeForAdj_endpoints hab with hh | hh
      · rw [hee, hh.1, hh.2]
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ hb⟩
      · rw [hee, hh.1, hh.2]
        exact ⟨List.mem_cons_of_mem _ hb, List.mem_cons_self⟩
    · have hp : N.walkWord p e ≠ 0 := by
        intro h0
        apply he
        show (Pi.single (N.edgeForAdj hab) (1 : F₂) : N.EdgeWord) e + N.walkWord p e = 0
        rw [h0, add_zero, Pi.single_apply, if_neg hee]
      obtain ⟨h1, h2⟩ := ih hp
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- A region without a nonzero even word has at most as many internal edges as vertices. -/
theorem card_internalEdges_le (F : Finset N.Vertex)
    (hF : ∀ z : N.internalCycleSpace F, z = 0) :
    (N.internalEdges F).card ≤ F.card := by
  have he := (PieceCore.Induced.graph N F).euler_formula
  rw [PieceCore.Induced.vertexCount, PieceCore.Induced.edgeCount] at he
  have hr : (PieceCore.Induced.graph N F).cycleRank = 0 := by
    unfold FiniteMultiGraph.cycleRank
    rw [(PoleProduct.cycleEquiv N F).finrank_eq]
    haveI : Subsingleton (N.internalCycleSpace F) :=
      ⟨fun a b => (hF a).trans (hF b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  omega

/-- The neighbours inside a region, summed over the region, are at most twice the number of
internal edges. -/
theorem sum_card_nbrs_le (F : Finset N.Vertex) :
    (∑ v ∈ F, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ F)).card) ≤
      2 * (N.internalEdges F).card := by
  -- the internal edges at a vertex
  have hstep : ∀ v ∈ F, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ F)).card ≤
      ((N.internalEdges F).filter (fun e => N.src e = v ∨ N.dst e = v)).card := by
    intro v hv
    let ψ : N.Edge → N.Vertex := fun e => if N.src e = v then N.dst e else N.src e
    have hsub : (nbrs N.toSimpleGraph v).filter (fun u => u ∈ F) ⊆
        ((N.internalEdges F).filter (fun e => N.src e = v ∨ N.dst e = v)).image ψ := by
      intro u hu
      rw [Finset.mem_filter, mem_nbrs] at hu
      obtain ⟨hadj, huF⟩ := hu
      have hne : v ≠ u := hadj.1
      rw [Finset.mem_image]
      refine ⟨N.edgeForAdj hadj, ?_, ?_⟩
      · rw [Finset.mem_filter]
        rcases N.edgeForAdj_endpoints hadj with hh | hh
        · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hh.1]; exact hv,
            by rw [hh.2]; exact huF⟩, Or.inl hh.1⟩
        · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hh.1]; exact huF,
            by rw [hh.2]; exact hv⟩, Or.inr hh.2⟩
      · rcases N.edgeForAdj_endpoints hadj with hh | hh
        · show (if N.src (N.edgeForAdj hadj) = v then _ else _) = u
          rw [if_pos hh.1, hh.2]
        · show (if N.src (N.edgeForAdj hadj) = v then _ else _) = u
          rw [if_neg (by rw [hh.1]; exact fun h => hne h.symm), hh.1]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  calc
    (∑ v ∈ F, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ F)).card) ≤
        ∑ v ∈ F, ((N.internalEdges F).filter (fun e => N.src e = v ∨ N.dst e = v)).card :=
      Finset.sum_le_sum hstep
    _ = ∑ v ∈ F, ∑ e ∈ N.internalEdges F, (if N.src e = v ∨ N.dst e = v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.card_filter]
    _ = ∑ e ∈ N.internalEdges F, ∑ v ∈ F, (if N.src e = v ∨ N.dst e = v then 1 else 0) :=
      Finset.sum_comm
    _ ≤ ∑ _e ∈ N.internalEdges F, 2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [← Finset.card_filter]
      have hsub : F.filter (fun v => N.src e = v ∨ N.dst e = v) ⊆ {N.src e, N.dst e} := by
        intro v hv
        rw [Finset.mem_filter] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hv.2 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    _ = 2 * (N.internalEdges F).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Words in the components of the complement of a set.** Let `b` be a demand that vanishes on
`X` and has even sum on the set of the vertices that a walk outside `X` joins to `v`, for every
`v` outside `X`. Then `b` is the boundary of a word whose edges have no end in `X`. -/
theorem exists_word_of_sides_even (X : Set N.Vertex) :
    ∀ (n : ℕ) (b : N.Demand), (Finset.univ.filter (fun v => b v ≠ 0)).card = n →
      (∀ v, v ∈ X → b v = 0) →
      (∀ v, v ∉ X →
        (∑ u ∈ Finset.univ.filter (fun u => AvoidReach N.toSimpleGraph X v u), b u) = 0) →
      ∃ w : N.EdgeWord, N.boundary w = b ∧ ∀ e, w e ≠ 0 → N.src e ∉ X ∧ N.dst e ∉ X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hX hev
    by_cases hb : ∀ v, b v = 0
    · refine ⟨0, ?_, fun e he => absurd rfl he⟩
      rw [map_zero]
      funext v
      exact (hb v).symm
    push_neg at hb
    obtain ⟨u, hu⟩ := hb
    have huX : u ∉ X := fun h => hu (hX u h)
    -- another vertex of the same component with a nonzero demand
    have hex : ∃ u', AvoidReach N.toSimpleGraph X u u' ∧ u' ≠ u ∧ b u' ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hsum := hev u huX
      rw [Finset.sum_eq_single u] at hsum
      · exact hu hsum
      · intro t ht htu
        exact hcon t (Finset.mem_filter.mp ht).2 htu
      · intro hnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, AvoidReach.refl huX⟩) hnot
    obtain ⟨u', hreach, hne, hu'⟩ := hex
    obtain ⟨p, hp⟩ := hreach
    -- the values are one, because the field has two elements
    have hone : ∀ t, b t ≠ 0 → b t = 1 := by
      intro t ht
      have := Fin.exists_fin_two.mp ⟨b t, rfl⟩
      rcases this with h | h
      · exact absurd h ht
      · exact h
    let b' : N.Demand := b + N.vertexUnit u + N.vertexUnit u'
    have hb'u : b' u = 0 := by
      show b u + N.vertexUnit u u + N.vertexUnit u' u = 0
      simp only [vertexUnit, Pi.single_apply, if_true, if_neg hne.symm, add_zero, hone u hu]
      decide
    have hb'u' : b' u' = 0 := by
      show b u' + N.vertexUnit u u' + N.vertexUnit u' u' = 0
      simp only [vertexUnit, Pi.single_apply, if_true, if_neg hne, add_zero, hone u' hu']
      decide
    have hb't : ∀ t, t ≠ u → t ≠ u' → b' t = b t := by
      intro t h1 h2
      show b t + N.vertexUnit u t + N.vertexUnit u' t = b t
      simp only [vertexUnit, Pi.single_apply, if_neg h1, if_neg h2, add_zero]
    -- the support of the new demand is smaller
    have hsupp : Finset.univ.filter (fun v => b' v ≠ 0) =
        ((Finset.univ.filter (fun v => b v ≠ 0)).erase u).erase u' := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases h1 : t = u
      · subst h1
        simp [hb'u]
      by_cases h2 : t = u'
      · subst h2
        simp [hb'u']
      rw [hb't t h1 h2]
      simp [h1, h2]
    have hcard : (Finset.univ.filter (fun v => b' v ≠ 0)).card + 2 = n := by
      rw [hsupp, Finset.card_erase_of_mem, Finset.card_erase_of_mem, hn]
      · have h1 : 1 ≤ n := by
          rw [← hn]
          exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
        have h2 : 2 ≤ n := by
          rw [← hn]
          exact Finset.one_lt_card.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, u',
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩, hne.symm⟩
        omega
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
      · exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩⟩
    have hX' : ∀ v, v ∈ X → b' v = 0 := by
      intro v hv
      have h1 : v ≠ u := fun h => huX (h ▸ hv)
      have h2 : v ≠ u' := fun h => hp u' p.end_mem_support (h ▸ hv)
      rw [hb't v h1 h2]
      exact hX v hv
    have hev' : ∀ v, v ∉ X →
        (∑ t ∈ Finset.univ.filter (fun t => AvoidReach N.toSimpleGraph X v t), b' t) = 0 := by
      intro v hv
      have hsplit : (∑ t ∈ Finset.univ.filter (fun t => AvoidReach N.toSimpleGraph X v t), b' t) =
          (∑ t ∈ Finset.univ.filter (fun t => AvoidReach N.toSimpleGraph X v t), b t) +
          (∑ t ∈ Finset.univ.filter (fun t => AvoidReach N.toSimpleGraph X v t),
            N.vertexUnit u t) +
          (∑ t ∈ Finset.univ.filter (fun t => AvoidReach N.toSimpleGraph X v t),
            N.vertexUnit u' t) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        rfl
      rw [hsplit, hev v hv, zero_add]
      by_cases hvu : AvoidReach N.toSimpleGraph X v u
      · have hvu' : AvoidReach N.toSimpleGraph X v u' := hvu.trans ⟨p, hp⟩
        rw [Finset.sum_eq_single u, Finset.sum_eq_single u']
        · simp only [vertexUnit, Pi.single_apply, if_true]
          decide
        · intro t _ ht
          simp only [vertexUnit, Pi.single_apply, if_neg ht]
        · intro hnot
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu'⟩) hnot
        · intro t _ ht
          simp only [vertexUnit, Pi.single_apply, if_neg ht]
        · intro hnot
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu⟩) hnot
      · have hvu' : ¬ AvoidReach N.toSimpleGraph X v u' :=
          fun h => hvu (h.trans (AvoidReach.symm ⟨p, hp⟩))
        rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
        · intro t ht
          have htu' : t ≠ u' := fun h => hvu' (h ▸ (Finset.mem_filter.mp ht).2)
          simp only [vertexUnit, Pi.single_apply, if_neg htu']
        · intro t ht
          have htu : t ≠ u := fun h => hvu (h ▸ (Finset.mem_filter.mp ht).2)
          simp only [vertexUnit, Pi.single_apply, if_neg htu]
    obtain ⟨w', hw', hsup'⟩ := ih _ (by omega) b' rfl hX' hev'
    refine ⟨w' + N.walkWord p, ?_, ?_⟩
    · rw [map_add, hw', boundary_walkWord]
      funext t
      show b t + N.vertexUnit u t + N.vertexUnit u' t + (N.vertexUnit u t + N.vertexUnit u' t) =
        b t
      have h2 : ∀ a : F₂, a + a = 0 := by decide
      have : b t + N.vertexUnit u t + N.vertexUnit u' t +
          (N.vertexUnit u t + N.vertexUnit u' t) =
          b t + (N.vertexUnit u t + N.vertexUnit u t) +
            (N.vertexUnit u' t + N.vertexUnit u' t) := by ring
      rw [this, h2, h2, add_zero, add_zero]
    · intro e he
      by_cases h1 : w' e ≠ 0
      · exact hsup' e h1
      · push_neg at h1
        have h2 : N.walkWord p e ≠ 0 := by
          intro h0
          apply he
          show w' e + N.walkWord p e = 0
          rw [h1, h0, add_zero]
        obtain ⟨hs, hd⟩ := walkWord_support N p e h2
        exact ⟨hp _ hs, hp _ hd⟩

end Erdos1016.ExactMaximum.GirthFive

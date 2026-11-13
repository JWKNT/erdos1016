import Erdos1016.ExactMaximum.GirthFive.Pieces
import Erdos1016.ExactMaximumSupport.Shortening.ChainPacking

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Packing of cyclic regions at girth five

The files `Shortening/ChainPackingBounds.lean`, `ChainPackingGeometry.lean` and
`ChainPacking.lean` bound a family of pairwise disjoint connected cyclic regions with at most
`d` cut edges, outside a connected marker `P` and a deleted set `S`, if the graph outside
`P ∪ S` has girth at least `d / 2` and forest probability at least `2/5`. The girth is used in
one place only: two disjoint large sets with small cuts force forest probability less than
`2/5`.

This file has the same three statements for girth five, for a fixed `d`:

* `exists_block_bound`: two disjoint sets with at least `F(d)` vertices and at most `2 d` cut
  edges, outside a set `Q` whose complement has no cycle of length less than five, force forest
  probability less than `2/5`. The proof takes a component of large cycle rank in each set
  (`PieceExtraction.exists_component_rank`), its core (`PieceCore.exists_induced_core`), the
  pieces theorem `exists_affine_bound_girth_five`, and the product
  `PoleProduct.region_product`.
* `exists_row_bound`: the bound for a good row of the two-link matrix.
* `exists_base_packing`, `exists_base_finset_packing`: the family has at most
  `(3 d (d + |S| + 2) q + 6 d) 2^d` members, with `q = q(d)`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open FiniteMultiGraph Erdos1016.ExactMaximumSupport.LargeGirth
open Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
open Erdos1016.PolynomialBound.Separation Erdos1016.PolynomialBound.ParallelLinks
open Erdos1016.ExactMaximumSupport.Shortening
open Erdos1016.ExactMaximumSupport.Shortening.ChainPackingMoment
open Erdos1016.Probability.PoleMarker
open ExteriorComponents

local instance basePackingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Two blocks at girth five.** -/
theorem exists_block_bound (d : ℕ) :
    ∃ F : ℕ, ∀ (G : FiniteMultiGraph) (Q : Finset G.Vertex) (X : Fin 2 → Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      ¬ (Induced.graph G Qᶜ).HasCycleShorterThan 5 →
      Disjoint (X 0) (X 1) → (∀ i, Disjoint (X i) Q) →
      (∀ i, F ≤ (X i).card) → (∀ i, (G.cutEdges (X i)).card ≤ 2 * d) →
      G.regionForestProbability Qᶜ < 2 / 5 := by
  obtain ⟨F₀, hF₀⟩ := exists_affine_bound_girth_five (2 * d)
  refine ⟨8 * (F₀ + d + 2) ^ 2, ?_⟩
  intro G Q X hG hcubic hshort hdisj hclean hsize hcut
  have hsub : ∀ i, X i ⊆ Qᶜ := fun i v hv =>
    Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp (hclean i) hv h)
  have hpos : ∀ i, 0 < (X i).card := by
    intro i
    have h1 := hsize i
    have h2 : 0 < 8 * (F₀ + d + 2) ^ 2 := by positivity
    omega
  have hproper : ∀ i, X i ≠ Finset.univ := by
    intro i huniv
    have key : ∀ j, Disjoint (X j) (X i) → False := by
      intro j hd
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (hpos j)
      exact Finset.disjoint_left.mp hd hv (by rw [huniv]; exact Finset.mem_univ v)
    fin_cases i
    · exact key 1 hdisj.symm
    · exact key 0 hdisj
  have hcores : ∀ i : Fin 2, ∃ U : Finset G.Vertex, U ⊆ X i ∧
      (Induced.graph G U).toSimpleGraph.Connected ∧
      F₀ ≤ (Induced.graph G U).cycleRank ∧
      (∀ v, (Induced.graph G U).degree v ≤ 3) ∧
      ¬ (Induced.graph G U).HasCycleShorterThan 5 ∧
      (Induced.graph G U).cubicDeficit ≤ 2 * d := by
    intro i
    obtain ⟨c, hr⟩ := PieceExtraction.exists_component_rank G (X i) hG (hproper i)
      (fun v _ => hcubic v) (F₀ + d + 2) (by omega) (hsize i)
      (by have := hcut i; omega)
    obtain ⟨U, hU, hUc, hUr, hUd, hUg, hUb⟩ :=
      PieceCore.exists_induced_core G (vertices G (X i) c)
        (vertices_connected G (X i) c) (fun v _ => hcubic v) (by omega) 5 (by norm_num)
        (Induced.no_short_mono G Qᶜ (vertices G (X i) c)
          ((vertices_subset G (X i) c).trans (hsub i)) 5 (by norm_num) hshort)
    refine ⟨U, hU.trans (vertices_subset G (X i) c), hUc, by omega,
      fun v => (hUd v).2, hUg, ?_⟩
    exact (hUb.trans (Finset.card_le_card (cut_subset G (X i) c))).trans (hcut i)
  choose U hUX hUc hUr hUd hUg hUb using hcores
  have hlocal : ∀ i : Fin 2, ∀ b : (Induced.graph G (U i)).Demand,
      (∀ v, (Induced.graph G (U i)).degree v = 3 → b v = 0) →
      affineForestProbability (Induced.graph G (U i)) b ≤ (3 / 5 : ℝ) :=
    fun i => hF₀ (Induced.graph G (U i)) (hUc i) (hUd i) (hUg i) (hUr i) (hUb i)
  exact (PoleProduct.region_product G (fun v => (hcubic v).le) Q (U 0) (U 1)
    (Finset.disjoint_left.mpr (fun v h0 h1 =>
      Finset.disjoint_left.mp hdisj (hUX 0 h0) (hUX 1 h1)))
    ((hUX 0).trans (hsub 0)) ((hUX 1).trans (hsub 1)) (hlocal 0) (hlocal 1)).2

/-- **A good row at girth five.** -/
theorem exists_row_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ q : ℕ, ∀ (G : FiniteMultiGraph) {ι : Type} [Fintype ι]
      (U : ι → Finset G.Vertex) (P S : Finset G.Vertex) (p : G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → p ∈ P →
      ¬ (Induced.graph G (P ∪ S)ᶜ).HasCycleShorterThan 5 →
      (2 / 5 : ℝ) ≤ G.regionForestProbability (P ∪ S)ᶜ →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) →
      (∀ i, U i ⊆ (P ∪ S)ᶜ) →
      (∀ i, (G.cutEdges (U i)).card ≤ d) →
      ∀ (a : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
      ∀ i, (∑ j, goodTwoLink G U p i j * a j) ≤
        ((d * ((d + S.card + 2) * q) : ℕ) : ℝ) := by
  obtain ⟨F, hF⟩ := exists_block_bound d
  refine ⟨F + 1, ?_⟩
  intro G ι _ U P S p hG hcubic hP hp hshort hprob hdisj hconn hUP hcut a ha ha1 i
  classical
  by_contra hn
  have hrow : ((d * ((d + S.card + 2) * (F + 1)) : ℕ) : ℝ) <
      ∑ j, goodTwoLink G U p i j * a j := lt_of_not_ge hn
  have hpU (j : ι) : p ∉ U j := by
    intro hpj
    exact Finset.mem_compl.mp (hUP j hpj) (Finset.mem_union_left S hp)
  have hPU (j : ι) : Disjoint P (U j) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvU
    exact Finset.mem_compl.mp (hUP j hvU) (Finset.mem_union_left S hvP)
  have hsize (j : ι) : 1 ≤ (U j).card := by
    obtain ⟨v⟩ := (hconn j).nonempty
    exact Finset.card_pos.mpr ⟨v.1, Finset.mem_coe.mp v.2⟩
  obtain ⟨u, hu, Fam, _, hfamily, hlarge⟩ :=
    DisjointRegionChain.exists_separatorFamily_of_good_row G U p Finset.univ i a d
      ((d * ((d + S.card + 2) * (F + 1)) : ℕ) : ℝ) (fun j _ => hconn j) (fun j _ => hpU j)
      (fun j _ k _ hjk => hdisj hjk) (hcut i) (by omega)
      (fun j _ => ha j) (fun j _ => ha1 j) (by positivity) hrow
  have hdiv : ((d * ((d + S.card + 2) * (F + 1)) : ℕ) : ℝ) / d =
      ((d + S.card + 2) * (F + 1) : ℕ) := by
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      exact this.ne'
    push_cast
    field_simp
  have hlarge' : (d + S.card + 2) * (F + 1) < Fam.card := by
    rw [hdiv] at hlarge
    exact_mod_cast hlarge
  obtain ⟨X, J, hJ, hXd, hX⟩ := DisjointRegionChain.exists_clean_chain_blocks
    G (U i) P S u p Fam U (F + 1) (d + S.card + 2) 1 d hfamily
    (ChainPackingGeometry.cutOutside_not_mem G (U i) hu) hlarge'
    (isConnectedSet_of_induce hP) hp
    (hPU i) (fun j _ => hPU j) (fun j _ => hsize j) (fun j _ => hcut j)
  have htwo : 1 < J.card := by have := hcut i; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp htwo
  have hXj := hX j hj
  have hXk := hX k hk
  rw [Nat.add_sub_cancel, mul_one] at hXj hXk
  let Y : Fin 2 → Finset G.Vertex := fun l => if l = 0 then X j else X k
  have hY0 : Y 0 = X j := rfl
  have hY1 : Y 1 = X k := rfl
  have hY (l : Fin 2) : F ≤ (Y l).card ∧
      (G.cutEdges (Y l)).card ≤ 2 * d ∧ Disjoint (Y l) (P ∪ S) := by
    fin_cases l
    · exact hXj
    · exact hXk
  have hfail := hF G (P ∪ S) Y hG hcubic hshort (by rw [hY0, hY1]; exact hXd j k hjk)
    (fun l => (hY l).2.2) (fun l => (hY l).1) (fun l => (hY l).2.1)
  exact not_lt_of_ge hprob hfail

/-- **Packing at girth five.** -/
theorem exists_base_packing (d : ℕ) (hd : 2 ≤ d) :
    ∃ q : ℕ, ∀ (G : FiniteMultiGraph) {ι : Type} [Fintype ι]
      (U : ι → Finset G.Vertex) (P S : Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → P.Nonempty →
      ¬ (Induced.graph G (P ∪ S)ᶜ).HasCycleShorterThan 5 →
      (2 / 5 : ℝ) ≤ G.regionForestProbability (P ∪ S)ᶜ →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) →
      (∀ i, U i ⊆ (P ∪ S)ᶜ) →
      (∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0) →
      (∀ i, (G.cutEdges (U i)).card ≤ d) →
      Fintype.card ι ≤ (3 * (d * ((d + S.card + 2) * q)) + 6 * d) * 2 ^ d := by
  obtain ⟨q, hrows⟩ := exists_row_bound d hd
  refine ⟨q, ?_⟩
  intro G ι _ U P S hG hcubic hP hPne hshort hprob hdisj hconn hUP hcyc hcut
  classical
  obtain ⟨p, hp⟩ := hPne
  have hlower (i : ι) : 1 / (2 : ℝ) ^ d ≤ regionWeight G U i :=
    RegionEventLower.regionCycleEvent_probability_ge G (U i) (hcyc i) d (by omega) (hcut i)
  have hmass : (Fintype.card ι : ℝ) / (2 : ℝ) ^ d ≤ ∑ i, regionWeight G U i := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] using
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hlower i))
  by_cases hn : Fintype.card ι = 0
  · simp [hn]
  have hpos : 0 < ∑ i, regionWeight G U i := lt_of_lt_of_le
    (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (by positivity)) hmass
  have hpU (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) : p ∉ U i := by
    intro h
    exact Finset.mem_compl.mp (hUP i h) (Finset.mem_union_left S hp)
  have hE (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) :
      G.internalEdges (U i) ⊆ G.internalEdges (P ∪ S)ᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUP i hh.1, hUP i hh.2⟩
  obtain ⟨i, _, hrow⟩ := exists_good_row G U p Finset.univ d
    (G.internalEdges (P ∪ S)ᶜ) hG hdisj hconn hpU (by omega)
    (fun i _ => hcut i) hE
    (by simpa only [G.regionForestProbability_eq_density] using hprob) hpos
  have hupper := hrows G U P S p hG hcubic hP hp hshort hprob hdisj hconn hUP hcut
    (regionWeight G U) (regionWeight_nonneg G U) (regionWeight_le_one G U) i
  have hmassupper : (∑ i, regionWeight G U i) ≤
      ((3 * (d * ((d + S.card + 2) * q)) + 6 * d : ℕ) : ℝ) := by
    push_cast at hupper ⊢
    linarith
  have hc : (Fintype.card ι : ℝ) ≤
      ((3 * (d * ((d + S.card + 2) * q)) + 6 * d : ℕ) : ℝ) * (2 : ℝ) ^ d :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ d)).mp (hmass.trans hmassupper)
  exact_mod_cast hc

/-- The packing bound for a finite set of regions. -/
theorem exists_base_finset_packing (d : ℕ) (hd : 2 ≤ d) :
    ∃ q : ℕ, ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex)
      (F : Finset (Finset G.Vertex)),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → P.Nonempty →
      ¬ (Induced.graph G (P ∪ S)ᶜ).HasCycleShorterThan 5 →
      (2 / 5 : ℝ) ≤ G.regionForestProbability (P ∪ S)ᶜ →
      (∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → Disjoint X Y) →
      (∀ X ∈ F, (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected) →
      (∀ X ∈ F, X ⊆ (P ∪ S)ᶜ) →
      (∀ X ∈ F, ∃ z : G.internalCycleSpace X, z ≠ 0) →
      (∀ X ∈ F, (G.cutEdges X).card ≤ d) →
      F.card ≤ (3 * (d * ((d + S.card + 2) * q)) + 6 * d) * 2 ^ d := by
  obtain ⟨q, hbound⟩ := exists_base_packing d hd
  refine ⟨q, ?_⟩
  intro G P S F hG hcubic hP hPne hshort hprob hdisj hconn hUP hcyc hcut
  have hh := hbound G (fun X : F => X.1) P S hG hcubic hP hPne hshort hprob
    (fun X Y hne => hdisj X.1 X.2 Y.1 Y.2 (fun he => hne (Subtype.ext he)))
    (fun X => hconn X.1 X.2) (fun X => hUP X.1 X.2)
    (fun X => hcyc X.1 X.2) (fun X => hcut X.1 X.2)
  simpa only [Fintype.card_coe] using hh

end Erdos1016.ExactMaximum.GirthFive

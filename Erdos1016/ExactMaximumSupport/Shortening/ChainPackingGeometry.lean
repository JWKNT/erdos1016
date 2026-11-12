import Erdos1016.ExactMaximumSupport.Shortening.ChainPackingBounds
import Erdos1016.ExactMaximumSupport.Shortening.DisjointRegionChain

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A bound on good rows from actual separator-chain blocks

The family consists of arbitrary disjoint connected cyclic regions. No cycle
seed, upper region-size bound, quotient, or supplied interval model is used.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainPackingGeometry
open FiniteMultiGraph LargeGirth LargeGirth.PieceCore PolynomialBound.Separation
open PolynomialBound.ParallelLinks

local instance chainGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cutOutside_not_mem (G : FiniteMultiGraph) (A : Finset G.Vertex)
    {u : G.Vertex} (hu : u ∈ cutOutsideVertices G A) : u ∉ A := by
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
  rcases (Finset.mem_filter.mp he).2 with h | h
  · simpa only [if_pos h.1] using h.2
  · simpa only [if_neg h.1] using h.1

/-- The logarithmic pole estimate bounds every actual good partner row. -/
theorem exists_row_bound_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (G : FiniteMultiGraph) {ι : Type*} [Fintype ι]
      (U : ι → Finset G.Vertex) (P S : Finset G.Vertex) (g d : ℕ)
      (p : G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      4 ≤ g → 2 ≤ d → d ≤ 2*g →
      C*Real.logb 2 ((max d 4 : ℕ)+2) ≤ g →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → p ∈ P →
      ¬ (Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5 : ℝ) ≤ G.regionForestProbability (P∪S)ᶜ →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) →
      (∀ i, U i ⊆ (P∪S)ᶜ) →
      (∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0) →
      (∀ i, (G.cutEdges (U i)).card ≤ d) →
      ∀ (a : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
      ∀ i, (∑ j, goodTwoLink G U p i j * a j) ≤
        d*((d+S.card+2)*(16*d+1)) := by
  obtain ⟨C, hC, hbound⟩ := ChainPackingBounds.exists_block_obstruction_constant
  refine ⟨C, hC, ?_⟩
  intro G ι _ U P S g d p hG hcubic hg hd hdg hlog hP hp hshort hprob
    hdisj hconn hUP hcyc hcut a ha ha1 i
  classical
  by_contra hn
  have hrow : ((d*((d+S.card+2)*(16*d+1)) : ℕ) : ℝ) <
      ∑ j, goodTwoLink G U p i j * a j := by exact_mod_cast lt_of_not_ge hn
  have hpU (j : ι) : p ∉ U j := by
    intro hpj
    exact Finset.mem_compl.mp (hUP j hpj) (Finset.mem_union_left S hp)
  have hPU (j : ι) : Disjoint P (U j) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvU
    exact Finset.mem_compl.mp (hUP j hvU) (Finset.mem_union_left S hvP)
  have hsize (j : ι) : g ≤ (U j).card :=
    ChainPackingBounds.cyclic_region_card G (U j) g (by omega)
      (Induced.no_short_mono G (P∪S)ᶜ (U j) (hUP j) g (by omega) hshort) (hcyc j)
  obtain ⟨u, hu, F, _, hfamily, hlarge⟩ :=
    DisjointRegionChain.exists_separatorFamily_of_good_row G U p Finset.univ i a d
      ((d*((d+S.card+2)*(16*d+1)) : ℕ) : ℝ) (fun j _ => hconn j) (fun j _ => hpU j)
      (fun j _ k _ hjk => hdisj hjk) (hcut i) (by omega)
      (fun j _ => ha j) (fun j _ => ha1 j) (by positivity) hrow
  have hdiv : ((d*((d+S.card+2)*(16*d+1)) : ℕ) : ℝ) / d =
      ((d+S.card+2)*(16*d+1) : ℕ) := by
    push_cast
    field_simp
  have hlarge' : (d+S.card+2)*(16*d+1) < F.card := by
    rw [hdiv] at hlarge
    exact_mod_cast hlarge
  obtain ⟨X, J, hJ, hXd, hX⟩ := DisjointRegionChain.exists_clean_chain_blocks
    G (U i) P S u p F U (16*d+1) (d+S.card+2) g d hfamily
    (cutOutside_not_mem G (U i) hu) hlarge' (isConnectedSet_of_induce hP) hp
    (hPU i) (fun j _ => hPU j) (fun j _ => hsize j) (fun j _ => hcut j)
  have htwo : 1 < J.card := by have := hcut i; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp htwo
  let Y : Fin 2 → Finset G.Vertex := fun l => if l = 0 then X j else X k
  have hY (l : Fin 2) : 16*d*g ≤ (Y l).card ∧
      (G.cutEdges (Y l)).card ≤ 2*d ∧ Disjoint (Y l) (P∪S) := by
    fin_cases l <;> simp only [Y, ↓reduceIte, Fin.zero_eta, Fin.isValue]
    · simpa only [Nat.add_sub_cancel] using hX j hj
    · simpa only [Nat.add_sub_cancel] using hX k hk
  have hfail := hbound G P S g d Y hG hcubic hg hd hdg hlog hshort
    (by simpa [Y] using hXd j k hjk)
    (fun l => (hY l).2.2) (fun l => (hY l).1) (fun l => (hY l).2.1)
  exact not_lt_of_ge hprob hfail

end Erdos1016.ExactMaximumSupport.Shortening.ChainPackingGeometry

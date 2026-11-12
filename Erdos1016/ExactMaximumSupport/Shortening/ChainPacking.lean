import Erdos1016.ExactMaximumSupport.Shortening.ChainPackingGeometry
import Erdos1016.ExactMaximumSupport.Shortening.ChainPackingMoment
import Erdos1016.ExactMaximumSupport.Shortening.RegionEventLower
import Erdos1016.ExactMaximumSupport.Shortening.ChainPackingCutoff

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Packing by the two-link moment and separator chains

The family consists of actual disjoint cyclic regions outside a nonempty
connected marker and an arbitrary deleted set. Both the probability law and
the separator blocks are derived from the graph; no packing estimate is an input.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainPacking
open FiniteMultiGraph LargeGirth LargeGirth.PieceCore ChainPackingMoment

local instance chainPackingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem exists_logarithmic_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ (G : FiniteMultiGraph) {ι : Type*} [Fintype ι]
      (U : ι → Finset G.Vertex) (P S : Finset G.Vertex) (g d : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      4 ≤ g → 2 ≤ d → d ≤ 2*g →
      C*Real.logb 2 ((max d 4 : ℕ)+2) ≤ g →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → P.Nonempty →
      ¬ (Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5 : ℝ) ≤ G.regionForestProbability (P∪S)ᶜ →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) →
      (∀ i, U i ⊆ (P∪S)ᶜ) →
      (∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0) →
      (∀ i, (G.cutEdges (U i)).card ≤ d) →
      Fintype.card ι ≤ 150*d^3*(S.card+1)*2^d := by
  obtain ⟨C, hC, hrows⟩ := ChainPackingGeometry.exists_row_bound_constant
  refine ⟨C, hC, ?_⟩
  intro G ι _ U P S g d hG hcubic hg hd hdg hlog hP hPne hshort hprob
    hdisj hconn hUP hcyc hcut
  classical
  obtain ⟨p, hp⟩ := hPne
  have hlower (i : ι) : 1/(2:ℝ)^d ≤ regionWeight G U i :=
    RegionEventLower.regionCycleEvent_probability_ge G (U i) (hcyc i) d (by omega) (hcut i)
  have hmass : (Fintype.card ι : ℝ)/(2:ℝ)^d ≤ ∑ i, regionWeight G U i := by
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
      G.internalEdges (U i) ⊆ G.internalEdges (P∪S)ᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUP i hh.1, hUP i hh.2⟩
  obtain ⟨i, _, hrow⟩ := exists_good_row G U p Finset.univ d
    (G.internalEdges (P∪S)ᶜ) hG hdisj hconn hpU (by omega)
    (fun i _ => hcut i) hE
    (by simpa only [G.regionForestProbability_eq_density] using hprob) hpos
  have hupper := hrows G U P S g d p hG hcubic hg hd hdg hlog hP hp hshort
    hprob hdisj hconn hUP hcyc hcut (regionWeight G U)
    (regionWeight_nonneg G U) (regionWeight_le_one G U) i
  have hscalar : ((3*d*((d+S.card+2)*(16*d+1))+6*d : ℕ) : ℝ) ≤
      150*(d:ℝ)^3*(S.card+1) := by
    exact_mod_cast ChainPackingBounds.packing_constant d S.card hd
  have hmassupper : (∑ i, regionWeight G U i) ≤ 150*(d:ℝ)^3*(S.card+1) := by
    push_cast at hscalar
    linarith
  have hc : (Fintype.card ι : ℝ) ≤ 150*(d:ℝ)^3*(S.card+1)*(2:ℝ)^d :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2^d)).mp (hmass.trans hmassupper)
  exact_mod_cast hc

/-- Uniform actual-region packing bound. The marker is explicitly nonempty
and connected, as required for the separator-chain anchor. -/
theorem exists_cutoff :
    ∃ D : ℕ, 256 ≤ D ∧
    ∀ (G : FiniteMultiGraph) {ι : Type*} [Fintype ι]
      (U : ι → Finset G.Vertex) (P S : Finset G.Vertex) (g d : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      D ≤ g → 2 ≤ d → d ≤ 2*g →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → P.Nonempty →
      ¬ (Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5 : ℝ) ≤ G.regionForestProbability (P∪S)ᶜ →
      Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected) →
      (∀ i, U i ⊆ (P∪S)ᶜ) →
      (∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0) →
      (∀ i, (G.cutEdges (U i)).card ≤ d) →
      Fintype.card ι ≤ 150*d^3*(S.card+1)*2^d := by
  obtain ⟨C, hC, hbound⟩ := exists_logarithmic_bound
  obtain ⟨D, hD, hlog⟩ := ChainPackingCutoff.exists_cutoff C hC.le
  refine ⟨D, hD, ?_⟩
  intro G ι _ U P S g d hG hcubic hg hd hdg
  exact hbound G U P S g d hG hcubic (by omega) hd hdg (hlog g d hg hdg)

/-- Finite-set form for the recursively selected high-girth packing. -/
theorem exists_finset_cutoff :
    ∃ D : ℕ, 256 ≤ D ∧
    ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex) (g d : ℕ)
      (F : Finset (Finset G.Vertex)),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      D ≤ g → 2 ≤ d → d ≤ 2*g →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected → P.Nonempty →
      ¬ (Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      (2/5 : ℝ) ≤ G.regionForestProbability (P∪S)ᶜ →
      (∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → Disjoint X Y) →
      (∀ X ∈ F, (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected) →
      (∀ X ∈ F, X ⊆ (P∪S)ᶜ) →
      (∀ X ∈ F, ∃ z : G.internalCycleSpace X, z ≠ 0) →
      (∀ X ∈ F, (G.cutEdges X).card ≤ d) →
      F.card ≤ 150*d^3*(S.card+1)*2^d := by
  obtain ⟨D, hD, hbound⟩ := exists_cutoff
  refine ⟨D, hD, ?_⟩
  intro G P S g d F hG hcubic hg hd hdg hP hPne hshort hprob hdisj hconn hUP hcyc hcut
  have hh := hbound G (fun X : F => X.1) P S g d hG hcubic hg hd hdg hP hPne hshort hprob
    (fun X Y hne => hdisj X.1 X.2 Y.1 Y.2 (fun he => hne (Subtype.ext he)))
    (fun X => hconn X.1 X.2) (fun X => hUP X.1 X.2)
    (fun X => hcyc X.1 X.2) (fun X => hcut X.1 X.2)
  simpa only [Fintype.card_coe] using hh

end Erdos1016.ExactMaximumSupport.Shortening.ChainPacking

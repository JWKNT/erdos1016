import Erdos1016.ExactMaximumSupport.LargeGirth.CycleSupply
import Erdos1016.ExactMaximumSupport.LargeGirth.ChainSelection
import Erdos1016.Probability.Moments.InducedCycleAvoidance

set_option autoImplicit false

/-!
# Separators from the actual retained cycles

The family here contains every retained physical cycle through the length cutoff.
Its ambient seeds, weights, supports, and vertex loads come from existing graph transport theorems.
No abstract cycle family or geometric mass assumption is substituted for these objects.
The link envelope and finite numerical budgets remain explicit hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.RetainedCycleSelection

open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open FiniteMultiGraph.SeedFamilyAvoidance FiniteMultiGraph.SeedPairCorrelation
open BoundaryDecay BoundaryTrace Nonbacktracking
open Proof Proof.LengthIndexedFamily Proof.SimpleRunWeight
open PolynomialBound.Separation

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

local notation "H" => graph G R hloop hsimple
local notation "U" => InducedCycleAvoidance.region G R hloop hsimple
local notation "seed" => InducedCycleAvoidance.seed G R hloop hsimple

/-- The ambient seed mass is exactly the retained cycle mass. -/
theorem total_seed_weight (L : ℕ) :
    (∑ i ∈ LengthIndexedFamily.family H L, weight G U seed i) =
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength H ell := by
  simp only [InducedCycleAvoidance.weight_eq]
  exact LengthIndexedFamily.total_weight H L

/-- Each retained cycle has the same physical length after ambient transport. -/
theorem region_card_le (L : ℕ) (i : LengthIndexedFamily.Index H)
    (hi : i ∈ LengthIndexedFamily.family H L) : (U i).card ≤ L := by
  change (cycleRegion G R hloop hsimple (LengthIndexedFamily.cycle H i)).card ≤ L
  rw [cycleRegion_card, LengthIndexedFamily.cycle_length]
  exact (LengthIndexedFamily.mem_family_iff H L i).mp hi |>.2

/-- All seed geometry and loads are derived from the actual retained graph.
The probability hypothesis concerns the actual ambient uniform cycle space. -/
theorem exists_separatorFamily_of_mass
    (p : G.Vertex) (hp : p ∉ R)
    (hG : G.toSimpleGraph.Connected) (hmax : ∀ v, G.degree v ≤ 3)
    (D L s : ℕ) (M : ℝ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (hM : 0 ≤ M)
    (hlinks : ∀ C C' : (H).CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length C' ≤ L → C ≠ C' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') →
      dyadic ((Nat.card (Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple C')) : ℤ) - 1) ≤ M)
    (E : Finset G.Edge) (hE : G.internalEdges R ⊆ E)
    (hforest : (2 / 5 : ℝ) ≤
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)))
    (hjoined : (L : ℝ) * ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) ≤ 1 / 2)
    (hmass : 30 < ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength H ell)
    (hη : M * L * L * ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) ≤ 1 / 2) :
    ∃ i ∈ LengthIndexedFamily.family H L,
      ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ LengthIndexedFamily.family H L,
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      (8 : ℝ) / L < (F.card : ℝ) * L * ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) := by
  classical
  have hHmax := max_degree_three G R hloop hsimple hmax
  have hlen := region_card_le G R hloop hsimple L
  have hmass' : 30 < ∑ i ∈ LengthIndexedFamily.family H L, weight G U seed i := by
    rw [total_seed_weight]
    exact hmass
  apply LargeGirth.exists_separatorFamily_of_forest G U p (LengthIndexedFamily.family H L)
    seed L M ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) E hG
    (fun i _ => cycleSeed_connected G R hloop hsimple (LengthIndexedFamily.cycle H i))
    (fun i _ hpi => hp (cycleRegion_subset G R hloop hsimple _ hpi))
    (fun i _ => cycleSeed_degree G R hloop hsimple (LengthIndexedFamily.cycle H i))
    (fun _ _ v _ => hmax v)
    (fun i _ j _ he => LengthIndexedFamily.cycle_injective H
      (cycleSeed_injective G R hloop hsimple he))
    hlen hM (by positivity)
    (InducedCycleAvoidance.vertex_load_le G R hloop hsimple hHmax D L s hg hs hshort)
    ?_ ?_ hforest hjoined hmass' hη
  · intro i hi j hj hij he
    apply hlinks
    · rw [LengthIndexedFamily.cycle_length]
      exact (LengthIndexedFamily.mem_family_iff H L i).mp hi |>.2
    · rw [LengthIndexedFamily.cycle_length]
      exact (LengthIndexedFamily.mem_family_iff H L j).mp hj |>.2
    · exact fun hh => hij (LengthIndexedFamily.cycle_injective H hh)
    · exact he.1
  · intro i _ e he
    apply hE
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      cycleRegion_subset G R hloop hsimple _ he'.2.1,
      cycleRegion_subset G R hloop hsimple _ he'.2.2⟩

/-- Explicit finite trace budgets supply the mass in the preceding graph theorem. -/
theorem exists_separatorFamily_of_supply
    (p : G.Vertex) (hp : p ∉ R)
    (hG : G.toSimpleGraph.Connected) (hmax : ∀ v, G.degree v ≤ 3)
    (M K s D : ℕ) (B : ℝ) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hn : 0 < (H).vertexCount) (hd : degreeDeficit H < (H).vertexCount)
    (hmain : degreeDeficit H * (K : ℝ) / (H).vertexCount ≤ 1 / 200)
    (herr : 3 * ((H).vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 200)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (hcollision : (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 100)
    (hlog : 123 ≤ Real.log ((K + 1 : ℕ) / (M : ℝ)))
    (hB : 0 ≤ B)
    (hlinks : ∀ C C' : (H).CycleWord,
      BoundaryDecay.Cycle.length C ≤ 2 * K → BoundaryDecay.Cycle.length C' ≤ 2 * K → C ≠ C' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') →
      dyadic ((Nat.card (Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple C')) : ℤ) - 1) ≤ B)
    (E : Finset G.Edge) (hE : G.internalEdges R ⊆ E)
    (hforest : (2 / 5 : ℝ) ≤
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)))
    (hjoined : ((2 * K : ℕ) : ℝ) *
      ((3 / 2 : ℝ) * (2 * K : ℕ) * (1 / 2 : ℝ) ^ s) ≤ 1 / 2)
    (hη : B * (2 * K : ℕ) * (2 * K : ℕ) *
      ((3 / 2 : ℝ) * (2 * K : ℕ) * (1 / 2 : ℝ) ^ s) ≤ 1 / 2) :
    ∃ i ∈ LengthIndexedFamily.family H (2 * K),
      ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ LengthIndexedFamily.family H (2 * K),
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      (8 : ℝ) / (2 * K : ℕ) < (F.card : ℝ) * (2 * K : ℕ) *
        ((3 / 2 : ℝ) * (2 * K : ℕ) * (1 / 2 : ℝ) ^ s) := by
  have hmass := CycleSupply.cycleWordMass_gt_thirty H
    (max_degree_three G R hloop hsimple hmax) hn hd M K s D hM hMK
    hmain herr hg hshort hs hcollision hlog
  exact exists_separatorFamily_of_mass G R hloop hsimple p hp hG hmax D (2 * K) s B
    hg hs hshort hB hlinks E hE hforest hjoined hmass hη

end Erdos1016.ExactMaximumSupport.LargeGirth.RetainedCycleSelection

import Erdos1016.ExactMaximumSupport.LargeGirth.RetainedCycleSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.LinkBound
import Erdos1016.Cycles.Selection.RetainedHighGirth

set_option autoImplicit false

/-!
# Actual packing-to-separator adapter

A family that hits all short cyclic regions gives the retained girth and link bound.
This file converts that link count into the dyadic second-moment envelope.
It then applies the actual retained-cycle separator theorem.
The cycle mass and finite numerical budgets remain explicit.
No packing cardinality bound is assumed or proved here.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingCycleSelection

open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open FiniteMultiGraph.ExteriorComponents FiniteMultiGraph.SeedPairCorrelation
open BoundaryDecay BoundaryTrace Nonbacktracking
open Proof Proof.SimpleRunWeight PolynomialBound.Separation

/-- The proved real link-count ceiling, before exponentiation. -/
def linkExponent (G : FiniteMultiGraph) (P : Finset G.Vertex) (D t L : ℕ) : ℝ :=
  (Fintype.card (Component G P) : ℝ) + 2 * L / (t + 1) +
    (3 * (2 : ℝ) ^ t + 1) + 578 * ((L : ℝ) / D) ^ 2

/-- The correlation exponent is one less than the number of links. -/
theorem dyadic_card_sub_one_le_rpow (n : ℕ) (B : ℝ) (hn : (n : ℝ) ≤ B) :
    dyadic ((n : ℤ) - 1) ≤ (2 : ℝ) ^ B := by
  unfold dyadic
  rw [← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

variable (G : FiniteMultiGraph) (P : Finset G.Vertex) (Q : Finset (Finset G.Vertex))
  (hloop : ∀ e ∈ G.internalEdges (P ∪ Q.biUnion id)ᶜ, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges (P ∪ Q.biUnion id)ᶜ,
    ∀ f ∈ G.internalEdges (P ∪ Q.biUnion id)ᶜ,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

local notation "R" => (P ∪ Q.biUnion id)ᶜ
local notation "J" => graph G R hloop hsimple
local notation "U" => InducedCycleAvoidance.region G R hloop hsimple

/-- The envelope follows from the actual short-region family and forest event. -/
theorem cycle_linkFactor_le
    (D t L : ℕ) (C C' : (J).CycleWord)
    (hdisjoint : Disjoint (cycleRegion G R hloop hsimple C)
      (cycleRegion G R hloop hsimple C'))
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (hQ : ∀ A ∈ Q, G.ShortCyclicRegion P D A)
    (hhit : ∀ A, G.ShortCyclicRegion P D A → (Q.biUnion id ∩ A).Nonempty)
    (hD : 8 ≤ D) (hDL : D ≤ L) (ht : 1 ≤ t)
    (hbudget : 2 * (t + 2 * (D / 8)) ≤ D)
    (hL : BoundaryDecay.Cycle.length C ≤ L)
    (hL' : BoundaryDecay.Cycle.length C' ≤ L)
    (hG : G.toSimpleGraph.Connected)
    (hforest : (2 / 5 : ℝ) ≤ G.regionForestProbability Pᶜ) :
    dyadic ((Nat.card (Links G (cycleRegion G R hloop hsimple C)
      (cycleRegion G R hloop hsimple C')) : ℤ) - 1) ≤
        (2 : ℝ) ^ linkExponent G P D t L := by
  have hd : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C') := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact Finset.disjoint_left.mp hdisjoint
      ((mem_cycleRegion_vertex G R hloop hsimple C v).mpr hv)
      ((mem_cycleRegion_vertex G R hloop hsimple C' v).mpr hv')
  apply dyadic_card_sub_one_le_rpow
  exact LinkBound.cycle_links_le G P Q D t L hloop hsimple C C' hd hmax hcubic
    hQ hhit hD hDL ht hbudget hL hL' hG hforest

/-- A hitting family, finite mass, and the proved link ceiling give actual separators. -/
theorem exists_separatorFamily
    (p : G.Vertex) (hp : p ∈ P)
    (hG : G.toSimpleGraph.Connected)
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (D t L s : ℕ)
    (hQ : ∀ A ∈ Q, G.ShortCyclicRegion P D A)
    (hhit : ∀ A, G.ShortCyclicRegion P D A → (Q.biUnion id ∩ A).Nonempty)
    (hD : 8 ≤ D) (hDL : D ≤ L) (ht : 1 ≤ t)
    (hbudget : 2 * (t + 2 * (D / 8)) ≤ D)
    (hs : 0 < s) (hshort : 2 * s ≤ D)
    (hforest : (2 / 5 : ℝ) ≤ G.regionForestProbability Pᶜ)
    (hjoined : (L : ℝ) * ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) ≤ 1 / 2)
    (hmass : 30 < ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength J ell)
    (hη : (2 : ℝ) ^ linkExponent G P D t L * L * L *
      ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) ≤ 1 / 2) :
    ∃ i ∈ LengthIndexedFamily.family J L,
      ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ LengthIndexedFamily.family J L,
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      (8 : ℝ) / L < (F.card : ℝ) * L * ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) := by
  classical
  have hpR : p ∉ R := by
    intro h
    exact (Finset.mem_compl.mp h) (Finset.mem_union_left _ hp)
  have hg := G.retained_girth P (Q.biUnion id) D hloop hsimple hmax hhit
  have hE : G.internalEdges R ⊆ G.internalEdges Pᶜ := by
    intro e he
    have hh := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact Finset.mem_compl.mpr fun hv =>
        (Finset.mem_compl.mp hh.2.1) (Finset.mem_union_left _ hv)
    · exact Finset.mem_compl.mpr fun hv =>
        (Finset.mem_compl.mp hh.2.2) (Finset.mem_union_left _ hv)
  have hforest' := hforest
  rw [G.regionForestProbability_eq_density] at hforest'
  apply RetainedCycleSelection.exists_separatorFamily_of_mass G R hloop hsimple p hpR hG hmax
    D L s ((2 : ℝ) ^ linkExponent G P D t L) hg hs hshort (by positivity)
    ?_ (G.internalEdges Pᶜ) hE hforest' hjoined hmass hη
  intro C C' hC hC' _ hdisjoint
  exact cycle_linkFactor_le G P Q hloop hsimple D t L C C' hdisjoint hmax hcubic
    hQ hhit hD hDL ht hbudget hC hC' hG hforest

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingCycleSelection

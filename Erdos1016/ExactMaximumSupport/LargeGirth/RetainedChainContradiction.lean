import Erdos1016.ExactMaximumSupport.LargeGirth.RetainedCycleSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.ChainContradiction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual retained cycles give the finite large-girth contradiction

The cycle family, separator chain, seeds, and clean blocks are constructed.
Only the finite scalar budgets and actual retained-graph girth are inputs.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.RetainedChainContradiction
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open FiniteMultiGraph.SeedPairCorrelation BoundaryDecay BoundaryTrace
open Nonbacktracking Proof Proof.SimpleRunWeight PolynomialBound.Separation
local instance retainedContradictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def constant : ℝ := Classical.choose ChainContradiction.exists_constant.{0}

theorem constant_pos : 0<constant := (Classical.choose_spec ChainContradiction.exists_constant.{0}).1

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀e∈G.internalEdges R,G.src e≠G.dst e)
  (hsimple : ∀e∈G.internalEdges R,∀f∈G.internalEdges R,
    ((G.src e=G.src f ∧ G.dst e=G.dst f) ∨ (G.src e=G.dst f ∧ G.dst e=G.src f))→e=f)

local notation "H" => graph G R hloop hsimple
local notation "U" => InducedCycleAvoidance.region G R hloop hsimple
local notation "seed" => InducedCycleAvoidance.seed G R hloop hsimple

theorem region_card_gt (D : ℕ) (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (i : LengthIndexedFamily.Index H) : D<(U i).card := by
  rw [InducedCycleAvoidance.region,cycleRegion_card]
  exact LowDegreeVertexMass.cycle_length_gt_of_girth H D hg (LengthIndexedFamily.cycle H i)

/-- This finite theorem constructs the entire separator-chain contradiction
from the literal cycle mass of the retained graph. -/
theorem bound_of_mass (P S : Finset G.Vertex) (p : G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀v,G.degree v=3)
    (hP : (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) (hp : p∈P)
    (hRP : R⊆Pᶜ) (D L s w g : ℕ) (M : ℝ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hL : 4≤L) (hs : 0<s) (hshort : 2*s≤D) (hM : 0≤M)
    (hlinks : ∀C C' : (H).CycleWord,
      BoundaryDecay.Cycle.length C≤L → BoundaryDecay.Cycle.length C'≤L → C≠C' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') →
      dyadic ((Nat.card (Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple C')) : ℤ)-1)≤M)
    (hforest : (2/5:ℝ)≤G.regionForestProbability Pᶜ)
    (hjoined : (L:ℝ)*((3/2:ℝ)*L*(1/2:ℝ)^s)≤1/2)
    (hmass : 30<∑ell∈Finset.Icc 1 L,cycleWordMassAtLength H ell)
    (hη : M*L*L*((3/2:ℝ)*L*(1/2:ℝ)^s)≤1/2)
    (hchain : (((L+S.card+2)*w : ℕ):ℝ)*(3/2:ℝ)*(L:ℝ)^3*(1/2:ℝ)^s≤8)
    (hwidth : 8*L^2≤(w-1)*(D+1)) (hgsmall : 3≤g)
    (hlog : constant*Real.logb 2 ((L:ℝ)+2)≤g)
    (hsmall : ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g) :
    G.regionForestProbability Pᶜ≤9/25 ∧ G.regionForestProbability Pᶜ<2/5 := by
  have hpR : p∉R := fun hm => (Finset.mem_compl.mp (hRP hm)) hp
  have hE : G.internalEdges R⊆G.internalEdges Pᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hRP hh.1,hRP hh.2⟩
  have hprob := hforest
  rw [G.regionForestProbability_eq_density] at hprob
  obtain ⟨i,hi,u,hu,F,hF,hfamily,hweight⟩ :=
    RetainedCycleSelection.exists_separatorFamily_of_mass G R hloop hsimple p hpR hG
      (fun v=>(hcubic v).le) D L s M hg hs hshort hM hlinks
      (G.internalEdges Pᶜ) hE hprob hjoined hmass hη
  have hlen := RetainedCycleSelection.region_card_le G R hloop hsimple L
  have hPU (j : LengthIndexedFamily.Index H) : Disjoint P (U j) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvU
    exact (Finset.mem_compl.mp (hRP (cycleRegion_subset G R hloop hsimple _ hvU))) hvP
  have hcut : (G.cutEdges (U i)).card≤L := by
    apply (G.cutEdges_card_le_of_two_regular (U i) (seed i).1.1
      (cycleSeed_degree G R hloop hsimple _) (seed i).2 (fun v _=>(hcubic v).le)).trans
    exact hlen i hi
  apply (Classical.choose_spec ChainContradiction.exists_constant.{0}).2 G (U i) P S u p F U
    (fun j=>(seed j).1.1) w (D+1) L g hG hcubic hfamily ?_
    (PolynomialBound.ParallelLinks.isConnectedSet_of_induce hP) hp (hPU i)
    (fun j _=>hPU j) ?_ (fun j hj=>hlen j (hF hj))
    (fun j _=>cycleSeed_degree G R hloop hsimple _)
    (fun j _=>(seed j).2) hcut ?_ hwidth hL hgsmall hlog hsmall
  · intro huA
    obtain ⟨e,he,heu⟩ := Finset.mem_image.mp hu
    rcases (Finset.mem_filter.mp he).2 with he | he
    · rw [if_pos he.1] at heu
      exact he.2 (heu.symm ▸ huA)
    · rw [if_neg he.1] at heu
      exact he.1 (heu.symm ▸ huA)
  · intro j _
    exact region_card_gt G R hloop hsimple D hg j
  · exact ChainContradiction.chain_card_of_weight F.card ((L+S.card+2)*w) L s
      (by omega) hweight hchain

end Erdos1016.ExactMaximumSupport.LargeGirth.RetainedChainContradiction

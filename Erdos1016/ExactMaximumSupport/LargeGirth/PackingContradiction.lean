import Erdos1016.ExactMaximumSupport.LargeGirth.PackingCycleSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.RetainedChainContradiction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The finite contradiction from actual raised-girth packings

Maximality supplies retained simplicity, girth, and link bounds. The finite
trace budgets supply the actual cycle mass. The clean-chain theorem finishes
the graph argument. Eventual scalar choices remain a separate theorem.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingContradiction
open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open Nonbacktracking Proof Proof.SimpleRunWeight
local instance packingContradictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem component_card_eq_one (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hP : (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) :
    Fintype.card (ExteriorComponents.Component G P)=1 := by
  letI : Subsingleton (ExteriorComponents.Component G P) := hP.preconnected.subsingleton_connectedComponent
  obtain ⟨p⟩ := hP.nonempty
  exact Fintype.card_eq_one_iff.mpr
    ⟨(ExteriorComponents.graph G P).connectedComponentMk p,fun _ => Subsingleton.elim _ _⟩

theorem linkExponent_eq (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hP : (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) (D t L : ℕ) :
    PackingCycleSelection.linkExponent G P D t L =
      1+2*(L:ℝ)/(t+1)+(3*(2:ℝ)^t+1)+578*((L:ℝ)/D)^2 := by
  rw [PackingCycleSelection.linkExponent,component_card_eq_one G P hP,Nat.cast_one]

variable (G : FiniteMultiGraph) (P S : Finset G.Vertex) (Q : Finset (Finset G.Vertex))
local notation "R" => (P∪Q.biUnion id)ᶜ

/-- All remaining hypotheses are actual graph assumptions or finite scalar
inequalities. Neither a cycle supply nor a separator family is assumed. -/
theorem bound_of_budgets (D t M K s w g : ℕ)
    (hG : G.toSimpleGraph.Connected) (hcubic : ∀v,G.degree v=3)
    (hP : (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected)
    (hQ : ∀U∈Q,G.ShortCyclicRegion P D U)
    (hhit : ∀U,G.ShortCyclicRegion P D U→(Q.biUnion id∩U).Nonempty)
    (hD : 8≤D) (hDL : D≤2*K) (ht : 1≤t) (hlink : 2*(t+2*(D/8))≤D)
    (hforest : (2/5:ℝ)≤G.regionForestProbability Pᶜ)
    (hM : 0<M) (hMK : M≤K+1) (hL : 4≤2*K) (hs : 0<s) (hshort : 2*s≤D)
    (hn : 0<(R).card) (hd : 3*((P∪Q.biUnion id).card:ℝ)<(R).card)
    (hmain : 3*((P∪Q.biUnion id).card:ℝ)*(K:ℝ)/(R).card≤1/200)
    (herr : 3*((R).card:ℝ)/(2:ℝ)^M≤1/200)
    (hcollision : (9/4:ℝ)*((2*K:ℕ):ℝ)^2*(1/2:ℝ)^s≤1/100)
    (hlogratio : 123≤Real.log ((K+1:ℕ)/(M:ℝ)))
    (hjoined : ((2*K:ℕ):ℝ)*((3/2:ℝ)*(2*K:ℕ)*(1/2:ℝ)^s)≤1/2)
    (hη : (2:ℝ)^(1+2*((2*K:ℕ):ℝ)/(t+1)+(3*(2:ℝ)^t+1)+
      578*(((2*K:ℕ):ℝ)/D)^2)*(2*K:ℕ)*(2*K:ℕ)*
        ((3/2:ℝ)*(2*K:ℕ)*(1/2:ℝ)^s)≤1/2)
    (hchain : (((2*K+S.card+2)*w:ℕ):ℝ)*(3/2:ℝ)*((2*K:ℕ):ℝ)^3*(1/2:ℝ)^s≤8)
    (hwidth : 8*(2*K)^2≤(w-1)*(D+1)) (hg : 3≤g)
    (hlogg : RetainedChainContradiction.constant*Real.logb 2 (((2*K:ℕ):ℝ)+2)≤g)
    (hsmall : ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g) :
    G.regionForestProbability Pᶜ≤9/25 ∧ G.regionForestProbability Pᶜ<2/5 := by
  have hmax (v : G.Vertex) : G.degree v≤3 := (hcubic v).le
  have hloop := G.retained_no_loops P (Q.biUnion id) D (by omega) hmax hhit
  have hsimple := G.retained_simple P (Q.biUnion id) D (by omega) hmax hhit
  have hret := G.retained_girth P (Q.biUnion id) D hloop hsimple hmax hhit
  let H := graph G R hloop hsimple
  have hmass : 30<∑ell∈Finset.Icc 1 (2*K),cycleWordMassAtLength H ell := by
    apply CycleSupply.retained_cycleWordMass_gt_thirty G P (Q.biUnion id) hloop hsimple
      hmax (fun v _=>hcubic v) M K s D hM hMK
    · simpa only [graph_vertexCount] using hn
    · simpa only [graph_vertexCount] using hd
    · simpa only [graph_vertexCount] using hmain
    · simpa only [graph_vertexCount] using herr
    · exact hret
    · exact hshort
    · exact hs
    · exact hcollision
    · exact hlogratio
  obtain ⟨p⟩ := hP.nonempty
  apply RetainedChainContradiction.bound_of_mass G R hloop hsimple P S p.1 hG hcubic hP p.2
    (by intro v hv; exact Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp hv) (Finset.mem_union_left _ h)))
    D (2*K) s w g ((2:ℝ)^PackingCycleSelection.linkExponent G P D t (2*K))
    hret hL hs hshort (by positivity) ?_ hforest hjoined hmass ?_ hchain hwidth hg hlogg hsmall
  · intro C C' hC hC' _ hdisj
    exact PackingCycleSelection.cycle_linkFactor_le G P Q hloop hsimple D t (2*K)
      C C' hdisj hmax (fun v _=>hcubic v) hQ hhit hD hDL ht hlink hC hC' hG hforest
  · simpa only [linkExponent_eq G P hP D t (2*K)] using hη

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingContradiction

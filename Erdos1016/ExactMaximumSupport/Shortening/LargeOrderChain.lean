import Erdos1016.ExactMaximumSupport.Shortening.LargeOrderPieces
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingContradiction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The finite chain contradiction using only large-order pieces

These actual graph assemblies use the logarithmic large-order regime alone.
The existing cycle selection, physical block geometry and numerical helpers
are retained. Neither fixed-rank pieces nor their old chain constants enter
any of the public proofs below.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.LargeOrderChain
open LargeGirth FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open FiniteMultiGraph.SeedPairCorrelation BoundaryDecay BoundaryTrace
open Nonbacktracking Proof Proof.SimpleRunWeight PolynomialBound.Separation
local instance largeOrderChainDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The clean-block argument yields the actual two-piece probability bound. -/
theorem exists_constant :
    ∃ C : ℝ,0<C ∧
    ∀ {ι : Type*} [DecidableEq ι] (G : FiniteMultiGraph)
      (A P S : Finset G.Vertex) (u p : G.Vertex) (F : Finset ι)
      (U : ι→Finset G.Vertex) (seed : ι→G.EdgeWord) (w d L g : ℕ),
      G.toSimpleGraph.Connected → (∀v,G.degree v=3) →
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑A)) u p F (fun i => ↑(U i)) →
      u∉A → IsConnectedSet G.toSimpleGraph (↑P) → p∈P →
      Disjoint P A → (∀i∈F,Disjoint P (U i)) →
      (∀i∈F,d≤(U i).card) → (∀i∈F,(U i).card≤L) →
      (∀i∈F,∀v∈U i,G.selectedDegree (seed i) v=2) →
      (∀i∈F,∀e,e∉G.internalEdges (U i)→seed i e=0) →
      (G.cutEdges A).card≤L → (L+S.card+2)*w<F.card →
      8*L^2≤(w-1)*d → 4≤L → 3≤g →
      C*Real.logb 2 ((L:ℝ)+2)≤g →
      ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      G.regionForestProbability Pᶜ≤9/25 ∧ G.regionForestProbability Pᶜ<2/5 := by
  obtain ⟨C,hC,hpieces⟩ := LargeOrderPieces.exists_constant
  refine ⟨C,hC,?_⟩
  intro ι _ G A P S u p F U seed w d L g hG hcubic hf hu hP hp hPA hPU
    hsize hlen htwo hsupp hcut hchain hwidth hL hg hlog hshort
  obtain ⟨X,J,hcount,hdisj,hclean⟩ := exists_clean_chain_blocks G A P S u p F U seed
    w (L+S.card+2) d L hf hu hchain hP hp hPA hPU hsize hlen htwo hsupp
    (fun v => (hcubic v).le)
  have hJ : 1<J.card := by omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hJ
  let Y : Fin 2→Finset G.Vertex := fun a => if a=0 then X i else X j
  have hy (a : Fin 2) : 8*L^2≤(Y a).card ∧
      (G.cutEdges (Y a)).card≤2*L ∧ Disjoint (Y a) (P∪S) := by
    fin_cases a <;> simp only [Y,Fin.isValue,Fin.zero_eta,↓reduceIte]
    · exact ⟨hwidth.trans (hclean i hi).1,(hclean i hi).2⟩
    · exact ⟨hwidth.trans (hclean j hj).1,(hclean j hj).2⟩
  have hsub (a : Fin 2) : Y a⊆(P∪S)ᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp (hy a).2.2 hv hm)
  apply hpieces G P Y (fun _=>g) hG hcubic ?_ ?_ ?_ ?_
  · simpa [Y] using hdisj i j hij
  · intro a v hv
    exact Finset.mem_compl.mpr (fun hm =>
      (Finset.mem_compl.mp (hsub a hv)) (Finset.mem_union_left _ hm))
  · intro a
    exact PieceCore.Induced.no_short_mono G (P∪S)ᶜ (Y a) (hsub a) g hg hshort
  · intro a
    refine ⟨(L:ℝ),by exact_mod_cast hL,?_,?_,hlog⟩
    · exact_mod_cast (hy a).1
    · exact_mod_cast (hy a).2.1


def constant : ℝ := Classical.choose exists_constant.{0}

theorem constant_pos : 0<constant := (Classical.choose_spec exists_constant.{0}).1

section Retained
variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀e∈G.internalEdges R,G.src e≠G.dst e)
  (hsimple : ∀e∈G.internalEdges R,∀f∈G.internalEdges R,
    ((G.src e=G.src f ∧ G.dst e=G.dst f) ∨ (G.src e=G.dst f ∧ G.dst e=G.src f))→e=f)

local notation "H" => graph G R hloop hsimple
local notation "U" => InducedCycleAvoidance.region G R hloop hsimple
local notation "seed" => InducedCycleAvoidance.seed G R hloop hsimple

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
  apply (Classical.choose_spec LargeOrderChain.exists_constant.{0}).2 G (U i) P S u p F U
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
    exact RetainedChainContradiction.region_card_gt G R hloop hsimple D hg j
  · exact ChainContradiction.chain_card_of_weight F.card ((L+S.card+2)*w) L s
      (by omega) hweight hchain

end Retained

section Packing
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
    (hlogg : LargeOrderChain.constant*Real.logb 2 (((2*K:ℕ):ℝ)+2)≤g)
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
  apply LargeOrderChain.bound_of_mass G R hloop hsimple P S p.1 hG hcubic hP p.2
    (by intro v hv; exact Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp hv) (Finset.mem_union_left _ h)))
    D (2*K) s w g ((2:ℝ)^PackingCycleSelection.linkExponent G P D t (2*K))
    hret hL hs hshort (by positivity) ?_ hforest hjoined hmass ?_ hchain hwidth hg hlogg hsmall
  · intro C C' hC hC' _ hdisj
    exact PackingCycleSelection.cycle_linkFactor_le G P Q hloop hsimple D t (2*K)
      C C' hdisj hmax (fun v _=>hcubic v) hQ hhit hD hDL ht hlink hC hC' hG hforest
  · simpa only [PackingContradiction.linkExponent_eq G P hP D t (2*K)] using hη

end Packing

end Erdos1016.ExactMaximumSupport.Shortening.LargeOrderChain

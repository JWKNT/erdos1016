import Erdos1016.ExactMaximumSupport.LargeGirth.BlockGeometry
import Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The finite clean-chain contradiction

Actual separator blocks provide the two large pieces. All finite size and
girth budgets are explicit; their eventual parameter choices are separate.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ChainContradiction
open FiniteMultiGraph SimpleGraph PolynomialBound.Separation
local instance chainContradictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem chain_card_of_weight (T N L s : ℕ) (hL : 0<L)
    (hweight : (8:ℝ)/L < (T:ℝ)*L*((3/2:ℝ)*L*(1/2:ℝ)^s))
    (hbudget : (N:ℝ)*(3/2:ℝ)*(L:ℝ)^3*(1/2:ℝ)^s≤8) : N<T := by
  have hLr : (0:ℝ)<L := by exact_mod_cast hL
  have hw := (div_lt_iff₀ hLr).mp hweight
  by_contra hnot
  have hTN : (T:ℝ)≤N := by exact_mod_cast (show T≤N by omega)
  have hh := mul_le_mul_of_nonneg_right hTN
    (by positivity : (0:ℝ)≤(3/2:ℝ)*(L:ℝ)^3*(1/2:ℝ)^s)
  nlinarith

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
  obtain ⟨D,C,hD,hC,hpieces⟩ := SmallBoundaryPieces.exists_constants
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
    right
    refine ⟨(L:ℝ),by exact_mod_cast hL,?_,?_,hlog⟩
    · exact_mod_cast (hy a).1
    · exact_mod_cast (hy a).2.1

end Erdos1016.ExactMaximumSupport.LargeGirth.ChainContradiction

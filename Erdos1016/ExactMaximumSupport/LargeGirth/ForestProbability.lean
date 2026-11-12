import Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudgetFinal
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingContradiction
import Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Forest probability below two fifths at large rank

The two dyadic packings are constructed in the actual graph. Their proved
size bounds discharge every finite trace, link, load, and clean-block budget.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.ExactMaximumSupport.LargeGirth.ForestProbability
open FiniteMultiGraph ParameterBudget RaisedGirth GirthRaiseBounds
local instance forestProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem exists_cutoff :
    ∃ D R : ℕ,256≤D ∧ ∀(G:FiniteMultiGraph)(P:Finset G.Vertex),
      G.toSimpleGraph.Connected→(∀v,G.degree v=3)→R≤G.cycleRank→
      (G.toSimpleGraph.induce (↑P:Set G.Vertex)).Connected→
      (P.card:ℝ)≤3*Real.logb 2 (G.cycleRank:ℝ)→
      ¬(PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D→
      G.regionForestProbability Pᶜ<2/5 := by
  obtain ⟨D,hD,hraise⟩ := RaisedGirth.exists_raising_cutoff
  obtain ⟨R,hR⟩ := exists_rank_threshold D (by omega) RetainedChainContradiction.constant
    RetainedChainContradiction.constant_pos.le
  refine ⟨D,max R 1,hD,?_⟩
  intro G P hG hcubic hr hP hPsize hshort
  by_contra hnot
  have hprob : (2/5:ℝ)≤G.regionForestProbability Pᶜ := le_of_not_gt hnot
  obtain ⟨seq⟩ := hraise G P D hG hcubic le_rfl (Or.inr hP) hshort hprob
  let r := G.cycleRank
  let x : ℝ := Real.logb 2 (r:ℝ)
  let i := scaleIndex D (Real.sqrt x)
  let j := scaleIndex D (x/16)
  let lo := scale D i
  let hi := scale D j
  let S := seq.region i
  let T := seq.region j
  let Q := seq.family j
  let V := (P∪T)ᶜ
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvT
    exact (Finset.mem_compl.mp (seq.outside j hvT)) hvP
  have hdel : (P∪T).card=P.card+T.card := Finset.card_union_of_disjoint hPT
  have horder : G.vertexCount+2=2*r := by
    have hh := G.order_add_two_eq_twice_rank_add_marked_deficit ∅ hG
      (fun v=>(hcubic v).le) (fun v _=>hcubic v)
    simpa only [Finset.sum_empty,add_zero] using hh
  have hledger : V.card+P.card+T.card+2=2*r := by
    have hh := Finset.card_add_card_compl (P∪T)
    simp only [Fintype.card_fin,hdel] at hh
    change P.card+T.card+V.card=G.vertexCount at hh
    omega
  have hpow : (2:ℝ)^x=(r:ℝ) :=
    Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast (show 0<r by dsimp [r]; omega))
  have hledgerR : (V.card:ℝ)+P.card+T.card+2=2*(2:ℝ)^x := by
    rw [hpow]
    exact_mod_cast hledger
  have hb : FiniteBudgets RetainedChainContradiction.constant x hi lo V.card
      (P.card+T.card) S.card :=
    hR r (by dsimp [r]; omega) P.card T.card S.card V.card hPsize (seq.size j) (seq.size i) hledgerR
  have hQregion : Q.biUnion id=T := (seq.region_eq j).symm
  have hcontr := PackingContradiction.bound_of_budgets G P S Q hi (parallelDepth x)
    (traceStart x) (halfCutoff x) (hi/2) (blockSpan x) (lo+1) hG hcubic hP
    (seq.spec j) (by
      intro U hU
      rw [hQregion]
      exact seq.hits j U hU)
    hb.large_girth hb.cutoff_ge hb.depth_pos hb.link_geometry hprob
    hb.trace_pos hb.trace_interval hb.cutoff_pos hb.radius_pos hb.radius_girth
    (by simpa only [hQregion] using hb.order_pos)
    (by simpa only [hQregion,hdel] using hb.deficit_lt)
    (by simpa only [hQregion,hdel] using hb.trace_main)
    (by simpa only [hQregion] using hb.trace_error)
    hb.collision hb.trace_log hb.joined_load hb.link_load hb.clean_chain hb.block_width
    hb.small_girth (by simpa only [Nat.cast_add, Nat.cast_one] using hb.small_log)
    (seq.no_short i)
  exact not_lt_of_ge hprob hcontr.2

end Erdos1016.ExactMaximumSupport.LargeGirth.ForestProbability

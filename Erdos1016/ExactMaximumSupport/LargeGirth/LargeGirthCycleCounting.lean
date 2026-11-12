import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.NetMinimal
import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProductWords

set_option autoImplicit false

/-!
# Counting cycles using an exterior forest event

A cycle that is not supported in a region restricts to a forest there.
The remaining cycles inject into the region's actual labelled cycle space.
Both counts use the original physical edge labels.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.LargeGirth.CycleCounting
open FiniteMultiGraph

local instance countingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cycle_restriction_forest (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (R : Finset G.Vertex) (x : G.EdgeWord) (hx : G.IsCycleWord x)
    (hout : ¬ G.SupportedIn x R) :
    G.IsForestWord (G.restrictEdges (G.internalEdges R) x) := by
  apply (G.isForestWord_iff_no_even_support _).2
  intro y hy
  by_contra hyn
  have hxn := (G.isCycleWord_iff_looplessNetwork x
    (fun e he => (hloop e he).elim)).1 hx
  have hsub : (looplessNetwork G).IsSubword (nonloopWord G y.1) (nonloopWord G x) := by
    intro e he
    have h := hy e.1 he
    by_cases hi : e.1 ∈ G.internalEdges R
    · simpa [restrictEdges, hi] using h
    · simp [restrictEdges, hi] at h
  have hye : (looplessNetwork G).boundary (nonloopWord G y.1) = 0 := by
    rw [nonloopWord_boundary]
    exact y.2
  have hyn' : nonloopWord G y.1 ≠ 0 :=
    (G.ne_zero_iff_nonloopWord y.1 (fun e he => (hloop e he).elim)).1 hyn
  have heq := hxn.eq_of_even_subword hsub hye hyn'
  apply hout
  intro e he
  have hval : y.1 e = x e := congrFun heq ⟨e, hloop e⟩
  have hf := hy e (by rw [hval]; exact he)
  have hi : e ∈ G.internalEdges R := by
    by_contra hi
    simp [restrictEdges, hi] at hf
  exact (Finset.mem_filter.mp hi).2

private def cycleEncoding (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (R : Finset G.Vertex) (x : {x : G.EdgeWord // G.IsCycleWord x}) :
    Sum {y : G.CycleSpace // G.IsForestWord (G.restrictEdges (G.internalEdges R) y.1)}
      (G.internalCycleSpace R) :=
  if hs : G.SupportedIn x.1 R then
    Sum.inr ⟨x.2.toCycleSpace, by
      intro e he
      by_contra hn
      exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs e hn⟩)⟩
  else Sum.inl ⟨x.2.toCycleSpace, cycle_restriction_forest G hloop R x.1 x.2 hs⟩

private theorem cycleEncoding_injective (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (R : Finset G.Vertex) : Function.Injective (cycleEncoding G hloop R) := by
  intro x y h
  by_cases hx : G.SupportedIn x.1 R <;> by_cases hy : G.SupportedIn y.1 R
  · simp only [cycleEncoding, dif_pos hx, dif_pos hy, Sum.inr.injEq] at h
    exact Subtype.ext (congrArg (fun z : G.internalCycleSpace R => z.1.1) h)
  · simp only [cycleEncoding, dif_pos hx, dif_neg hy] at h
    cases h
  · simp only [cycleEncoding, dif_neg hx, dif_pos hy] at h
    cases h
  · simp only [cycleEncoding, dif_neg hx, dif_neg hy, Sum.inl.injEq] at h
    exact Subtype.ext (congrArg (fun z :
      {y : G.CycleSpace // G.IsForestWord (G.restrictEdges (G.internalEdges R) y.1)} =>
        z.1.1) h)

/-- Cycle words meeting the complement inject into the actual forest event.
The other words inject into the induced cycle space. -/
theorem numCycles_le_forest_count_add_internal (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (R : Finset G.Vertex) :
    G.numCycles ≤
      (Finset.univ.filter fun x : G.CycleSpace =>
        G.IsForestWord (G.restrictEdges (G.internalEdges R) x.1)).card +
        2 ^ (PieceCore.Induced.graph G R).cycleRank := by
  have h := Fintype.card_le_of_injective (cycleEncoding G hloop R)
    (cycleEncoding_injective G hloop R)
  have hi : Fintype.card (G.internalCycleSpace R) =
      2 ^ (PieceCore.Induced.graph G R).cycleRank := by
    rw [← Fintype.card_congr (PoleProduct.cycleEquiv G R).toEquiv]
    exact (PieceCore.Induced.graph G R).cycleSpace_card
  simpa only [numCycles, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_subtype, hi] using h

/-- The cycle count is bounded by one exterior-event count and one internal rank. -/
theorem numCycles_le_probability_add_internal (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (R : Finset G.Vertex) :
    (G.numCycles : ℝ) ≤ G.regionForestProbability R * (2 : ℝ) ^ G.cycleRank +
      (2 : ℝ) ^ (PieceCore.Induced.graph G R).cycleRank := by
  have h := numCycles_le_forest_count_add_internal G hloop R
  have hp : G.regionForestProbability R * (2 : ℝ) ^ G.cycleRank =
      ((Finset.univ.filter fun x : G.CycleSpace =>
        G.IsForestWord (G.restrictEdges (G.internalEdges R) x.1)).card : ℝ) := by
    unfold regionForestProbability
    exact div_mul_cancel₀ _ (by positivity)
  rw [hp]
  exact_mod_cast h

/-- A loss of four ranks leaves enough room below one half. -/
theorem numCycles_lt_half_of_forest_rank_loss (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (R : Finset G.Vertex)
    (hq : G.regionForestProbability R < (2 / 5 : ℝ))
    (hrank : (PieceCore.Induced.graph G R).cycleRank + 4 ≤ G.cycleRank) :
    G.numCycles < 2 ^ (G.cycleRank - 1) := by
  have hc := numCycles_le_probability_add_internal G hloop R
  have hp : (2 : ℝ) ^ (PieceCore.Induced.graph G R).cycleRank * 16 ≤
      (2 : ℝ) ^ G.cycleRank := by
    calc
      _ = (2 : ℝ) ^ ((PieceCore.Induced.graph G R).cycleRank + 4) := by
        rw [pow_add]
        norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hrank
  have hr : 1 ≤ G.cycleRank := by omega
  have he : (2 : ℝ) ^ G.cycleRank = 2 * (2 : ℝ) ^ (G.cycleRank - 1) := by
    conv_lhs => rw [show G.cycleRank = (G.cycleRank - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hstrict := mul_lt_mul_of_pos_right hq (by positivity : (0 : ℝ) < 2 ^ G.cycleRank)
  have hpositive : (0 : ℝ) < 2 ^ G.cycleRank := by positivity
  have hlt : (G.numCycles : ℝ) < (2 : ℝ) ^ (G.cycleRank - 1) := by
    nlinarith
  exact_mod_cast hlt

/-- Actual labelled girth passes from the whole graph to an induced region. -/
theorem induced_no_short (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (D : ℕ) (hD : 3 ≤ D) (hshort : ¬ G.HasCycleShorterThan D) :
    ¬ (PieceCore.Induced.graph G R).HasCycleShorterThan D := by
  open PieceCore.Induced ShortProof.CycleCore CubicReduction Nonbacktracking in
  have h3 := no_short_three_of_le G D hD hshort
  let H := realization G h3
  let K := InducedSimpleRealization.graph G R
    (fun e _ => noLoops_of_no_short_cycle G h3 e)
    (fun e _ f _ => simple_of_no_short_cycle G h3 e f)
  let inc : K.toSimpleGraph →g H.toSimpleGraph := {
    toFun := PieceCore.Induced.vertex G R
    map_rel' := by
      intro u v huv
      change (realization G h3).toSimpleGraph.Adj _ _
      rw [realization_toSimpleGraph]
      exact (InducedSimpleRealization.adj_vertex_iff G R _ _ u v).mp huv }
  have hinj : Function.Injective inc := PieceCore.Induced.vertex_injective G R
  rintro ⟨x, hx, hlen⟩
  have hx' : K.IsCycleWord x :=
    (CubicReduction.asMultigraph_isCycleWord_iff K x).mp hx
  obtain ⟨v, p, hp, heq⟩ := Nonbacktracking.exists_cycle_walk_of_cycleWord K ⟨x, hx'⟩
  let q := p.map inc
  have hq : q.IsCycle := (SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).mpr hp
  let C := Nonbacktracking.cycleWordOfWalk H q hq
  have hC : G.IsCycleWord C.1 := (realization_isCycleWord_iff G h3 C.1).mp C.2
  have he := Nonbacktracking.cycleWordOfWalk_length K p hp
  rw [heq] at he
  have hf := Nonbacktracking.cycleWordOfWalk_length H q hq
  change (PieceCore.Induced.graph G R).wordLength x = p.length at he
  change G.wordLength C.1 = q.length at hf
  have hqLen : q.length = p.length := by simp [q]
  exact hshort ⟨C.1, hC, by omega⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.CycleCounting

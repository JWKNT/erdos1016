import Erdos1016.Extremal.Construction.RecursiveShortcutGraph
import Erdos1016.Extremal.CompleteGraphWitness

set_option autoImplicit false

/-!
# Unconditional upper bound, including every small order

The recursive shortcut construction supplies the bound for orders at least
seven. Complete graphs cover orders three through five; a six-cycle with two
chords covers order six. This exports the upper half of the target without
any of the forest-probability hypotheses needed for the lower half.
-/

namespace Erdos1016.Problem1016

open SimpleGraph Erdos1016.Extremal

private def sixVertexGraph : SimpleGraph (Fin 6) :=
  cycleGraph 6 ⊔ fromEdgeSet ({s(0, 2), s(0, 3)} : Set (Sym2 (Fin 6)))

private instance : DecidableRel sixVertexGraph.Adj := by
  intro u v
  change Decidable ((cycleGraph 6).Adj u v ∨
    (s(u, v) ∈ ({s(0, 2), s(0, 3)} : Set (Sym2 (Fin 6))) ∧ u ≠ v))
  infer_instance

private def sixCycle3 : sixVertexGraph.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 2) (by decide) (.cons (by decide) .nil))

private def sixCycle4 : sixVertexGraph.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 2) (by decide)
    (.cons (v := 3) (by decide) (.cons (by decide) .nil)))

private def sixCycle5 : sixVertexGraph.Walk 0 0 :=
  .cons (v := 2) (by decide) (.cons (v := 3) (by decide)
    (.cons (v := 4) (by decide) (.cons (v := 5) (by decide)
      (.cons (by decide) .nil))))

private def sixCycle6 : sixVertexGraph.Walk 0 0 :=
  .cons (v := 1) (by decide) (.cons (v := 2) (by decide)
    (.cons (v := 3) (by decide) (.cons (v := 4) (by decide)
      (.cons (v := 5) (by decide) (.cons (by decide) .nil)))))

private theorem sixVertexGraph_pancyclic : IsPancyclic sixVertexGraph := by
  intro ℓ hmin hmax
  have hmax' : ℓ ≤ 6 := by simpa using hmax
  interval_cases ℓ
  · refine ⟨0, sixCycle3, ?_, rfl⟩
    rw [sixCycle3, Walk.cons_isCycle_iff, Walk.isPath_def]
    decide
  · refine ⟨0, sixCycle4, ?_, rfl⟩
    rw [sixCycle4, Walk.cons_isCycle_iff, Walk.isPath_def]
    decide
  · refine ⟨0, sixCycle5, ?_, rfl⟩
    rw [sixCycle5, Walk.cons_isCycle_iff, Walk.isPath_def]
    decide
  · refine ⟨0, sixCycle6, ?_, rfl⟩
    rw [sixCycle6, Walk.cons_isCycle_iff, Walk.isPath_def]
    decide

private theorem sixVertexGraph_excess : excess 6 sixVertexGraph = 2 := by
  classical
  letI : Fintype sixVertexGraph.edgeSet := Fintype.ofFinite _
  have hedges : sixVertexGraph.edgeFinset =
      {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0), s(0, 2), s(0, 3)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [mem_edgeFinset]
      fin_cases u <;> fin_cases v <;> decide
  have hc : sixVertexGraph.edgeFinset.card = 8 := by rw [hedges]; decide
  unfold excess
  rw [← SimpleGraph.edgeFinset_card]
  omega

private theorem completeGraph_excess_le (n : ℕ) :
    excess n (completeGraph (Fin n)) ≤ n.choose 2 - n := by
  classical
  letI : Fintype (completeGraph (Fin n)).edgeSet := Fintype.ofFinite _
  unfold excess
  rw [← SimpleGraph.edgeFinset_card]
  apply Nat.sub_le_sub_right
  simpa using (SimpleGraph.card_edgeFinset_le_card_choose_two
    (G := completeGraph (Fin n)))

/-- The binary-shortcut upper bound holds for every order in the problem,
with the same additive constant one, including orders three through six. -/
theorem upper_bound_integer (n : ℕ) (hn : 3 ≤ n) :
    h n ≤ n.log2 + logStar n + 1 := by
  by_cases hlarge : 7 ≤ n
  · exact pancyclic_excess_integer_upper_bound n hlarge
  have hsmall : n ≤ 6 := by omega
  have hcomplete := (h_le_excess_of_isPancyclic n _
    (completeGraph_isPancyclic n)).trans (completeGraph_excess_le n)
  have hstar4 : logStar 4 = 2 := by
    simpa [expTower] using logStar_expTower 2
  interval_cases n
  · norm_num [Nat.choose] at hcomplete ⊢
    omega
  · norm_num [Nat.choose, hstar4] at hcomplete ⊢
    omega
  · have hs : 2 ≤ logStar 5 := by
      rw [← hstar4]
      exact logStar_mono (by omega)
    have hl : 2 ≤ Nat.log2 5 := (Nat.le_log2 (by decide)).2 (by norm_num)
    norm_num [Nat.choose] at hcomplete ⊢
    omega
  · have hsix := h_le_excess_of_isPancyclic 6 sixVertexGraph sixVertexGraph_pancyclic
    rw [sixVertexGraph_excess] at hsix
    have hl : 2 ≤ Nat.log2 6 := (Nat.le_log2 (by decide)).2 (by norm_num)
    omega

/-- The upper half of the sharp asymptotic statement is unconditional. -/
theorem upper_bound (n : ℕ) (hn : 3 ≤ n) :
    (h n : ℝ) ≤ Real.logb 2 (n : ℝ) + (logStar n : ℝ) + 1 := by
  have hint := upper_bound_integer n hn
  have hlog := log2_real_logb_bounds n (by omega : 1 ≤ n)
  have hcast : (h n : ℝ) ≤ (n.log2 : ℝ) + (logStar n : ℝ) + 1 := by
    exact_mod_cast hint
  linarith [hlog.1]

end Erdos1016.Problem1016

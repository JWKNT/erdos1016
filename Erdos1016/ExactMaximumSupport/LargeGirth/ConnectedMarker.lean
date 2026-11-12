import Erdos1016.Graph.ConnectedRegionBoundary
import Erdos1016.Graph.Multigraph.SubcubicOrder
import Erdos1016.ExactMaximum.Cycles
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# A connected marker of fixed size

A finite connected graph contains a connected induced region of each
positive size up to its order. We use eight vertices in the final count.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker

local instance markerDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem exists_connected_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (n : ℕ) (hn : 1 ≤ n) (hle : n ≤ Fintype.card V) :
    ∃ P : Finset V, P.card = n ∧ (G.induce (↑P : Set V)).Connected := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      obtain ⟨v⟩ := hG.nonempty
      refine ⟨{v}, by simp, ?_⟩
      simpa using (SimpleGraph.Walk.nil : G.Walk v v).connected_induce_support
    · obtain ⟨P, hcard, hconn⟩ := ih (by omega) (by omega)
      have hne : (↑P : Set V).Nonempty := by
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
        exact ⟨v, hv⟩
      have hproper : (↑P : Set V) ≠ Set.univ := by
        intro heq
        have hPu : P = Finset.univ := by
          ext v
          have hv := Set.ext_iff.mp heq v
          simpa using hv
        rw [hPu, Finset.card_univ] at hcard
        omega
      obtain ⟨a, b, ha, hb, hab⟩ :=
        Proof.ConnectedRegionBoundary.Connected.exists_adj_boundary hG hne hproper
      refine ⟨insert b P, ?_, ?_⟩
      · rw [Finset.card_insert_of_not_mem (show b ∉ P from hb), hcard]
      have hc := SimpleGraph.induce_union_connected hconn
        (SimpleGraph.induce_pair_connected_of_adj hab) ⟨a, ha, by simp⟩
      have heq : (↑P : Set V) ∪ {a, b} = ↑(insert b P) := by
        ext v
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert]
        constructor
        · rintro (hv | rfl | rfl)
          · exact Or.inr hv
          · exact Or.inr ha
          · exact Or.inl rfl
        · rintro (rfl | hv)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl hv
      rw [heq] at hc
      exact hc

/-- The cubic order identity gives enough vertices once the rank is at least five. -/
theorem exists_eight (G : FiniteMultiGraph) (hG : G.toSimpleGraph.Connected)
    (hcub : G.IsCubic) (hr : 5 ≤ G.cycleRank) :
    ∃ P : Finset G.Vertex, P.card = 8 ∧
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected := by
  have ho := G.order_add_two_eq_twice_rank_add_deficit hG (fun v => (hcub v).le)
  have hd : G.cubicDeficit = 0 := by
    unfold FiniteMultiGraph.cubicDeficit
    apply Finset.sum_eq_zero
    intro v _
    rw [hcub v]
    norm_num
  have hn : 8 ≤ G.vertexCount := by omega
  exact exists_connected_card G.toSimpleGraph hG 8 (by omega)
    (by simpa using hn)

theorem eight_le_log_budget (r : ℕ) (hr : 8 ≤ r) :
    (8 : ℝ) ≤ 3 * Real.logb 2 (r : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 8) (by exact_mod_cast hr : (8 : ℝ) ≤ r)
  have he : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]
    simp
  rw [he] at h
  linarith

end Erdos1016.ExactMaximumSupport.LargeGirth.ConnectedMarker

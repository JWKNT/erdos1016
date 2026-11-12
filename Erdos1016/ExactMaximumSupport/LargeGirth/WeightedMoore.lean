import Erdos1016.ExactMaximumSupport.LargeGirth.CorridorMoore
import Erdos1016.ExactMaximumSupport.LargeGirth.SimpleRealization
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
# The weighted Moore bound for connected degree-two/three graphs

Suppress the degree-two vertices through the actual corridor partition.
The resulting cubic multigraph has `2(h-1)` vertices and `3(h-1)` edges.
The weighted corridor count supplies a short ordinary cycle, even when the
suppressed graph has loops or parallel labels. No walk/girth adapter is an
extra hypothesis of the final theorem.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open FiniteMultiGraph ShortProof Proof.CompressedRouteDecomposition
open Proof.PartitionRouteDecomposition Proof.PhysicalPartition

/-- The integer form avoids division and is convenient for subsequent bounds. -/
theorem weighted_moore_integer (G : PhysicalGraph) (g : ℕ)
    (hconn : G.IsConnected) (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 2 ≤ G.cycleRank)
    (hg : ∀ v (p : G.toSimpleGraph.Walk v v), p.IsCycle → g ≤ p.length) :
    g * (3 * (G.cycleRank - 1)) ≤
      4 * Nat.clog 2 (8 * G.cycleRank) * G.edgeCount := by
  classical
  let P := CubicReduction.cubicVertices G
  have hP : P.Nonempty := CubicReduction.cubicVertices_nonempty G hconn hmin hmax hr
  have hd (v : G.Vertex) (_hv : v ∉ P) : G.degree v = 2 ∨ G.degree v = 3 := by
    have h₁ := hmin v
    have h₂ := hmax v
    omega
  let D := MarkedCorridors.partition G P hconn hP hd
  let hne := MarkedCorridors.partition_nonempty G P hconn hP hd
  let hend := MarkedCorridors.partition_endpoints G P hconn hP hd
  let M := MarkedCorridors.graph G P hconn hP hd
  have hmconn : M.toSimpleGraph.Connected := MarkedCorridors.connected G P hconn hP hd
  have hmr : M.cycleRank = G.cycleRank := MarkedCorridors.cycleRank_preserved G P hconn hP hd
  have hmcub : M.IsCubic := by
    intro v
    rw [MarkedCorridors.degree_preserved]
    have hv := MarkedCorridors.vertexMap_retained G P hconn hP hd v
    simpa only [Proof.PhysicalDegreeTwoCoreComponents.protectedOrBranch, P,
      CubicReduction.cubicVertices, Finset.union_self, Finset.mem_filter,
      Finset.mem_univ, true_and] using hv
  have horder := CorridorLedger.cubic_order_size M hmconn hmcub
  rw [hmr] at horder
  have hn : M.vertexCount = 2 * (G.cycleRank - 1) := by omega
  have hm : M.edgeCount = 3 * (G.cycleRank - 1) := by omega
  let t := Nat.clog 2 (8 * G.cycleRank)
  have ht : 0 < t := by
    have hp := Nat.le_pow_clog (by decide : 1 < 2) (8 * G.cycleRank)
    by_contra hnot
    have hz : t = 0 := Nat.eq_zero_of_not_pos hnot
    change 8 * G.cycleRank ≤ 2 ^ t at hp
    rw [hz] at hp
    norm_num at hp
    omega
  have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hp : 8 * G.cycleRank ≤ 2 * 2 ^ (t - 1) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (8 * G.cycleRank)
    change 8 * G.cycleRank ≤ 2 ^ t at hh
    rw [← ht', pow_succ] at hh
    simpa only [Nat.mul_comm] using hh
  have hcount : 2 * M.vertexCount ^ 2 < 2 * M.edgeCount * 2 ^ (t - 1) := by
    have hmul := Nat.mul_le_mul_left M.edgeCount hp
    rw [hn, hm] at *
    have hpred : G.cycleRank - 1 + 1 = G.cycleRank := by omega
    have hpos : 1 ≤ G.cycleRank - 1 := by omega
    nlinarith
  have hsum : (∑ e : M.Edge, CorridorMoore.weight D hend e) = G.edgeCount := by
    calc
      _ = ∑ e : M.Edge, ((MarkedCorridors.routes G P hconn hP hd).support e).card := by
        apply Finset.sum_congr rfl
        intro e _
        exact (PhysicalCorridor.support_card_eq_length (corridorAt D e)).symm
      _ = G.edgeCount := CorridorLedger.marked_route_length_sum G P hconn hP hd
  have hb := CorridorMoore.weighted_girth_bound D hne hend hmcub g (t - 1) hg hcount
  change g * M.edgeCount ≤ 4 * (t - 1 + 1) * ∑ e, CorridorMoore.weight D hend e at hb
  have hb' : g * M.edgeCount ≤ 4 * (t - 1 + 1) * G.edgeCount :=
    hb.trans (Nat.mul_le_mul_left _ hsum.le)
  rw [hm, ht'] at hb'
  exact hb'

def degreeTwoCount (G : PhysicalGraph) : ℕ := by
  classical
  exact (Finset.univ.filter fun v => G.degree v = 2).card

theorem edgeCount_eq_rank_and_degreeTwo (G : PhysicalGraph)
    (hconn : G.IsConnected) (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 1 ≤ G.cycleRank) :
    G.edgeCount = 3 * (G.cycleRank - 1) + degreeTwoCount G := by
  classical
  let M := CycleCore.asMultigraph G
  have hc : M.toSimpleGraph.Connected := by
    rw [CubicReduction.asMultigraph_toSimpleGraph]
    exact hconn
  have hmdegree (v : M.Vertex) : M.degree v = G.degree v :=
    CubicReduction.asMultigraph_selectedDegree G (fun _ => 1) v
  have hd : M.cubicDeficit = degreeTwoCount G := by
    unfold FiniteMultiGraph.cubicDeficit degreeTwoCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    rw [hmdegree]
    have h₁ := hmin v
    have h₂ := hmax v
    by_cases h : G.degree v = 2
    · simp [h]
    · have h3 : G.degree v = 3 := by omega
      simp [h3]
  have he := M.connected_euler hc
  have ho := M.order_add_two_eq_twice_rank_add_deficit hc (fun v => by rw [hmdegree]; exact hmax v)
  rw [CubicReduction.asMultigraph_cycleRank] at he ho
  rw [hd] at ho
  change G.cycleRank + G.vertexCount = G.edgeCount + 1 at he
  change G.vertexCount + 2 = 2 * G.cycleRank + degreeTwoCount G at ho
  omega

/-- `Nat.clog 2 (8h)` is the integer ceiling of the base-two logarithm.
This is the weighted Moore bound in the usual real-valued form. -/
theorem weighted_moore (G : PhysicalGraph) (g : ℕ)
    (hconn : G.IsConnected) (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 2 ≤ G.cycleRank)
    (hg : ∀ v (p : G.toSimpleGraph.Walk v v), p.IsCycle → g ≤ p.length) :
    (g : ℝ) ≤ 4 * (Nat.clog 2 (8 * G.cycleRank) : ℝ) *
      (1 + (degreeTwoCount G : ℝ) / (3 * (G.cycleRank - 1 : ℕ) : ℝ)) := by
  have hb := weighted_moore_integer G g hconn hmin hmax hr hg
  rw [edgeCount_eq_rank_and_degreeTwo G hconn hmin hmax (by omega)] at hb
  have hbR : (g : ℝ) * (3 * (G.cycleRank - 1 : ℕ) : ℝ) ≤
      4 * (Nat.clog 2 (8 * G.cycleRank) : ℝ) *
        ((3 * (G.cycleRank - 1 : ℕ) : ℝ) + degreeTwoCount G) := by exact_mod_cast hb
  have hpos : (0 : ℝ) < (3 * (G.cycleRank - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 3 * (G.cycleRank - 1) by omega)
  apply (mul_le_mul_right hpos).mp
  calc
    _ ≤ 4 * (Nat.clog 2 (8 * G.cycleRank) : ℝ) *
        ((3 * (G.cycleRank - 1 : ℕ) : ℝ) + degreeTwoCount G) := hbR
    _ = (4 * (Nat.clog 2 (8 * G.cycleRank) : ℝ) *
        (1 + (degreeTwoCount G : ℝ) / (3 * (G.cycleRank - 1 : ℕ) : ℝ))) *
          (3 * (G.cycleRank - 1 : ℕ) : ℝ) := by
      rw [mul_assoc _ _ (3 * (G.cycleRank - 1 : ℕ) : ℝ), add_mul,
        one_mul, div_mul_cancel₀ _ hpos.ne']

/-- The exact multigraph cycle-word predicate supplies simplicity and the
ordinary girth premise. Simplicity is not an additional assumption. -/
theorem multigraph_weighted_moore_integer (M : FiniteMultiGraph) (g : ℕ)
    (hconn : M.toSimpleGraph.Connected) (hmin : ∀ v, 2 ≤ M.degree v)
    (hmax : ∀ v, M.degree v ≤ 3) (hr : 2 ≤ M.cycleRank)
    (hg : 3 ≤ g) (hshort : ¬ M.HasCycleShorterThan g) :
    g * (3 * (M.cycleRank - 1)) ≤
      4 * Nat.clog 2 (8 * M.cycleRank) * M.edgeCount := by
  let h3 := no_short_three_of_le M g hg hshort
  let G := realization M h3
  have hc : G.IsConnected := realization_connected M h3 hconn
  have h₁ (v : G.Vertex) : 2 ≤ G.degree v := by
    rw [realization_degree]
    exact hmin v
  have h₂ (v : G.Vertex) : G.degree v ≤ 3 := by
    rw [realization_degree]
    exact hmax v
  have hrg : 2 ≤ G.cycleRank := by simpa only [G, realization_cycleRank] using hr
  have hgw : ∀ v (p : G.toSimpleGraph.Walk v v), p.IsCycle → g ≤ p.length := by
    have hh := realization_girthGreater M h3 (g - 1) (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ g)] using hshort)
    intro v p hp
    have ht := hh v p hp
    omega
  have hb := weighted_moore_integer G g hc h₁ h₂ hrg hgw
  simpa only [G, realization_cycleRank, realization] using hb

/-- In a connected degree-two/three multigraph the cubic deficit equals
the number of degree-two ports. This form keeps the standard deficit API. -/
theorem multigraph_weighted_moore (M : FiniteMultiGraph) (g : ℕ)
    (hconn : M.toSimpleGraph.Connected) (hmin : ∀ v, 2 ≤ M.degree v)
    (hmax : ∀ v, M.degree v ≤ 3) (hr : 2 ≤ M.cycleRank)
    (hg : 3 ≤ g) (hshort : ¬ M.HasCycleShorterThan g) :
    (g : ℝ) ≤ 4 * (Nat.clog 2 (8 * M.cycleRank) : ℝ) *
      (1 + (M.cubicDeficit : ℝ) / (3 * (M.cycleRank - 1 : ℕ) : ℝ)) := by
  have hb := multigraph_weighted_moore_integer M g hconn hmin hmax hr hg hshort
  have he := M.connected_euler hconn
  have ho := M.order_add_two_eq_twice_rank_add_deficit hconn hmax
  have hm : M.edgeCount = 3 * (M.cycleRank - 1) + M.cubicDeficit := by omega
  rw [hm] at hb
  have hbR : (g : ℝ) * (3 * (M.cycleRank - 1 : ℕ) : ℝ) ≤
      4 * (Nat.clog 2 (8 * M.cycleRank) : ℝ) *
        ((3 * (M.cycleRank - 1 : ℕ) : ℝ) + M.cubicDeficit) := by exact_mod_cast hb
  have hpos : (0 : ℝ) < (3 * (M.cycleRank - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 3 * (M.cycleRank - 1) by omega)
  apply (mul_le_mul_right hpos).mp
  calc
    _ ≤ 4 * (Nat.clog 2 (8 * M.cycleRank) : ℝ) *
        ((3 * (M.cycleRank - 1 : ℕ) : ℝ) + M.cubicDeficit) := hbR
    _ = (4 * (Nat.clog 2 (8 * M.cycleRank) : ℝ) *
        (1 + (M.cubicDeficit : ℝ) / (3 * (M.cycleRank - 1 : ℕ) : ℝ))) *
          (3 * (M.cycleRank - 1 : ℕ) : ℝ) := by
      rw [mul_assoc _ _ (3 * (M.cycleRank - 1 : ℕ) : ℝ), add_mul,
        one_mul, div_mul_cancel₀ _ hpos.ne']

end Erdos1016.ExactMaximumSupport.LargeGirth

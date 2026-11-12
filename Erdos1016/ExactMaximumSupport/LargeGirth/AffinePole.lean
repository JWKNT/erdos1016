import Erdos1016.ExactMaximumSupport.LargeGirth.MooreGrowth
import Erdos1016.ExactMaximumSupport.LargeGirth.BallLayers
import Erdos1016.Probability.Avoidance.PoleMarker
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# Affine forest proportions for poles of large girth

The two numerical regimes use the actual multigraph cycle-word girth.
The demand may be arbitrary on the degree-two vertices. The proof combines
the weighted Moore theorem, a port-free ball, and the thin-marker layer bound.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.AffinePole

open Probability.PoleMarker MooreGrowth

variable (M : FiniteMultiGraph)

def ports : Finset M.Vertex := by
  classical
  exact Finset.univ.filter fun v => M.degree v = 2

@[simp] theorem mem_ports (v : M.Vertex) : v ∈ ports M ↔ M.degree v = 2 := by
  classical
  simp [ports]

theorem ports_card (hmin : ∀ v, 2 ≤ M.degree v) (hmax : ∀ v, M.degree v ≤ 3) :
    (ports M).card = M.cubicDeficit := by
  classical
  unfold ports FiniteMultiGraph.cubicDeficit
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  have h₁ := hmin v
  have h₂ := hmax v
  by_cases he : M.degree v = 2
  · simp [he]
  · have he3 : M.degree v = 3 := by omega
    simp [he3]

theorem edgeCount_eq (hconn : M.toSimpleGraph.Connected) (hmax : ∀ v, M.degree v ≤ 3)
    (hr : 2 ≤ M.cycleRank) :
    M.edgeCount = 3*(M.cycleRank-1)+M.cubicDeficit := by
  have he := M.connected_euler hconn
  have hn := M.order_add_two_eq_twice_rank_add_deficit hconn hmax
  omega

/-- The exact geometric and numerical contradiction, with an auxiliary root
included in the marker even when the pole has no degree-two vertices. -/
theorem bound_of_budgets (B : ℕ)
    (hB : ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex) (o : G.Vertex)
      (b : G.Demand), G.toSimpleGraph.Connected → (∀ v, G.degree v ≤ 3) →
      (∀ v, v ∉ P → G.degree v = 3) → o ∈ P →
      (∀ v, v ∉ P → b v = 0) →
      (3/5 : ℝ) ≤ affineForestProbability G b →
      ∀ j : ℤ, (Finset.univ.filter fun v => (G.toSimpleGraph.dist o v : ℤ) = j).card ≤
        B*(P.card+1)^2)
    (g : ℕ) (hconn : M.toSimpleGraph.Connected)
    (hmin : ∀ v, 2 ≤ M.degree v) (hmax : ∀ v, M.degree v ≤ 3)
    (hr : 2 ≤ M.cycleRank) (hg : 3 ≤ g) (hshort : ¬ M.HasCycleShorterThan g)
    (hlog : g < 8*Nat.clog 2 (8*M.cycleRank))
    (hcover : 24*(M.cubicDeficit+1) < 2^(g/16))
    (hlayer : (2*(g/16)+1)*B*(M.cubicDeficit+2)^2 < 2^(g/16))
    (b : M.Demand) (hb : ∀ v, M.degree v = 3 → b v = 0) :
    affineForestProbability M b < 3/5 := by
  classical
  obtain ⟨o⟩ := hconn.nonempty
  let P := insert o (ports M)
  have ho : o ∈ P := Finset.mem_insert_self _ _
  have hc (v : M.Vertex) (hv : v ∉ P) : M.degree v = 3 := by
    have hnot : M.degree v ≠ 2 := by
      intro he
      exact hv (Finset.mem_insert_of_mem ((mem_ports M v).mpr he))
    have h₁ := hmin v
    have h₂ := hmax v
    omega
  have hP : P.card ≤ M.cubicDeficit+1 := by
    exact (Finset.card_insert_le o (ports M)).trans_eq (by rw [ports_card M hmin hmax])
  have hn : M.cycleRank ≤ M.vertexCount := by
    have hh := M.order_add_two_eq_twice_rank_add_deficit hconn hmax
    omega
  have hp := radius_power_lt_rank_of_clog M.cycleRank g hlog
  have hsize : 3*P.card*2^(g/16) < M.vertexCount := by
    have hh := cover_budget_of_square M.cycleRank M.cubicDeficit (g/16) hp hcover
    have hh' := Nat.mul_le_mul_right (2^(g/16)) (Nat.mul_le_mul_left 3 hP)
    exact hh'.trans_lt (hh.trans_le hn)
  obtain ⟨j, hj⟩ := BallLayers.multigraph_exists_large_layer M hconn hmax P hc o (g/16) g
    hg hshort (by omega) hsize
  by_contra hnot
  have hq : (3/5 : ℝ) ≤ affineForestProbability M b := le_of_not_gt hnot
  have hw := hB M P o b hconn hmax hc ho (fun v hv => hb v (hc v hv)) hq j
  have hsquare : (P.card+1)^2 ≤ (M.cubicDeficit+2)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hwidth := hw.trans (Nat.mul_le_mul_left B hsquare)
  have hmul := Nat.mul_le_mul_left (2*(g/16)+1) hwidth
  nlinarith

/-- Both regimes of the affine-pole lemma. The second uses the integer ceiling
of the binary logarithm; a real-log version follows below. -/
theorem exists_constants :
    ∃ D C : ℕ, 256 ≤ D ∧ 64 ≤ C ∧
    ∀ (M : FiniteMultiGraph) (g : ℕ), M.toSimpleGraph.Connected →
      (∀ v, 2 ≤ M.degree v) → (∀ v, M.degree v ≤ 3) →
      ¬ M.HasCycleShorterThan g →
      ((256 ≤ M.cycleRank ∧ M.cubicDeficit ≤ 4*g ∧ D ≤ g) ∨
       ∃ l : ℕ, 4 ≤ l ∧ l ≤ M.cycleRank ∧ M.cubicDeficit ≤ 2*l ∧
         C*Nat.clog 2 (l+2) ≤ g) →
      ∀ b : M.Demand, (∀ v, M.degree v = 3 → b v = 0) →
        affineForestProbability M b ≤ 3/5 := by
  obtain ⟨B, hB⟩ := exists_supported_demand_layer_bound
  obtain ⟨D, hD, hfixed⟩ := exists_fixed_ratio_budget B
  obtain ⟨C, hC, hlogarithmic⟩ := exists_logarithmic_budget B
  refine ⟨D, C, hD, hC, ?_⟩
  intro M g hconn hmin hmax hshort hcase b hb
  rcases hcase with ⟨hr, hk, hg⟩ | ⟨l, hl, hlh, hk, hg⟩
  · have hg3 : 3 ≤ g := by omega
    have hm := multigraph_weighted_moore_integer M g hconn hmin hmax (by omega) hg3 hshort
    rw [edgeCount_eq M hconn hmax (by omega)] at hm
    have hlog := girth_lt_eight_clog M.cycleRank M.cubicDeficit g hr hk hm
    have hbud := hfixed g M.cubicDeficit hg hk
    exact (bound_of_budgets M B hB g hconn hmin hmax (by omega) hg3 hshort hlog
      hbud.1 hbud.2 b hb).le
  · have hbud := hlogarithmic g M.cubicDeficit l hl hk hg
    have hg3 : 3 ≤ g := by omega
    have hm := multigraph_weighted_moore_integer M g hconn hmin hmax (by omega) hg3 hshort
    rw [edgeCount_eq M hconn hmax (by omega)] at hm
    have hlog := girth_lt_eight_clog_of_rank M.cycleRank M.cubicDeficit g (by omega)
      (by omega) hm
    exact (bound_of_budgets M B hB g hconn hmin hmax (by omega) hg3 hshort hlog
      hbud.2.1 hbud.2.2 b hb).le


/-- Ceiling the rank parameter changes the logarithmic budget by at most four. -/
theorem ceil_clog_le_four_logb (l : ℝ) (hl : 4 ≤ l) :
    (Nat.clog 2 (⌈l⌉₊+2) : ℝ) ≤ 4 * Real.logb 2 (l+2) := by
  have hl0 : 0 ≤ l := by linarith
  have hc : (⌈l⌉₊ : ℝ) ≤ 2*l := Nat.ceil_le_two_mul (by linarith)
  have hc' := Nat.le_ceil l
  have hself : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (l+2) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ)≤l+2)
    rwa [hself] at hh
  have hlog' : 1 ≤ Real.logb 2 (⌈l⌉₊+2 : ℕ) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (by push_cast; linarith : (2:ℝ)≤(⌈l⌉₊+2 : ℕ))
    rwa [hself] at hh
  have hmono : Real.logb 2 (⌈l⌉₊+2 : ℕ) ≤ 1 + Real.logb 2 (l+2) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by positivity : (0:ℝ)<(⌈l⌉₊+2 : ℕ))
      (by push_cast; linarith : ((⌈l⌉₊+2 : ℕ):ℝ)≤2*(l+2))
    rw [Real.logb_mul (by norm_num) (by linarith), hself] at hh
    exact hh
  rw [← Real.natCeil_logb_natCast]
  norm_num only [Nat.cast_ofNat]
  have hh := Nat.ceil_le_two_mul (by linarith : (2:ℝ)⁻¹ ≤ Real.logb 2 (⌈l⌉₊+2 : ℕ))
  linarith

/-- The two regimes with the paper's real binary logarithm and real rank
parameter. The constants are absolute and the demand is the actual parity demand. -/
theorem exists_constants_real :
    ∃ D : ℕ, ∃ C : ℝ, 256 ≤ D ∧ 0 < C ∧
    ∀ (M : FiniteMultiGraph) (g : ℕ), M.toSimpleGraph.Connected →
      (∀ v, 2 ≤ M.degree v) → (∀ v, M.degree v ≤ 3) →
      ¬ M.HasCycleShorterThan g →
      ((256 ≤ M.cycleRank ∧ M.cubicDeficit ≤ 4*g ∧ D ≤ g) ∨
       ∃ l : ℝ, 4 ≤ l ∧ l ≤ M.cycleRank ∧ (M.cubicDeficit : ℝ) ≤ 2*l ∧
         C*Real.logb 2 (l+2) ≤ g) →
      ∀ b : M.Demand, (∀ v, M.degree v = 3 → b v = 0) →
        affineForestProbability M b ≤ 3/5 := by
  obtain ⟨D, C, hD, hC, hbound⟩ := exists_constants
  refine ⟨D, 4*C, hD, by positivity, ?_⟩
  intro M g hconn hmin hmax hshort hcase b hb
  apply hbound M g hconn hmin hmax hshort ?_ b hb
  rcases hcase with ha | ⟨l, hl, hlh, hk, hg⟩
  · exact Or.inl ha
  · refine Or.inr ⟨⌈l⌉₊, ?_, ?_, ?_, ?_⟩
    · have hh := Nat.le_ceil l
      exact_mod_cast (show (4:ℝ) ≤ (⌈l⌉₊:ℝ) by linarith)
    · exact Nat.ceil_le.mpr hlh
    · have hh := Nat.le_ceil l
      exact_mod_cast (show (M.cubicDeficit:ℝ) ≤ 2*(⌈l⌉₊:ℝ) by linarith)
    · have hh := mul_le_mul_of_nonneg_left (ceil_clog_le_four_logb l hl)
        (by positivity : (0:ℝ)≤C)
      have hlast : (C:ℝ)*(Nat.clog 2 (⌈l⌉₊+2):ℝ) ≤ (g:ℝ) := by nlinarith
      exact_mod_cast hlast

end Erdos1016.ExactMaximumSupport.LargeGirth.AffinePole

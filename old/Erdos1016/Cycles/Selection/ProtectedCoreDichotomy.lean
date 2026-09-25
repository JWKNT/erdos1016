import Erdos1016.Cycles.Selection.ProtectorCutoffs
import Erdos1016.Cycles.Selection.ApexPackingLift

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.ProtectorCoreDichotomy
open Nonbacktracking CycleSupply SafeCore BoundaryDecay
open CutoffAvoidance EvenTraceParameters ProtectorParameterBounds FewBranchCoreRealization
open CutoffLimits
open ConnectorCutoffLimits
open RejectedCycleEncoding ExternalReturnFilter InducedRetainedCycleFilter

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def manyBound (c n : ℝ) : ℝ :=
  (2 : ℝ) ^ logarithmicGirthCutoff n *
    (manyCycleConflictBound ((c * n ^ (-(1 / 8 : ℝ))) / 2) (logarithmicGirthCutoff n) + 1) /
    polynomialPackingCutoff n

/-- A graph-uniform realization of the manuscript's few/many split. The
protector, physical unsuppressed core and retained family are constructed
from the displayed expansion and deficit bounds. No geometric or trace
conclusion is an input. -/
theorem eventually_many_bound_or_selected_core
    (c B σ : ℝ) (hc : 0 < c) (hB : 0 < B) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H),
      (H.vertexCount : ℝ) = n j → H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      (Nonbacktracking.degreeTwoCount H : ℝ) ≤ B * (n j) ^ (7 / 8 : ℝ) →
      ∃ W₀ : Finset H.Vertex, ConnectedRegion H W₀ ∧ p₀.1 ∈ W₀ ∧
        ((momentK σ (Real.logb 2 (n j)) : ℝ) * cutoffL σ (Real.logb 2 (n j))) /
          ((c * (n j) ^ (-(1 / 8 : ℝ))) / 2) < W₀.card ∧
        ((momentK σ (Real.logb 2 (n j)) : ℝ) * cutoffL σ (Real.logb 2 (n j))) +
          ((momentK σ (Real.logb 2 (n j)) : ℝ) * cutoffL σ (Real.logb 2 (n j))) /
            ((c * (n j) ^ (-(1 / 8 : ℝ))) / 2) < H.vertexCount + 1 ∧
        (coreBoundaryAverage H ≤ manyBound c (n j) ∨
          ∃ W : Finset H.Vertex, ConnectedRegion H W ∧ W₀ ⊆ W ∧
            NoShortCycles H Wᶜ (logarithmicGirthCutoff (n j)) ∧
            W.card ≤ protectorBudget (anchorCount c σ (n j)) (logarithmicGirthCutoff (n j))
              (polynomialPackingCutoff (n j)) (logarithmicConnectorRadius c (n j)) ∧
            ∃ F ⊆ inducedAcceptedCycles (coreGraph H W) Finset.univ
                (shortCycleWords (coreGraph H W) (cutoffL σ (Real.logb 2 (n j))))
                (cutoffQ σ (Real.logb 2 (n j))),
              evenTraceTarget σ (Real.logb 2 (n j)) ≤ cycleWeightSum F ∧
              cycleWeightSum F ≤ evenTraceTarget σ (Real.logb 2 (n j)) +
                1 / (2 : ℝ) ^ (cutoffD (Real.logb 2 (n j)) + 1)) := by
  let x := fun j => Real.logb 2 (n j)
  have hx : Tendsto x atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hn
  have hhlim := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hn).const_mul c
  simp only [mul_zero] at hhlim
  have hbudget := weighted_total_defect_tendsto_zero c B σ hc hσ n hn hnge
  filter_upwards [hn.eventually_gt_atTop 1,
      hhlim.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1),
      hbudget.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      retained_cutoff_budgets σ hσ hσ20 x hx,
      eventually_exists_selected_retained_family σ hσ hσ20 x hx]
    with j hnj hhj hbj hcut hsupply
  intro H p₀ hnH hH hmin hmax hExp hb
  let h := c * (n j) ^ (-(1 / 8 : ℝ))
  let L := cutoffL σ (x j)
  let Km := momentK σ (x j)
  let D := logarithmicGirthCutoff (n j)
  let Kp := polynomialPackingCutoff (n j)
  let a := anchorCount c σ (n j)
  let R := logarithmicConnectorRadius c (n j)
  let w := protectorBudget a D Kp R
  have hnpos : 0 < n j := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := hhj.le
  have hL : (1 : ℝ) ≤ L := by
    have hhL : 1 ≤ L := by dsimp [L, cutoffL, largestOddCutoff]; omega
    exact_mod_cast hhL
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hb0 : 0 ≤ B * (n j) ^ (7 / 8 : ℝ) := by positivity
  have hweighted : (B * (n j) ^ (7 / 8 : ℝ) + 4 * (w : ℝ)) * (L : ℝ) ≤ n j / 2 := by
    exact ((div_le_iff₀ hnpos).mp hbj.le).trans_eq (by ring)
  have hsmall : B * (n j) ^ (7 / 8 : ℝ) + 4 * (w : ℝ) ≤ n j / 2 := by
    have hm := mul_le_mul_of_nonneg_left hL (add_nonneg hb0 (by positivity : 0 ≤ 4 * (w : ℝ)))
    nlinarith
  have hw : (w : ℝ) ≤ n j / 8 := by linarith
  have hR : connectorRadius H h ≤ R := by
    have hhn : 1 ≤ H.vertexCount := by
      have : (1 : ℝ) ≤ H.vertexCount := by rw [hnH]; linarith
      exact_mod_cast this
    have ht := Extremal.connectorRadius_le_ceil_log_over_expansion H h hh hh1 hhn
    simpa only [hnH] using ht
  have hwm : protectorBudget a D Kp (connectorRadius H h) ≤ w := by
    dsimp [protectorBudget, w]
    gcongr
  have haW : a ≤ w := by
    have ht := Nat.le_mul_of_pos_right (a + D * (Kp - 1)) (by omega : 0 < 2 * R + 1)
    dsimp [w, protectorBudget]
    omega
  have haN : a ≤ H.vertexCount := by
    have haR : (a : ℝ) ≤ w := by exact_mod_cast haW
    have : (a : ℝ) ≤ H.vertexCount := by rw [hnH]; linarith
    exact_mod_cast this
  have hKp : 0 < Kp := by
    apply Nat.ceil_pos.mpr
    positivity
  have hsmallG : (Nonbacktracking.degreeTwoCount H : ℝ) +
      4 * (protectorBudget a D Kp (connectorRadius H h) : ℝ) ≤ H.vertexCount / 2 := by
    have hwR : (protectorBudget a D Kp (connectorRadius H h) : ℝ) ≤ w := by exact_mod_cast hwm
    rw [hnH]
    linarith
  have hweightedG : ((Nonbacktracking.degreeTwoCount H : ℝ) +
      3 * (protectorBudget a D Kp (connectorRadius H h) : ℝ)) * L ≤ H.vertexCount / 2 := by
    have hwR : (protectorBudget a D Kp (connectorRadius H h) : ℝ) ≤ w := by exact_mod_cast hwm
    rw [hnH]
    exact (mul_le_mul_of_nonneg_right (by linarith :
      (Nonbacktracking.degreeTwoCount H : ℝ) + 3 * (protectorBudget a D Kp (connectorRadius H h) : ℝ) ≤
        B * (n j) ^ (7 / 8 : ℝ) + 4 * (w : ℝ)) (by positivity : (0 : ℝ) ≤ L)).trans hweighted
  obtain ⟨W₀, hW₀, hp, haW₀, hW₀size, hcases⟩ := many_or_few_core H h hh hExp hmin hmax p₀
    a D Kp L haN hKp hsmallG hweightedG
  have haW₀R : (a : ℝ) ≤ W₀.card := by exact_mod_cast haW₀
  have haWR : (a : ℝ) ≤ w := by exact_mod_cast haW
  have haStrict : 2 * (Km : ℝ) * (L : ℝ) / h < (a : ℝ) := by
    have ht := Nat.lt_floor_add_one (2 * (Km : ℝ) * (L : ℝ) / h)
    simpa [a, anchorCount, Km, L, h, x] using ht
  have hhalf : ((Km : ℝ) * (L : ℝ)) / (h / 2) = 2 * (Km : ℝ) * (L : ℝ) / h := by ring
  have hlarge : ((Km : ℝ) * (L : ℝ)) / (h / 2) < W₀.card := by rw [hhalf]; linarith
  have hmass : 2 * (Km : ℝ) * (L : ℝ) ≤ 2 * (Km : ℝ) * (L : ℝ) / h := by
    apply le_div_self (by positivity) hh hh1
  have hroom : (Km : ℝ) * (L : ℝ) + ((Km : ℝ) * (L : ℝ)) / (h / 2) < H.vertexCount + 1 := by
    rw [hnH, hhalf]
    linarith
  refine ⟨W₀, hW₀, hp, hlarge, hroom, ?_⟩
  rcases hcases with ⟨F, hF, hpack, hsize⟩ | ⟨W, hW, hsub, hcard, hno, hncore, hdcore, hgcore⟩
  · left
    have hD : 2 * (D : ℝ) ≤ (Km : ℝ) * (L : ℝ) := by
      have hxj : 1 ≤ x j := by linarith [hcut.1]
      have hDm : (D : ℝ) ≤ x j / 2 := Nat.floor_le (by linarith)
      have hLm : 6 * x j ≤ (L : ℝ) := (traceStart_bounds hxj).1.trans (by exact_mod_cast hcut.2.2.1)
      have hKm : (1 : ℝ) ≤ Km := by
        have hk : 1 ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) := Nat.one_le_ceil_iff.mpr (by positivity)
        dsimp [Km, momentK]
        push_cast
        have hkR : (1 : ℝ) ≤ Nat.ceil (5 * σ * Real.sqrt (x j)) := by exact_mod_cast hk
        linarith
      nlinarith
    have hne : F.Nonempty := Finset.card_pos.mp (hKp.trans_le hsize)
    have hlen : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D := fun C hC => (mem_shortCycles H W₀ᶜ D C).mp (hF hC) |>.2
    have havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W₀ := by
      intro C hC
      exact Finset.disjoint_left.mpr fun v hv hvW =>
        (Finset.mem_compl.mp (((mem_shortCycles H W₀ᶜ D C).mp (hF hC)).1 hv)) hvW
    have hDdiv : 4 * (D : ℝ) / h ≤ ((Km : ℝ) * (L : ℝ)) / (h / 2) := by
      rw [hhalf]
      exact div_le_div_of_nonneg_right (by linarith) hh.le
    have hm := coreBoundaryAverage_le_many_of_core_packing H hH p₀ hmin hmax h hh hh1 hExp
      W₀ hW₀ hp F hne D hlen hpack havoid (by linarith [hroom]) (by linarith [hlarge])
    apply hm.trans
    change _ ≤ (2 : ℝ) ^ D * (manyCycleConflictBound (h / 2) D + 1) / Kp
    have hkR : (0 : ℝ) < Kp := by exact_mod_cast hKp
    have hsR : (Kp : ℝ) ≤ F.card := by exact_mod_cast hsize
    exact div_le_div_of_nonneg_left (by positivity) hkR hsR
  · right
    refine ⟨W, hW, hsub, hno, hcard.trans hwm, ?_⟩
    apply hsupply (coreGraph H W) Finset.univ (core_min_degree H W) (core_max_degree H W hmax) hncore
    · rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hnpos]
      rw [← hnH]
      exact_mod_cast core_order_le H W
    · exact hdcore
    · exact hgcore

end Erdos1016.Proof.ProtectorCoreDichotomy

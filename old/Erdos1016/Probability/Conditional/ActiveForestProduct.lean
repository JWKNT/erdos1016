import Erdos1016.Probability.Conditional.ActiveRestrictionEvents
import Erdos1016.Probability.Conditional.ComponentEventFactorization
import Erdos1016.Probability.Conditional.RegionProductBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActiveOutsideProbabilityBridge

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.ActiveComponentProbability

theorem activeOutsideEdges_eq_activeComplementEdges (G : PhysicalGraph)
    (E : Finset G.Edge) :
    activeOutsideEdges G E = activeComplementEdges G E := by
  ext e
  simp [activeOutsideEdges, activeComplementEdges, originalActiveEdge]

theorem hostOutsideState_iff_activeOutsideForest (G : PhysicalGraph)
    (E : Finset G.Edge) (x : G.CycleSpace) :
    x ∈ G.outsideLinearForestStates E ↔
      activeOutsideForest G E (cycleSpaceActiveSubgraphEquiv G x) := by
  rw [outsideLinearForestStates_mem_iff_active G E x]
  unfold activeOutsideForest
  change (activeSubgraph G).IsRestrictedLinearForest (activeOutsideEdges G E)
      ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
        (activeWordOfCycle G x)) ↔ _
  rw [activeOutsideEdges_eq_activeComplementEdges]
  rfl

def hostActiveEventEquiv (G : PhysicalGraph) (E : Finset G.Edge) :
    {x : G.CycleSpace // x ∈ G.outsideLinearForestStates E} ≃
      {y : (activeSubgraph G).CycleSpace // activeOutsideForest G E y} where
  toFun x := ⟨cycleSpaceActiveSubgraphEquiv G x.1,
    (hostOutsideState_iff_activeOutsideForest G E x.1).mp x.2⟩
  invFun y := by
    refine ⟨(cycleSpaceActiveSubgraphEquiv G).symm y.1, ?_⟩
    apply (hostOutsideState_iff_activeOutsideForest G E _).mpr
    simpa using y.2
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

theorem outsideLinearForestProbability_eq_activeDensity
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.outsideLinearForestProbability E =
      density (activeOutsideForest G E) := by
  classical
  have hnum : (G.outsideLinearForestStates E).card =
      Fintype.card {y : (activeSubgraph G).CycleSpace //
        activeOutsideForest G E y} := by
    calc
      _ = Fintype.card {x : G.CycleSpace //
          x ∈ G.outsideLinearForestStates E} := by simp
      _ = _ := Fintype.card_congr (hostActiveEventEquiv G E)
  have hdenNat : Fintype.card G.CycleSpace =
      Fintype.card (activeSubgraph G).CycleSpace :=
    Fintype.card_congr (cycleSpaceActiveSubgraphEquiv G)
  have hdenPow : 2 ^ G.cycleRank = Fintype.card (activeSubgraph G).CycleSpace := by
    rw [← G.cycleSpace_card, hdenNat]
  have hnumR : ((G.outsideLinearForestStates E).card : ℝ) =
      (Fintype.card {y : (activeSubgraph G).CycleSpace //
        activeOutsideForest G E y} : ℝ) := by exact_mod_cast hnum
  have hdenR : (2 : ℝ) ^ G.cycleRank =
      (Fintype.card (activeSubgraph G).CycleSpace : ℝ) := by exact_mod_cast hdenPow
  unfold PhysicalGraph.outsideLinearForestProbability density
  rw [hnumR, hdenR]

theorem outsideLinearForestProbability_eq_componentProduct
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.outsideLinearForestProbability E =
      ∏ c : ActiveComponent G,
        density (activeComponentOutsideForest G E c) := by
  rw [outsideLinearForestProbability_eq_activeDensity]
  exact activeOutsideForest_density_eq_prod G E

theorem componentDensity_gt_half_of_hostProbability_gt_half
    (G : PhysicalGraph) (E : Finset G.Edge)
    (hprob : (1 / 2 : ℝ) < G.outsideLinearForestProbability E) :
    ∀ c : ActiveComponent G,
      density (activeComponentOutsideForest G E c) > (1 / 2 : ℝ) := by
  classical
  let p : ActiveComponent G → ℝ := fun c =>
    density (activeComponentOutsideForest G E c)
  have hfactor := outsideLinearForestProbability_eq_componentProduct G E
  have hprob' := hprob
  rw [hfactor] at hprob'
  have hprod : (1 / 2 : ℝ) < ∏ c : ActiveComponent G, p c := by
    simpa [p] using hprob'
  have hp0 : ∀ c, 0 ≤ p c := by
    intro c
    dsimp [p]
    letI : Nonempty
        ((activeSubgraph G).RestrictedCycleSpace (componentEdges G c)) := ⟨0⟩
    exact Erdos1016.Proof.ConditionalProductProbability.localDensity_bounds
      (activeComponentOutsideForest G E c) |>.1
  have hp1 : ∀ c, p c ≤ 1 := by
    intro c
    dsimp [p]
    letI : Nonempty
        ((activeSubgraph G).RestrictedCycleSpace (componentEdges G c)) := ⟨0⟩
    exact Erdos1016.Proof.ConditionalProductProbability.localDensity_bounds
      (activeComponentOutsideForest G E c) |>.2
  intro c
  simpa [p] using ActiveComponentProbability.component_gt_half_of_prod_gt
    p hp0 hp1 hprod c

end Erdos1016.Proof.ActiveOutsideProbabilityBridge

end

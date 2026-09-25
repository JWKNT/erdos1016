import Erdos1016.Extremal.Capacity.CycleLengths
import Erdos1016.CycleSpace.RegionRankLoss
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

/-!
# Elementary final adapters for actual graphs

This reconstructs the missing first-continuation graph adapters using the
single PhysicalGraph API shared by the delivered archives. No reindexing or
GraphCode oracle is needed: PhysicalGraph already has finite labelled types.
-/
noncomputable section
namespace Erdos1016.Extremal
open BoundaryDecay
open Filter
open scoped Topology
local instance elementaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def IsPancyclic (G : PhysicalGraph) : Prop :=
  G.IsConnected ∧ 3 ≤ G.vertexCount ∧ G.IsPancyclic

def edgeExcess (G : PhysicalGraph) : ℝ := (G.edgeCount : ℝ) - G.vertexCount

theorem connected_rank_euler (G : PhysicalGraph) (hG : G.IsConnected) :
    G.cycleRank + G.vertexCount = G.edgeCount + 1 := by
  have hc : G.traceNetwork.graph.Connected := by
    simpa only [G.traceNetwork_graph] using hG
  have h := network_rank_euler G.traceNetwork
  rw [rank_traceNetwork, Fintype.card_fin, Fintype.card_fin,
    connected_component_card G.traceNetwork hc] at h
  exact h

theorem rank_real_eq_excess_add_one (G : PhysicalGraph) (hG : G.IsConnected) :
    (G.cycleRank : ℝ) = edgeExcess G + 1 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (connected_rank_euler G hG)
  push_cast at h
  unfold edgeExcess
  linarith

/-- Empty initial coverage is realized, so the logarithm of capacity is positive-domain. -/
def emptyGraph : PhysicalGraph where
  vertexCount := 0
  edgeCount := 0
  src := Fin.elim0
  dst := Fin.elim0
  noLoops e := Fin.elim0 e
  simple e := Fin.elim0 e

theorem emptyGraph_rank : emptyGraph.cycleRank = 0 := by
  unfold PhysicalGraph.cycleRank
  haveI : Subsingleton emptyGraph.Word := ⟨fun f g => funext (fun e => Fin.elim0 e)⟩
  haveI : Subsingleton emptyGraph.CycleSpace := inferInstance
  exact Module.finrank_zero_of_subsingleton

theorem initialCapacity_two_le (r : ℕ) : 2 ≤ initialCapacity r := by
  apply coverage_le_initialCapacity emptyGraph
  · rw [emptyGraph_rank]
    omega
  · intro n hn
    have h := Finset.mem_Icc.1 hn
    omega











end Erdos1016.Extremal

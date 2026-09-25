import Erdos1016.Decomposition.TwoCore.MaximalCore
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

/-!
# Cycles are supported on the finite 2-core

This is the graph-theoretic support lemma used by the §9 core transfer.  It is
stated for an arbitrary selected simple graph sitting inside the ambient
simple graph; in the cleanup application, the selected graph is the internal
restriction of a cycle-space word.
-/

noncomputable section

namespace Erdos1016.Proof.CycleSupport

open Erdos1016.Nonbacktracking.FiniteTwoCore

local instance coreCycleSupportDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The support vertices of a selected cycle form a minimum-degree-two set in
the ambient induced region, hence are contained in its maximal finite
2-core. -/
theorem cycle_support_subset_twoCore
    (J S : SimpleGraph V) (region : Finset V)
    (hSJ : S ≤ J)
    {u : V} (p : S.Walk u u) (hp : p.IsCycle)
    (hsupport : ∀ v ∈ p.support, v ∈ region) :
    p.toSubgraph.verts.toFinset ⊆ vertices J region := by
  classical
  let A : Finset V := p.toSubgraph.verts.toFinset
  have hAsub : A ⊆ region := by
    intro v hv
    have hvvert : v ∈ p.toSubgraph.verts :=
      Set.mem_toFinset.mp (show v ∈ p.toSubgraph.verts.toFinset from hv)
    have hv' : v ∈ p.support := (p.mem_verts_toSubgraph).1 hvvert
    exact hsupport v hv'
  have hAmin : MinTwo J A := by
    intro v hv
    have hvvert : v ∈ p.toSubgraph.verts :=
      Set.mem_toFinset.mp (show v ∈ p.toSubgraph.verts.toFinset from hv)
    have hvsupport : v ∈ p.support := (p.mem_verts_toSubgraph).1 hvvert
    have hcycleNbr : (p.toSubgraph.neighborSet v).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_eq_two hvsupport
    have hsub : p.toSubgraph.neighborSet v ⊆
        {w | w ∈ A ∧ J.Adj v w} := by
      intro w hw
      have hAdj : p.toSubgraph.Adj v w := hw
      have hwvert : w ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hAdj.symm
      have hwsupport : w ∈ p.support := (p.mem_verts_toSubgraph).1 hwvert
      have hwA : w ∈ A := by
        change w ∈ p.toSubgraph.verts.toFinset
        exact Set.mem_toFinset.mpr hwvert
      refine ⟨hwA, ?_⟩
      exact hSJ (p.toSubgraph.adj_sub hAdj)
    have hcard : (p.toSubgraph.neighborSet v).ncard ≤
        ({w | w ∈ A ∧ J.Adj v w} : Set V).ncard :=
      Set.ncard_le_ncard hsub
    have htarget : ({w | w ∈ A ∧ J.Adj v w} : Set V).ncard =
        degreeWithin J A v := by
      classical
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      have hset : {w | w ∈ A ∧ J.Adj v w} =
          (A.filter fun w => J.Adj v w : Finset V) := by
        ext w
        simp [and_comm]
      calc
        Fintype.card {w // w ∈ {w | w ∈ A ∧ J.Adj v w}} =
            Fintype.card {w // w ∈ (A.filter fun w => J.Adj v w : Finset V)} :=
          Fintype.card_congr (Equiv.setCongr hset)
        _ = (A.filter fun w => J.Adj v w).card := Fintype.card_coe _
        _ = degreeWithin J A v := by simp [degreeWithin]
    rw [hcycleNbr, htarget] at hcard
    exact hcard
  exact maximal J region A hAsub hAmin

/-- Transfer a particular walk along an edge map which is only known to be
defined on the vertices visited by that walk. -/
def transferWalkToSubgraph
    {S T : SimpleGraph V} (K : Finset V)
    (edgeMap : ∀ {a b}, S.Adj a b → a ∈ K → b ∈ K → T.Adj a b) :
    ∀ {u v} (p : S.Walk u v), (∀ w ∈ p.support, w ∈ K) → T.Walk u v
  | _, _, .nil, _ => .nil
  | _, _, .cons h p, hs =>
      .cons (edgeMap h (hs _ (by simp)) (hs _ (by simp)))
        (transferWalkToSubgraph K edgeMap p (by
          intro w hw
          exact hs w (by simp [hw])))









end Erdos1016.Proof.CycleSupport

end

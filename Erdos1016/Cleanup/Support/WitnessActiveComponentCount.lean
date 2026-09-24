import Erdos1016.Extremal.Capacity.ComponentWitnessCoverage
import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

/-!
# A cleanup witness can meet only finitely many active components

If the outside forest probability exceeds one half, every edge-bearing active
component meets the witness edge set. Since each connected component of the
witness graph lies inside one active component, the witness component count
bounds the number of active components that carry witness edges.
-/

noncomputable section

namespace Erdos1016.Proof.WitnessActiveComponentCount

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.CleanupSpecification

local instance witnessActiveCountDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {G : PhysicalGraph}

private abbrev InputWitnessGraph (I : CleanupInput G) :=
  witnessGraph G I.witnessVertices I.witnessEdges

private abbrev InputWitnessInduce (I : CleanupInput G) :=
  (InputWitnessGraph I).induce (↑I.witnessVertices : Set G.Vertex)

private noncomputable def pickedWitnessEdge
    (I : CleanupInput G)
    (c : {c : ActiveComponent G // (componentEdges G c).Nonempty}) :
    (activeSubgraph G).Edge :=
  Classical.choose
    (every_nonempty_activeComponent_meets_witness G I.witnessEdges
      (by
        have hinv : 0 ≤ (1 / (I.R : ℝ)) := by positivity
        linarith [I.outside_probability]) c.1 c.2)

private theorem pickedWitnessEdge_spec
    (I : CleanupInput G)
    (c : {c : ActiveComponent G // (componentEdges G c).Nonempty}) :
    pickedWitnessEdge I c ∈ componentEdges G c.1 ∧
      (G.restrictedEdgeEquiv (activeEdges G) (pickedWitnessEdge I c)).1 ∈
        I.witnessEdges :=
  Classical.choose_spec
    (every_nonempty_activeComponent_meets_witness G I.witnessEdges
      (by
        have hinv : 0 ≤ (1 / (I.R : ℝ)) := by positivity
        linarith [I.outside_probability]) c.1 c.2)

private theorem witness_induce_adj_maps_to_active_adj
    (I : CleanupInput G)
    {u v : {v : G.Vertex // v ∈ I.witnessVertices}}
    (h : (InputWitnessInduce I).Adj u v) :
    (activeSubgraph G).toSimpleGraph.Adj u.1 v.1 := by
  classical
  let J := InputWitnessGraph I
  change J.Adj u.1 v.1 at h
  rcases h with ⟨_, _, hne, e, he, hend⟩
  obtain ⟨x, hx⟩ := I.witness_edges_active e he
  have hactive : ActiveEdgeUniform.ActiveEdge G e :=
    active_of_cycle_coordinate_ne_zero G x e hx
  have heactive : e ∈ activeEdges G :=
    (mem_activeEdges_iff G e).2 hactive
  let ea : (activeSubgraph G).Edge :=
    (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨e, heactive⟩
  have hcoord : (G.restrictedEdgeEquiv (activeEdges G) ea).1 = e := by
    exact congrArg Subtype.val
      ((G.restrictedEdgeEquiv (activeEdges G)).apply_symm_apply ⟨e, heactive⟩)
  have hsrc : (activeSubgraph G).src ea = G.src e := by
    change G.src (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
    rw [hcoord]
  have hdst : (activeSubgraph G).dst ea = G.dst e := by
    change G.dst (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
    rw [hcoord]
  change ∃ f : (activeSubgraph G).Edge,
    (fun _ : (activeSubgraph G).Edge => (1 : ZMod 2)) f ≠ 0 ∧
      (((activeSubgraph G).src f = u.1 ∧ (activeSubgraph G).dst f = v.1) ∨
       ((activeSubgraph G).src f = v.1 ∧ (activeSubgraph G).dst f = u.1))
  refine ⟨ea, ?_, ?_⟩
  · norm_num
  · rw [hsrc, hdst]
    exact hend

private noncomputable def witnessComponentOfActive
    (I : CleanupInput G)
    (c : {c : ActiveComponent G // (componentEdges G c).Nonempty}) :
    (InputWitnessInduce I).ConnectedComponent := by
  classical
  let e := pickedWitnessEdge I c
  let eOriginal := (G.restrictedEdgeEquiv (activeEdges G) e).1
  have heWitness : eOriginal ∈ I.witnessEdges :=
    (pickedWitnessEdge_spec I c).2
  let hends := I.witness_endpoints eOriginal heWitness
  exact (InputWitnessInduce I).connectedComponentMk
    ⟨G.src eOriginal, hends.1⟩

private theorem picked_source_active_component
    (I : CleanupInput G)
    (c : {c : ActiveComponent G // (componentEdges G c).Nonempty}) :
    componentOf G (G.src (G.restrictedEdgeEquiv (activeEdges G)
      (pickedWitnessEdge I c)).1) = c.1 := by
  have heComp : pickedWitnessEdge I c ∈ componentEdges G c.1 :=
    (pickedWitnessEdge_spec I c).1
  have hcomp : edgeComponent G (pickedWitnessEdge I c) = c.1 :=
    (mem_componentEdges_iff G c.1 (pickedWitnessEdge I c)).1 heComp
  change componentOf G ((activeSubgraph G).src (pickedWitnessEdge I c)) = c.1 at hcomp
  have hsrc : (activeSubgraph G).src (pickedWitnessEdge I c) =
      G.src (G.restrictedEdgeEquiv (activeEdges G)
        (pickedWitnessEdge I c)).1 := by
    rfl
  rw [hsrc] at hcomp
  exact hcomp

private theorem witnessComponentOfActive_injective (I : CleanupInput G) :
    Function.Injective (witnessComponentOfActive I) := by
  classical
  intro c d hcd
  let Q := InputWitnessInduce I
  let hom : Q →g (activeSubgraph G).toSimpleGraph := {
    toFun := fun v => v.1
    map_rel' := by
      intro u v huv
      exact witness_induce_adj_maps_to_active_adj I huv
  }
  have hreach : Q.Reachable
      ⟨G.src (G.restrictedEdgeEquiv (activeEdges G)
        (pickedWitnessEdge I c)).1,
        (I.witness_endpoints
          (G.restrictedEdgeEquiv (activeEdges G) (pickedWitnessEdge I c)).1
          (pickedWitnessEdge_spec I c).2).1⟩
      ⟨G.src (G.restrictedEdgeEquiv (activeEdges G)
        (pickedWitnessEdge I d)).1,
        (I.witness_endpoints
          (G.restrictedEdgeEquiv (activeEdges G) (pickedWitnessEdge I d)).1
          (pickedWitnessEdge_spec I d).2).1⟩ := by
    exact SimpleGraph.ConnectedComponent.exact hcd
  obtain ⟨p⟩ := hreach
  have hactiveReach :
      (activeSubgraph G).toSimpleGraph.Reachable
        (G.src (G.restrictedEdgeEquiv (activeEdges G)
          (pickedWitnessEdge I c)).1)
        (G.src (G.restrictedEdgeEquiv (activeEdges G)
          (pickedWitnessEdge I d)).1) := by
    simpa using (p.map hom).reachable
  have hactiveComp := SimpleGraph.ConnectedComponent.sound hactiveReach
  have hsrcC := picked_source_active_component I c
  have hsrcD := picked_source_active_component I d
  change componentOf G _ = componentOf G _ at hactiveComp
  rw [hsrcC, hsrcD] at hactiveComp
  exact Subtype.ext hactiveComp

/-- The active connected components carrying at least one edge are no more
numerous than the cleanup witness's connected components. -/
theorem nonempty_active_component_card_le_witness_component_count
    (I : CleanupInput G) :
    Fintype.card {c : ActiveComponent G // (componentEdges G c).Nonempty} ≤
      witnessComponentCount G I.witnessVertices I.witnessEdges := by
  classical
  have hcard : Nat.card {c : ActiveComponent G // (componentEdges G c).Nonempty} ≤
      Nat.card (InputWitnessInduce I).ConnectedComponent :=
    Finite.card_le_of_injective (witnessComponentOfActive I)
      (witnessComponentOfActive_injective I)
  unfold witnessComponentCount
  simpa only [Nat.card_eq_fintype_card] using hcard

/-- In particular, the witness component budget screens the number of
edge-bearing active components by the cleanup scale. -/
theorem nonempty_active_component_card_lt_five_R
    (I : CleanupInput G)
    (hcomponents : witnessComponentCount G I.witnessVertices I.witnessEdges <
      5 * I.R) :
    Fintype.card {c : ActiveComponent G // (componentEdges G c).Nonempty} <
      5 * I.R :=
  (nonempty_active_component_card_le_witness_component_count I).trans_lt hcomponents

end Erdos1016.Proof.WitnessActiveComponentCount

end

import Erdos1016.Graph.Cubicization.IncidenceMarkedCore
import Erdos1016.Graph.ConnectedCover

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The incidence expansion with the actual union of finitely many cycle witnesses. -/

noncomputable section

namespace Erdos1016.ShortProof.IncidencePaths

local instance incidenceWitnessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (F : Finset G.CycleWord)

theorem cycleWitness_degree_condition (v : G.Vertex) :
    witnessCount G (witnessSupportEdges G F) v = 0 ∨
      2 ≤ witnessCount G (witnessSupportEdges G F) v := by
  by_cases hz : witnessCount G (witnessSupportEdges G F) v = 0
  · exact Or.inl hz
  right
  have hpos := Nat.pos_of_ne_zero hz
  rw [witnessCount_eq_filter_card] at hpos
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  obtain ⟨heW, heinc⟩ := Finset.mem_filter.mp he
  obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp heW
  have heC' : C.1 e ≠ 0 := (Finset.mem_filter.mp heC).2
  have hv : v ∈ G.usedVertices C.1 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, heC', heinc⟩
  have hd : G.selectedDegree C.1 v = 2 := C.2.2.2.2 v hv
  rw [← hd, witnessCount_eq_filter_card]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨_, hfc, hfinc⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_filter.mpr ⟨witnessSupport_edge_mem G F hC
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfc⟩), hfinc⟩

theorem cycleWitness_marked_min_degree_two
    (a : {v // v ∈ markedVertices G (witnessSupportEdges G F)}) :
    2 ≤ ((physical G (witnessSupportEdges G F)).toSimpleGraph.induce
      (↑(markedVertices G (witnessSupportEdges G F)) :
        Set (physical G (witnessSupportEdges G F)).Vertex)).degree a :=
  marked_physical_min_degree_two G (witnessSupportEdges G F) (cycleWitness_degree_condition G F) a

lemma witnessCount_pos_iff_cycleUnion (v : G.Vertex) :
    0 < witnessCount G (witnessSupportEdges G F) v ↔ v ∈ cycleUnionVertices G F := by
  rw [witnessCount_eq_filter_card, Finset.card_pos]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨heW, heinc⟩ := Finset.mem_filter.mp he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp heW
    apply Finset.mem_biUnion.mpr
    exact ⟨C, hC, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, e, (Finset.mem_filter.mp heC).2, heinc⟩⟩
  · intro hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨e, he, heinc⟩ := (Finset.mem_filter.mp hvC).2
    exact ⟨e, Finset.mem_filter.mpr ⟨witnessSupport_edge_mem G F hC
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩), heinc⟩⟩

lemma witnessSupport_graph : (witnessSupportGraph G F).toSimpleGraph =
    G.selectedGraph (fun e => if e ∈ witnessSupportEdges G F then 1 else 0) := by
  ext u v
  constructor
  · rintro ⟨e, _, hend⟩
    let f := (Finset.equivFin (witnessSupportEdges G F)).symm e
    refine ⟨f.1, ?_, hend⟩
    simp only [if_pos f.2, ne_eq, one_ne_zero, not_false_eq_true]
  · rintro ⟨e, he, hend⟩
    have heW : e ∈ witnessSupportEdges G F := by
      by_contra hn
      simp only [if_neg hn, ne_eq, not_true_eq_false] at he
    let f := Finset.equivFin (witnessSupportEdges G F) ⟨e, heW⟩
    refine ⟨f, one_ne_zero, ?_⟩
    simpa only [witnessSupportGraph, f, Equiv.symm_apply_apply] using hend

def supportCycleUnionIso : supportGraph G (witnessSupportEdges G F) ≃g cycleUnionGraph G F where
  toEquiv := {
    toFun v := ⟨v.1, (witnessCount_pos_iff_cycleUnion G F v.1).mp v.2⟩
    invFun v := ⟨v.1, (witnessCount_pos_iff_cycleUnion G F v.1).mpr v.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  map_rel_iff' := by
    intro a b
    change (witnessSupportGraph G F).toSimpleGraph.Adj a.1 b.1 ↔
      (G.selectedGraph (fun e => if e ∈ witnessSupportEdges G F then 1 else 0)).Adj a.1 b.1
    rw [witnessSupport_graph]

/-- The actual union of `F.card` cycle witnesses gives at most `F.card`
marked components in the expanded physical graph. -/
theorem cycleWitness_marked_component_count_le :
    Nat.card ((physical G (witnessSupportEdges G F)).toSimpleGraph.induce
      (↑(markedVertices G (witnessSupportEdges G F)) :
        Set (physical G (witnessSupportEdges G F)).Vertex)).ConnectedComponent ≤ F.card := by
  calc
    _ ≤ Nat.card (supportGraph G (witnessSupportEdges G F)).ConnectedComponent :=
      marked_physical_component_count_le G (witnessSupportEdges G F)
    _ = Nat.card (cycleUnionGraph G F).ConnectedComponent :=
      Nat.card_congr (supportCycleUnionIso G F).connectedComponentEquiv
    _ ≤ F.card := cycleUnion_component_count_le G F

end Erdos1016.ShortProof.IncidencePaths

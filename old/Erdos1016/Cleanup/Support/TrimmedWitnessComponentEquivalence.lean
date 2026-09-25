import Erdos1016.Cleanup.CleanupSpecification
import Erdos1016.Extremal.Capacity.TrimmedWitnessNetwork

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.TrimmedWitnessComponentEquivalence

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.Proof.TrimmedWitnessNetworkIso
open Erdos1016.Proof.Capacity

local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := Fintype.ofFinite _

/-- The cleanup witness graph on its endpoint set is the same graph as the
induced support graph, up to the identity map on endpoint vertices. -/
def witnessGraph_induce_iso_supportGraph_induce
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    ((witnessGraph G (witnessSupportVertices G F) (witnessSupportEdges G F)).induce
      (↑(witnessSupportVertices G F) : Set G.Vertex)) ≃g
    ((witnessSupportGraph G F).toSimpleGraph.induce
      (↑(witnessSupportVertices G F) : Set G.Vertex)) := by
  classical
  have hAdj (u v : {x : G.Vertex // x ∈ (↑(witnessSupportVertices G F) : Set G.Vertex)}) :
      (witnessGraph G (witnessSupportVertices G F)
        (witnessSupportEdges G F)).Adj u.1 v.1 ↔
      (witnessSupportGraph G F).toSimpleGraph.Adj u.1 v.1 := by
    simp only [witnessGraph, SimpleGraph.Adj]
    constructor
    · rintro ⟨_, _, hne, e, he, hend | hend⟩
      · refine ⟨(Finset.equivFin (witnessSupportEdges G F)) ⟨e, he⟩,
          one_ne_zero, ?_⟩
        simpa [witnessSupportGraph] using Or.inl hend
      · refine ⟨(Finset.equivFin (witnessSupportEdges G F)) ⟨e, he⟩,
          one_ne_zero, ?_⟩
        simpa [witnessSupportGraph] using Or.inr hend
    · rintro ⟨e, _, hend | hend⟩
      · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
        have hq : q ∈ witnessSupportEdges G F :=
          ((Finset.equivFin (witnessSupportEdges G F)).symm e).2
        refine ⟨u.2, v.2, ?_, q, hq, ?_⟩
        · intro heq
          have hs : G.src q = u.1 := by
            simpa [witnessSupportGraph, q] using hend.1
          have ht : G.dst q = v.1 := by
            simpa [witnessSupportGraph, q] using hend.2
          exact G.noLoops q (hs.trans (heq.trans ht.symm))
        · exact Or.inl ⟨by simpa [witnessSupportGraph, q] using hend.1,
            by simpa [witnessSupportGraph, q] using hend.2⟩
      · let q := ((Finset.equivFin (witnessSupportEdges G F)).symm e).1
        have hq : q ∈ witnessSupportEdges G F :=
          ((Finset.equivFin (witnessSupportEdges G F)).symm e).2
        refine ⟨u.2, v.2, ?_, q, hq, ?_⟩
        · intro heq
          have hs : G.src q = v.1 := by
            simpa [witnessSupportGraph, q] using hend.1
          have ht : G.dst q = u.1 := by
            simpa [witnessSupportGraph, q] using hend.2
          exact G.noLoops q (hs.trans (heq.symm.trans ht.symm))
        · exact Or.inr ⟨by simpa [witnessSupportGraph, q] using hend.1,
            by simpa [witnessSupportGraph, q] using hend.2⟩
  refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
  intro u v
  change (witnessSupportGraph G F).toSimpleGraph.Adj u.1 v.1 ↔
    (witnessGraph G (witnessSupportVertices G F)
      (witnessSupportEdges G F)).Adj u.1 v.1
  exact (hAdj u v).symm

/-- The canonical witness support's component count equals the component
count required by CleanupInput when the witness vertices are their actual
support endpoints. -/
theorem witnessComponentCount_eq_trimmed
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    witnessComponentCount G (witnessSupportVertices G F)
        (witnessSupportEdges G F) =
      Fintype.card (trimmedWitnessGraph G F).traceNetwork.Component := by
  classical
  unfold witnessComponentCount
  let V := witnessSupportVertices G F
  let W := witnessSupportGraph G F
  let T := trimmedWitnessGraph G F
  let e₁ := witnessGraph_induce_iso_supportGraph_induce G F
  let e₂ := witnessSupport_induced_trimmed_iso G F
  letI : Fintype T.toSimpleGraph.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype T.traceNetwork.Component := Fintype.ofFinite _
  have e : ((witnessGraph G V (witnessSupportEdges G F)).induce
      (↑V : Set G.Vertex)) ≃g T.toSimpleGraph := e₁.trans e₂
  let eComp :
      (((witnessGraph G V (witnessSupportEdges G F)).induce
        (↑V : Set G.Vertex)).ConnectedComponent) ≃
        T.toSimpleGraph.ConnectedComponent := e.connectedComponentEquiv
  let eTrace : T.traceNetwork.Component ≃ T.toSimpleGraph.ConnectedComponent :=
    Equiv.cast (congrArg (fun Q : SimpleGraph T.Vertex => Q.ConnectedComponent)
      T.traceNetwork_graph)
  exact Fintype.card_congr (eComp.trans eTrace.symm)

end Erdos1016.Proof.TrimmedWitnessComponentEquivalence

end

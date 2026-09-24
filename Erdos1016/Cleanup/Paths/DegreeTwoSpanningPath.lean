import Erdos1016.Cycles.Geometry.DegreeTwoTreePaths
import Erdos1016.Cleanup.Protection.UnprotectedDegreeTwoAcyclicity

set_option autoImplicit false

namespace Erdos1016.Proof.DegreeTwoSpanningPath

open Erdos1016
open SimpleGraph

/-- Each connected component of the induced graph on unprotected vertices is
a path: it is a tree by the induced acyclicity theorem, and its degrees are at
most two because its vertices have ambient degree two. The path visits the
whole component, including the singleton case. -/
theorem exists_component_spanning_path
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent) :
    ∃ a b, ∃ p :
        ((G.toSimpleGraph.induce {v | v ∉ P}).induce c.supp).Walk a b,
      p.IsPath ∧ ∀ v, v ∈ p.support := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let H : SimpleGraph U := G.toSimpleGraph.induce U
  let K : SimpleGraph c.supp := H.induce c.supp
  have hHacyc : H.IsAcyclic := by
    simpa [H, U] using
      UnprotectedDegreeTwoAcyclicity.induced_unprotected_isAcyclic
        G P hconn hP hdegree
  have htree : K.IsTree := by
    refine ⟨c.connected_induce_supp, ?_⟩
    intro a p hp
    let emb : K ↪g H := @SimpleGraph.Embedding.induce U H c.supp
    exact hHacyc (p.map emb.toHom) (hp.map emb.injective)
  have hdegreeK : ∀ v : c.supp, (K.neighborFinset v).card ≤ 2 := by
    intro v
    have hKcard : (K.neighborFinset v).card =
        (H.neighborFinset v.1 ∩ c.supp.toFinset).card := by
      rw [← Finset.card_map (Function.Embedding.subtype c.supp)]
      rw [SimpleGraph.map_neighborFinset_induce]
    have hHcard : (H.neighborFinset v.1).card =
        (G.toSimpleGraph.neighborFinset v.1.1 ∩ U.toFinset).card := by
      rw [← Finset.card_map (Function.Embedding.subtype U)]
      rw [SimpleGraph.map_neighborFinset_induce]
    calc
      (K.neighborFinset v).card =
          (H.neighborFinset v.1 ∩ c.supp.toFinset).card := hKcard
      _ ≤ (H.neighborFinset v.1).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = (G.toSimpleGraph.neighborFinset v.1.1 ∩ U.toFinset).card := hHcard
      _ ≤ (G.toSimpleGraph.neighborFinset v.1.1).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree v.1.1 :=
          (PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v.1.1).symm
      _ = 2 := hdegree v.1.1 v.1.2
  exact FiniteTreeDegreeTwoPath.exists_spanning_path K htree.isConnected
    htree.IsAcyclic hdegreeK

end Erdos1016.Proof.DegreeTwoSpanningPath

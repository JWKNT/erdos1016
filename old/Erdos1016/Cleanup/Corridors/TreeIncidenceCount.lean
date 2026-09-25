import Erdos1016.Cleanup.Corridors.DegreeTwoComponentCut
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

namespace Erdos1016.Proof.TreeIncidenceCount

open Erdos1016
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of the internal incidences of a nonempty finite vertex set whose
induced graph is a tree is the usual tree degree sum. -/
theorem internal_incidence_sum_eq_tree_value
    (H : SimpleGraph V) [DecidableRel H.Adj] (C : Finset V)
    (hconn : (H.induce (↑C : Set V)).Connected)
    (hacyc : (H.induce (↑C : Set V)).IsAcyclic) :
    (∑ v ∈ C, (H.neighborFinset v ∩ C).card) = 2 * (C.card - 1) := by
  classical
  letI : Fintype {v : V // v ∈ (↑C : Set V)} := FinsetCoe.fintype C
  let K := H.induce (↑C : Set V)
  have htree : K.IsTree := ⟨hconn, hacyc⟩
  have hcard := htree.card_edgeFinset
  have hsum := K.sum_degrees_eq_twice_card_edges
  have hdeg (v : ↑(↑C : Set V)) :
      K.degree v = (H.neighborFinset v.1 ∩ C).card := by
    calc
      K.degree v = (K.neighborFinset v).card :=
        (K.card_neighborFinset_eq_degree v).symm
      _ = ((K.neighborFinset v).map
          (Function.Embedding.subtype (↑C : Set V))).card := by
        rw [Finset.card_map]
      _ = (H.neighborFinset v.1 ∩ C).card := by
        have hm' : Finset.map (Function.Embedding.subtype (↑C : Set V))
            (K.neighborFinset v) = H.neighborFinset v.1 ∩ C := by
          ext w
          simp only [Finset.mem_map, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset, K]
          constructor
          · rintro ⟨⟨x, hx⟩, hAdj, rfl⟩
            exact ⟨hAdj, hx⟩
          · rintro ⟨hAdj, hx⟩
            exact ⟨⟨w, hx⟩, hAdj, rfl⟩
        rw [hm']
  have hsum' :
      (∑ v ∈ C, (H.neighborFinset v ∩ C).card) =
        ∑ v : ↑(↑C : Set V), K.degree v := by
    rw [Finset.sum_subtype C (by intro v; rfl)]
    apply Finset.sum_congr rfl
    intro v hv
    exact (hdeg ⟨v, by simp [K]⟩).symm
  have hvertices : Fintype.card ↑(↑C : Set V) = C.card := by
    simp [Fintype.card_coe]
  calc
    _ = ∑ v : ↑(↑C : Set V), K.degree v := hsum'
    _ = 2 * K.edgeFinset.card := hsum
    _ = 2 * (C.card - 1) := by rw [hvertices] at hcard; omega



end Erdos1016.Proof.TreeIncidenceCount

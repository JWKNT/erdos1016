import Erdos1016.ExactMaximumSupport.CubicReduction.CoreCycles
import Erdos1016.Graph.Suppression.MarkedCorridors
import Erdos1016.Graph.Multigraph.SubcubicOrder

set_option autoImplicit false

/-!
# A cubic model for a connected subcubic core

Rank at least two supplies a degree-three vertex. Marking all such vertices
lets the existing corridor construction suppress every degree-two vertex.
This file records the graph, degree, and rank conclusions. Cycle-count
transport through those corridors is a separate obligation.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof.CycleCore

variable (G : PhysicalGraph)

theorem asMultigraph_toSimpleGraph : (asMultigraph G).toSimpleGraph = G.toSimpleGraph := by
  ext u v
  constructor
  · rintro ⟨_, e, h⟩
    exact ⟨e, one_ne_zero, h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨?_, e, h⟩
    exact G.toSimpleGraph.ne_of_adj ⟨e, he, h⟩

theorem asMultigraph_cycleRank : (asMultigraph G).cycleRank = G.cycleRank :=
  (physicalMultigraphEquiv G).symm.finrank_eq

def cubicVertices : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v => G.degree v = 3

theorem cubicVertices_nonempty (hconn : G.IsConnected)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 2 ≤ G.cycleRank) : (cubicVertices G).Nonempty := by
  classical
  by_contra hn
  have htwo (v : G.Vertex) : G.degree v = 2 := by
    have hnot : G.degree v ≠ 3 := by
      intro hv
      apply hn
      exact ⟨v, by simp [cubicVertices, hv]⟩
    have hlo := hmin v
    have hhi := hmax v
    omega
  have hdegree (v : (asMultigraph G).Vertex) : (asMultigraph G).degree v = 2 := by
    change (asMultigraph G).selectedDegree (fun _ => 1) v = 2
    rw [asMultigraph_selectedDegree]
    exact htwo v
  have hsum : 2 * G.vertexCount = 2 * G.edgeCount := by
    calc
      _ = ∑ _v : (asMultigraph G).Vertex, (2 : ℕ) := by simp [asMultigraph, Nat.mul_comm]
      _ = ∑ v : (asMultigraph G).Vertex, (asMultigraph G).degree v := by simp [hdegree]
      _ = _ := (asMultigraph G).sum_degree
  have hc : (asMultigraph G).toSimpleGraph.Connected := by
    rw [asMultigraph_toSimpleGraph]
    exact hconn
  have heuler := (asMultigraph G).connected_euler hc
  rw [asMultigraph_cycleRank] at heuler
  change G.cycleRank + G.vertexCount = G.edgeCount + 1 at heuler
  omega

theorem exists_cubic_of_subcubic_core (hconn : G.IsConnected)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hr : 2 ≤ G.cycleRank) :
    ∃ M : FiniteMultiGraph, M.toSimpleGraph.Connected ∧ M.IsCubic ∧
      M.cycleRank = G.cycleRank := by
  classical
  let P := cubicVertices G
  have hP : P.Nonempty := cubicVertices_nonempty G hconn hmin hmax hr
  have hd (v : G.Vertex) (_hv : v ∉ P) : G.degree v = 2 ∨ G.degree v = 3 := by
    have hlo := hmin v
    have hhi := hmax v
    omega
  let M := ShortProof.MarkedCorridors.graph G P hconn hP hd
  refine ⟨M, ShortProof.MarkedCorridors.connected G P hconn hP hd, ?_,
    ShortProof.MarkedCorridors.cycleRank_preserved G P hconn hP hd⟩
  intro v
  rw [ShortProof.MarkedCorridors.degree_preserved]
  have hv := ShortProof.MarkedCorridors.vertexMap_retained G P hconn hP hd v
  simpa only [Proof.PhysicalDegreeTwoCoreComponents.protectedOrBranch, P, cubicVertices,
    Finset.union_self, Finset.mem_filter, Finset.mem_univ, true_and] using hv

end Erdos1016.ExactMaximumSupport.CubicReduction

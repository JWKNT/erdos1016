import Erdos1016.Nonbacktracking.Girth.BreadthFirstLayers
import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.Decomposition.TwoCore.PhysicalCore

set_option autoImplicit false

noncomputable section

/-!
# Section 8.1: physical no-short-cycle adapter

The layer argument is formulated for an ordinary induced simple graph. This
adapter consumes the paper's physical `NoShortCycles` hypothesis on a finite
target region and feeds the resulting girth statement and ambient cubic
degrees into the actual-contact theorem.
-/

namespace Erdos1016.Proof.InducedBoundaryContacts

open Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.Proof.BreadthFirstLayers

local instance boundaryContactDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The three-contact conclusion for an actual physical target region. The
target must be connected (as in the paper's connected-region setup), while
short cycles are excluded in the target by the physical cycle-word
hypothesis. Ambient degree three supplies the literal outgoing contacts. -/
theorem physical_induced_target_three_contacts_of_small_order
    (G : Erdos1016.PhysicalGraph) (U : Finset G.Vertex)
    (hreg : ∀ v ∈ U, G.degree v = 3)
    (hconn : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (D r : ℕ)
    (hno : Erdos1016.CycleSupply.NoShortCycles G U D)
    (hD : 2 * r + 1 ≤ D)
    (root : U)
    (hsmall : (U.card : ℝ) < 2 ^ r) :
    2 < ∑ k ∈ Finset.range r,
      ∑ v ∈ bfsLayer (G.toSimpleGraph.induce (↑U : Set G.Vertex)) root k,
        (((G.toSimpleGraph.neighborFinset v.1).filter
          (fun w => w ∉ U)).card : ℝ) := by
  classical
  let J := G.toSimpleGraph.induce (↑U : Set G.Vertex)
  have hg : GirthGreater J D := by
    exact Erdos1016.Nonbacktracking.girthGreater_induce_of_noShortCycles G U D hno
  have hreg' : ∀ v : {v : G.Vertex // v ∈ (↑U : Set G.Vertex)},
      G.toSimpleGraph.degree v.1 = 3 := by
    intro v
    calc
      G.toSimpleGraph.degree v.1 = G.degree v.1 :=
        (Erdos1016.Nonbacktracking.FiniteTwoCore.original_degree_eq_graph_degree
          G v.1).symm
      _ = 3 := hreg v.1 v.2
  have hsmall' : (Fintype.card U : ℝ) < 2 ^ r := by
    simpa using hsmall
  simpa [J, Finset.mem_coe] using
    induced_target_three_contacts_of_small_order G.toSimpleGraph
      (↑U : Set G.Vertex) hreg' hconn D r hg hD root hsmall'



end Erdos1016.Proof.InducedBoundaryContacts

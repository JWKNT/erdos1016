import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

/-!
# Initial physical corridor construction facts

This separate module records the edge-seeded chain construction and the
connected-graph endpoint fact. It does not assert a global maximal partition.
-/

namespace Erdos1016.Proof.EdgeSeedConstruction

open Erdos1016
open Erdos1016.Proof.PhysicalPartition

/-- Every physical edge has a concrete one-step corridor certificate. -/
def singletonCorridor (G : PhysicalGraph) (e : G.Edge) : PhysicalCorridor G := by
  refine ⟨[e], [G.src e, G.dst e], by simp, by simp, ?_⟩
  intro i
  cases i with
  | mk i hi =>
      simp at hi
      subst i
      simp

theorem singletonCorridor_support (G : PhysicalGraph) (e : G.Edge) :
    (singletonCorridor G e).support = {e} := by
  simp [singletonCorridor, PhysicalCorridor.support]



end Erdos1016.Proof.EdgeSeedConstruction

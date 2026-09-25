import Erdos1016.Decomposition.Descent.GraphDescentTree
import Erdos1016.Cleanup.Transport.PortExpansionCycleSpace

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpandedDecomposition

open Erdos1016
open Erdos1016.SafeCore
open Erdos1016.Proof.PortExpansion
open Erdos1016.Proof.PortExpansionCycleSpace
open Erdos1016.Proof.CleanupSpecification

theorem rootRegion_connectedRegion (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) :
    ConnectedRegion (graph M S h) (rootRegion M S h) := by
  classical
  let G := graph M S h
  let R := rootRegion M S h
  have hc := rootRegion_induce_connected M S h
  let f : {x : M.Vertex // x ∈ S} → {x : G.Vertex // x ∈ R} := fun x =>
    ⟨oldVertex M S x.1, (mem_rootRegion_oldVertex M S h x.1).2 x.2⟩
  letI : Nonempty {x : G.Vertex // x ∈ R} := (h.1.nonempty.map f)
  obtain ⟨base⟩ := ‹Nonempty {x : G.Vertex // x ∈ R}›
  refine ⟨⟨base.1, base.2⟩, ?_⟩
  intro u hu v hv
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hc
  obtain ⟨root, hbase⟩ := hc
  have hbu := hbase ⟨u, hu⟩
  have hbv := hbase ⟨v, hv⟩
  have hreach := hbu.symm.trans hbv
  have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).1 hreach
  have hconvert : ∀ {a b : {x : G.Vertex // x ∈ R}},
      Relation.ReflTransGen (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Adj a b →
        InReach G R a.1 b.1 := by
    intro a b hab
    induction hab with
    | refl => exact .refl a.1 a.2
    | tail hab hstep ih => exact .step ih (by aesop) hstep
  exact hconvert hrel











end Erdos1016.Proof.PortExpandedDecomposition

end

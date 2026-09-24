import Erdos1016.Cleanup.Packing.CorridorParallelPairCount
import Erdos1016.CycleSpace.EmbeddedForestMarginals

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.UnprotectedLoopExclusion

open Erdos1016
open FiniteMultiGraph
open PhysicalPartition CorridorPairedPathCertificates
open CompressedRouteDecomposition PartitionRouteDecomposition
open CorridorRouteEquivalence CorridorParallelPairCount
open CorridorTailNodup ClosedCorridorCycles
open CleanupSpecification

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

/-- A compressed loop outside protection would force a nonzero cycle-space
coordinate to vanish on every outside-forest state, giving probability at
most one half. This applies directly to the support graph and its witness. -/
theorem no_unprotected_loop
    (D : CorridorPartition G P W)
    (hne : ∀ C ∈ D.corridors, C.edges ≠ []) (hend : Endpoints D)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hprob : (1 / 2 : ℝ) < G.outsideLinearForestProbability W)
    (e : (compressedCorridorGraph D hend).Edge)
    (hs : (compressedCorridorGraph D hend).src e ∉ protection D hend)
    (ht : (compressedCorridorGraph D hend).dst e ∉ protection D hend) :
    (compressedCorridorGraph D hend).src e ≠ (compressedCorridorGraph D hend).dst e := by
  classical
  intro hloop
  let Γ := compressedCorridorGraph D hend
  let R := compressedCorridorRouteSystem D hne hend
  let E := compressedCorridor_cycleEquiv D hne hend
  let J := physicalCycleRouteEquiv G
  let M : G.CycleSpace ≃ₗ[ZMod 2] Γ.CycleSpace := J.trans E.symm
  let f : G.CycleSpace →ₗ[ZMod 2] ZMod 2 := (cycleCoordinate Γ e).comp M.toLinearMap
  have hnonzero : f ≠ 0 := by
    intro hz
    apply cycleCoordinate_ne_zero_of_loop Γ e hloop
    ext z
    obtain ⟨x, rfl⟩ := M.surjective z
    exact congrArg (fun g : G.CycleSpace →ₗ[ZMod 2] ZMod 2 => g x) hz
  let C := corridorAt D e
  have hC := corridorAt_mem D e
  have hpathcoord : ∀ x : G.CycleSpace, ∀ p ∈ C.support, (M x).1 e = x.1 p := by
    intro x p hp
    have hword : expand Γ (SingleCorridorRoute.routeGraph G) R (M x).1 = x.1 := by
      change Subtype.val (E (E.symm (J x))) = x.1
      exact congrArg Subtype.val (E.apply_symm_apply (J x))
    have hc := congrFun hword p
    rw [expand_apply_of_mem_support Γ (SingleCorridorRoute.routeGraph G)
      R (M x).1 e p hp] at hc
    exact hc
  have hstart : corridorStart C ∉ P := by
    intro hp
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [C] using hp⟩)
  have hfinish : corridorFinish C ∉ P := by
    intro hp
    exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [C] using hp⟩)
  have havoid : ∀ p ∈ C.support, p ∉ W := by
    exact fun p hp => (Finset.disjoint_left.mp
      (CorridorWitnessAvoidance.corridor_support_disjoint_witnesses
        D P hW hC hstart hfinish)) hp
  have hclosed : corridorStart C = corridorFinish C := by
    have h := congrArg (compressedCorridorVertexMap D hend) hloop
    simpa [C] using h
  have hlen : 0 < C.length := by
    exact List.length_pos_iff.mpr (hne C hC)
  have htail := partition_corridor_vertex_tail_nodup D C hC
  let Good := fun x : G.CycleSpace =>
    G.IsRestrictedLinearForest Wᶜ (G.restrictWord Wᶜ x.1)
  have hkernel : ∀ x : G.CycleSpace, Good x → f x = 0 := by
    intro x hx
    by_contra hn
    have hy : (M x).1 e ≠ 0 := hn
    let H := G.restrictedSelectedGraph Wᶜ (G.restrictWord Wᶜ x.1)
    let p := (corridorWalk C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)).copy rfl hclosed.symm
    have hcycle : p.IsCycle := closed_corridor_isCycle C hclosed hlen htail
    have hselected : ∀ a ∈ C.support, x.1 a ≠ 0 := by
      intro a ha hz
      exact hy ((hpathcoord x a ha).trans hz)
    have hsupport : ∀ a ∈ p.edges, a ∈ H.edgeSet := by
      intro a ha
      obtain ⟨b, hb, hab⟩ := closed_corridor_cycle_edges_supported C hclosed hlen htail a ha
      have hbW : b ∈ Wᶜ := Finset.mem_compl.mpr (havoid b hb)
      have hadj : H.Adj (G.src b) (G.dst b) :=
        ⟨⟨b, hbW⟩, hselected b hb, Or.inl ⟨rfl, rfl⟩⟩
      rw [hab]
      exact H.mem_edgeSet.mpr hadj
    exact hx.1 (p.transfer H hsupport) (hcycle.transfer hsupport)
  have hdensity := NonzeroProjectionLoss.density_le_half_of_nonzero_linear_obstruction
    f hnonzero Good hkernel
  have heq := PhysicalEmbeddingForestProbability.outside_probability_eq_density G W
  exact (not_le_of_gt hprob) (heq ▸ hdensity)

end Erdos1016.Proof.UnprotectedLoopExclusion

end

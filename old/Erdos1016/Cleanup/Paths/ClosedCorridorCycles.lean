import Erdos1016.Cleanup.Packing.CorridorPairedPathCertificates

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ClosedCorridorCycles
open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.CorridorPairedPathCertificates
open SimpleGraph
variable {G : PhysicalGraph}

/-- A nonempty closed corridor whose vertex list has no repetitions after its
first entry is itself a simple cycle in the physical simple graph. The vertex
simplicity premise is essential: edge-label simplicity alone permits a
figure-eight corridor. -/
theorem closed_corridor_isCycle (C : PhysicalCorridor G)
    (hclosed : corridorStart C = corridorFinish C)
    (hne : C.length > 0)
    (hvertices : C.vertices.tail.Nodup) :
    ((corridorWalk C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)).copy rfl hclosed.symm).IsCycle := by
  let raw := corridorWalk C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)
  let p := raw.copy rfl hclosed.symm
  have he := corridorWalk_edgePairs C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)
  have hplen : p.length = C.length := by
    rw [← Walk.length_edges]
    simp [p, raw, Walk.edges_copy, ← he, PhysicalCorridor.length]
  have hlen : p.length > 0 := hplen ▸ hne
  have htrail : p.IsTrail := by
    rw [Walk.isTrail_def]
    simp only [p, Walk.edges_copy]
    rw [← he]
    apply List.Nodup.map (f := fun e : G.Edge => s(G.src e, G.dst e))
    · intro e f hef
      apply G.simple
      exact Sym2.eq_iff.mp hef
    · exact C.edges_nodup
  have hsupp : p.support = C.vertices := by
    simp [p, raw, Walk.support_copy, corridorWalk_support]
  change p.IsCycle
  rw [Walk.isCycle_def]
  refine ⟨htrail, ?_, ?_⟩
  · intro hp
    rw [hp] at hlen
    simp at hlen
  · rw [hsupp]
    exact hvertices
/-- The simple-graph edges of the cycle are exactly images of physical labels
in the corridor support. -/
theorem closed_corridor_cycle_edges_supported (C : PhysicalCorridor G)
    (hclosed : corridorStart C = corridorFinish C)
    (hne : C.length > 0)
    (hvertices : C.vertices.tail.Nodup) :
    ∀ e ∈ ((corridorWalk C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)).copy rfl hclosed.symm).edges,
      ∃ f ∈ C.support, e = s(G.src f, G.dst f) := by
  let raw := corridorWalk C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)
  let p := raw.copy rfl hclosed.symm
  have he := corridorWalk_edgePairs C (corridorStart C) (corridorFinish C)
      (corridorStart_head? C) (corridorFinish_getLast? C)
  have hpEdges : p.edges = List.map (fun f : G.Edge => s(G.src f, G.dst f)) C.edges := by
    simpa [p, raw, Walk.edges_copy] using he.symm
  intro e he
  rw [hpEdges] at he
  rcases List.mem_map.mp he with ⟨f, hf, rfl⟩
  exact ⟨f, List.mem_toFinset.mpr hf, rfl⟩

end Erdos1016.Proof.ClosedCorridorCycles

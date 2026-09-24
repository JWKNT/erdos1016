import Erdos1016.Cycles.Geometry.PhysicalCycleEmbedding

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Erdos1016.Proof.PhysicalCycleEmbedding
open BoundaryDecay CycleSupply SafeCore Nonbacktracking

local instance inducedCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- An adjacency-reflecting physical embedding preserves induced cycles,
including every internal physical edge label. -/
theorem Embedding.liftCycle_induced {H G : PhysicalGraph} (E : Embedding H G)
    (hreflect : ∀ u v, G.toSimpleGraph.Adj (E.vertex u) (E.vertex v) → H.toSimpleGraph.Adj u v)
    (C : H.CycleWord) (hC : Cycle.IsInduced C) : Cycle.IsInduced (E.liftCycle C) := by
  apply Finset.Subset.antisymm _ (Cycle.edges_subset_internal (E.liftCycle C))
  intro e he
  obtain ⟨_, hs, hd⟩ := Finset.mem_filter.mp he
  rw [E.liftCycle_vertices] at hs hd
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hs
  obtain ⟨v, hv, hev⟩ := Finset.mem_image.mp hd
  have hadj : G.toSimpleGraph.Adj (E.vertex u) (E.vertex v) :=
    ⟨e, one_ne_zero, Or.inl ⟨heu.symm, hev.symm⟩⟩
  obtain ⟨f, _, hends⟩ := hreflect u v hadj
  have hf : f ∈ internalEdges H (Cycle.vertices C) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hends with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact ⟨hs ▸ hu, hd ▸ hv⟩
    · exact ⟨hs ▸ hv, hd ▸ hu⟩
  have heq : E.edge f = e := by
    apply G.simple
    rw [E.src, E.dst]
    rcases hends with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact Or.inl ⟨(congrArg E.vertex hs).trans heu, (congrArg E.vertex hd).trans hev⟩
    · exact Or.inr ⟨(congrArg E.vertex hs).trans hev, (congrArg E.vertex hd).trans heu⟩
  rw [hC] at hf
  have hne : C.1 f ≠ 0 := (Finset.mem_filter.mp hf).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← heq, E.liftCycle_coord]
  exact hne

/-- Adjacency between ordinary vertices in the apex owner is exactly the
original adjacency. This does not identify paths through the apex. -/
theorem apex_adj_reflect (H : PhysicalGraph) (u v : H.Vertex)
    (h : (coreApexGraph H).toSimpleGraph.Adj (coreVertexLift H u) (coreVertexLift H v)) :
    H.toSimpleGraph.Adj u v := by
  obtain ⟨e, he, hend⟩ := h
  cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
  | inl f =>
    have hedge : e = coreEdgeLift H f := by
      dsimp [coreEdgeLift]
      rw [← hdec]
      exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
    subst e
    rw [coreEdgeLift_src, coreEdgeLift_dst] at hend
    rcases hend with ⟨hs, hd⟩ | ⟨hs, hd⟩
    · exact ⟨f, one_ne_zero, Or.inl ⟨coreVertexLift_injective H hs, coreVertexLift_injective H hd⟩⟩
    · exact ⟨f, one_ne_zero, Or.inr ⟨coreVertexLift_injective H hs, coreVertexLift_injective H hd⟩⟩
  | inr p =>
    have hedge : e = apexSpoke H p := by
      dsimp [apexSpoke]
      rw [← hdec]
      exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
    subst e
    rw [apexSpoke_src, apexSpoke_dst] at hend
    rcases hend with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact (coreVertex_ne_apex H v hd.symm).elim
    · exact (coreVertex_ne_apex H u hd.symm).elim

end Erdos1016.Proof.PhysicalCycleEmbedding

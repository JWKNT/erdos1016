import Erdos1016.ExactMaximumSupport.CubicReduction.PhysicalCycles

set_option autoImplicit false

/-!
# Cycles survive pruning to the full two-core

The existing linear equivalence restricts the original edge labels.
Here we also transport the degree and connectedness conditions of a cycle.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof.CycleCore BoundaryDecay

variable (G : PhysicalGraph)

private theorem edgeBack_injective : Function.Injective (edgeBack G) := by
  intro e f h
  exact (edgeLabels G).symm.injective (Subtype.ext h)

private theorem edgeBack_surjective_on_core (e : G.Edge)
    (hs : G.src e ∈ core G) (ht : G.dst e ∈ core G) :
    ∃ f : (corePhysical G).Edge, edgeBack G f = e := by
  exact ⟨edgeLabels G ⟨e, hs, ht⟩, by simp [edgeBack]⟩

theorem core_selectedDegree (x : G.CycleSpace) (v : (corePhysical G).Vertex) :
    (corePhysical G).selectedDegree (ShortProof.CycleCore.physicalCycleEquiv G x).1 v =
      G.selectedDegree x.1 (vertexBack G v) := by
  classical
  unfold PhysicalGraph.selectedDegree
  apply Finset.card_bij (fun e _ => edgeBack G e)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    refine ⟨he.1, ?_⟩
    rcases he.2 with hs | ht
    · exact Or.inl ((vertexBack_src G e).symm.trans (congrArg (vertexBack G) hs))
    · exact Or.inr ((vertexBack_dst G e).symm.trans (congrArg (vertexBack G) ht))
  · intro e he f hf h
    exact edgeBack_injective G h
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hs, ht⟩ := nonzero_edge_in_core G x e he.1
    obtain ⟨f, hf⟩ := edgeBack_surjective_on_core G e hs ht
    refine ⟨f, ?_, hf⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simpa only [physicalCycleEquiv_edge, hf] using he.1, ?_⟩
    rcases he.2 with hv | hv
    · apply Or.inl
      apply vertexBack_injective G
      simpa only [vertexBack_src, hf] using hv
    · apply Or.inr
      apply vertexBack_injective G
      simpa only [vertexBack_dst, hf] using hv

theorem core_selectedGraph_adj (x : G.CycleSpace)
    (u v : (corePhysical G).Vertex) :
    ((corePhysical G).selectedGraph (ShortProof.CycleCore.physicalCycleEquiv G x).1).Adj u v ↔
      (G.selectedGraph x.1).Adj (vertexBack G u) (vertexBack G v) := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact ⟨edgeBack G e, he, Or.inl
        ⟨(vertexBack_src G e).symm.trans (congrArg (vertexBack G) h.1),
          (vertexBack_dst G e).symm.trans (congrArg (vertexBack G) h.2)⟩⟩
    · exact ⟨edgeBack G e, he, Or.inr
        ⟨(vertexBack_src G e).symm.trans (congrArg (vertexBack G) h.1),
          (vertexBack_dst G e).symm.trans (congrArg (vertexBack G) h.2)⟩⟩
  · rintro ⟨e, he, h⟩
    obtain ⟨hs, ht⟩ := nonzero_edge_in_core G x e he
    obtain ⟨f, hf⟩ := edgeBack_surjective_on_core G e hs ht
    refine ⟨f, by simpa only [physicalCycleEquiv_edge, hf] using he, ?_⟩
    rcases h with h | h
    · refine Or.inl ⟨?_, ?_⟩ <;> apply vertexBack_injective G
      · simpa only [vertexBack_src, hf] using h.1
      · simpa only [vertexBack_dst, hf] using h.2
    · refine Or.inr ⟨?_, ?_⟩ <;> apply vertexBack_injective G
      · simpa only [vertexBack_src, hf] using h.1
      · simpa only [vertexBack_dst, hf] using h.2

theorem core_isCycleWord (C : G.CycleWord) :
    (corePhysical G).IsCycleWord
      (ShortProof.CycleCore.physicalCycleEquiv G ⟨C.1, C.2.2.1⟩).1 := by
  classical
  let x : G.CycleSpace := ⟨C.1, C.2.2.1⟩
  let y := ShortProof.CycleCore.physicalCycleEquiv G x
  apply (asMultigraph_isCycleWord_iff (corePhysical G) y.1).1
  refine ⟨?_, ?_, ?_⟩
  · intro hy
    have hy' : y = 0 := Subtype.ext hy
    have hx : x = 0 := (ShortProof.CycleCore.physicalCycleEquiv G).injective
      (by simpa only [map_zero] using hy')
    exact C.2.1 (congrArg Subtype.val hx)
  · intro v
    rw [asMultigraph_selectedDegree, core_selectedDegree]
    by_cases hv : vertexBack G v ∈ G.usedVertices C.1
    · exact Or.inr (C.2.2.2.2 _ hv)
    · exact Or.inl (selectedDegree_zero_of_not_used C.1 _ hv)
  · intro u v hu hv
    rw [asMultigraph_selectedDegree, core_selectedDegree] at hu hv
    have hu' := (usedVertices_iff_selectedDegree_pos G C.1 _).2 hu
    have hv' := (usedVertices_iff_selectedDegree_pos G C.1 _).2 hv
    have hsupport : G.usedVertices C.1 ⊆ core G :=
      Proof.CoreCycleSpace.usedVertices_subset_core G x
    let f : (G.selectedGraph C.1).induce (↑(G.usedVertices C.1) : Set G.Vertex) →g
        (corePhysical G).selectedGraph y.1 := {
      toFun := fun w => vertexLabels G ⟨w.1, hsupport w.2⟩
      map_rel' := by
        intro a b hab
        apply (core_selectedGraph_adj G x _ _).2
        simpa only [vertexBack, Equiv.symm_apply_apply] using hab }
    have hp := (C.2.2.2.1.preconnected ⟨vertexBack G u, hu'⟩
      ⟨vertexBack G v, hv'⟩).map f
    have hf (w : (corePhysical G).Vertex)
        (hw : vertexBack G w ∈ G.usedVertices C.1) :
        f ⟨vertexBack G w, hw⟩ = w := by
      change vertexLabels G ⟨vertexBack G w, _⟩ = w
      apply (vertexLabels G).symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply, vertexBack]
    rw [asMultigraph_selectedGraph]
    simpa only [hf] using hp

def coreCycleEmbedding : G.CycleWord ↪ (corePhysical G).CycleWord where
  toFun C := ⟨_, core_isCycleWord G C⟩
  inj' := by
    intro C D h
    have h' := congrArg Subtype.val h
    have heq := (ShortProof.CycleCore.physicalCycleEquiv G).injective (Subtype.ext h')
    apply Subtype.ext
    exact congrArg (fun z : G.CycleSpace => z.1) heq

theorem cycleCount_le_core :
    Fintype.card G.CycleWord ≤ Fintype.card (corePhysical G).CycleWord :=
  Fintype.card_le_of_injective (coreCycleEmbedding G) (coreCycleEmbedding G).injective

end Erdos1016.ExactMaximumSupport.CubicReduction

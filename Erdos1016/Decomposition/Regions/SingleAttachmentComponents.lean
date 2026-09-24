import Erdos1016.Decomposition.Descent.ExteriorMerge

set_option autoImplicit false

/-!
# Attaching a connected region to just one component

When a connected region is added to an induced graph and all its neighbors
in that graph lie in one component, the component count is preserved.
-/

noncomputable section
namespace Erdos1016.Proof.ConnectedComponentAttachment

open Erdos1016.SafeCore

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem componentCount_union_eq_of_single_attachment
    (G : PhysicalGraph) (V D B : Finset G.Vertex)
    (hdisj : Disjoint V D) (hD : ConnectedRegion G D)
    (hB : B ∈ components G V) (htouch : (crossing G B D).Nonempty)
    (honly : ∀ u ∈ D, ∀ v ∈ V, G.toSimpleGraph.Adj u v → v ∈ B) :
    componentCount G (V ∪ D) = componentCount G V := by
  let M := B ∪ D
  have hM : IsComponent G (V ∪ D) M := by
    refine ⟨Finset.union_subset_union (component_subset G hB) (Finset.Subset.refl _),
      connected_union_of_edge G (component_connected G hB) hD htouch, ?_⟩
    intro u hu v hv huv
    rcases Finset.mem_union.mp hv with hvV | hvD
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hu with huB | huD
      · exact component_closed G hB u huB v hvV huv
      · exact honly u huD v hvV huv
    · exact Finset.mem_union_right _ hvD
  have hother : ∀ A ∈ (components G V).erase B, IsComponent G (V ∪ D) A := by
    intro A hA
    obtain ⟨hAB, hA⟩ := Finset.mem_erase.mp hA
    refine ⟨(component_subset G hA).trans Finset.subset_union_left,
      component_connected G hA, ?_⟩
    intro u hu v hv huv
    rcases Finset.mem_union.mp hv with hvV | hvD
    · exact component_closed G hA u hu v hvV huv
    · have huB := honly v hvD u (component_subset G hA hu) huv.symm
      exact (hAB (components_eq_of_mem G hA hB hu huB)).elim
  have hparts : components G (V ∪ D) = insert M ((components G V).erase B) := by
    apply components_eq_of_cover
    · intro A hA
      rcases Finset.mem_insert.mp hA with hA | hA
      · simpa only [hA] using hM
      · exact hother A hA
    · intro u hu
      rcases Finset.mem_union.mp hu with huV | huD
      · obtain ⟨A, hA, huA⟩ := components_cover G huV
        by_cases hAB : A = B
        · refine ⟨M, Finset.mem_insert_self _ _, Finset.mem_union_left _ ?_⟩
          simpa only [hAB] using huA
        · exact ⟨A, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hAB, hA⟩), huA⟩
      · exact ⟨M, Finset.mem_insert_self _ _, Finset.mem_union_right _ huD⟩
  have hnot : M ∉ (components G V).erase B := by
    intro hmem
    have hMV := component_subset G (Finset.mem_erase.mp hmem).2
    obtain ⟨u, huD⟩ := hD.1
    have huV := hMV (Finset.mem_union_right _ huD)
    exact Finset.disjoint_left.mp hdisj huV huD
  unfold componentCount
  rw [hparts, Finset.card_insert_of_not_mem hnot, Finset.card_erase_of_mem hB]
  have hpos := Finset.card_pos.mpr ⟨B, hB⟩
  omega

end Erdos1016.Proof.ConnectedComponentAttachment

end

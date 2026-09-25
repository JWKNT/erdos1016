import Erdos1016.Cycles.Filtering.CoreReturnTransport
import Erdos1016.Cycles.Geometry.SelectedComplementGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Erdos1016.Proof.SelectedReturnTransport
open BoundaryDecay CycleSupply SafeCore Nonbacktracking
open PhysicalCycleEmbedding InducedCoreReturnTransport ExternalReturnFilter
open FewBranchSelectedCycles FewBranchCoreRealization CutoffLimits

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem protector_complement_eq (H : PhysicalGraph) (W : Finset H.Vertex) :
    (apexProtector H W)ᶜ = Wᶜ.image (coreVertexLift H) := by
  ext v
  constructor
  · intro hv
    have hnz : v ≠ coreApexVertex H := by
      intro heq
      exact (Finset.mem_compl.mp hv) (heq ▸ Finset.mem_insert_self _ _)
    obtain ⟨u, rfl⟩ | heq := apex_vertex_cases H v
    · apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_compl.mpr ?_, rfl⟩
      intro hu
      exact (Finset.mem_compl.mp hv) (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
    · exact (hnz heq).elim
  · rintro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_compl.mpr
    intro hW
    rcases Finset.mem_insert.mp hW with h | h
    · exact coreVertex_ne_apex H u h
    · obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp h
      exact (Finset.mem_compl.mp hu) ((coreVertexLift_injective H hEq) ▸ hv)

/-- Every selected cycle retains its return exclusion in the ordinary safe
region of the one-apex owner. The proof first brings the external path into
the original physical two-core, then transports that path along embeddings. -/
theorem selected_noReturnWithin {H : PhysicalGraph} {p₀ : CorePin H} {c σ n : ℝ}
    (S : Selection H p₀ c σ n) (C : (coreApexGraph H).CycleWord) (hC : C ∈ S.cycles) :
    NoShortExternalReturnWithin (coreApexGraph H) (apexProtector H S.W)ᶜ
      (Cycle.vertices C) (cutoffQ σ (Real.logb 2 n)) := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
  have hret := (mem_acceptedShortReturnCycles _ _ _ _ A).mp (S.retained hA)
  have hcore := noReturnWithin_of_induced_core H S.Wᶜ A _ hret.2
  have hapex := noReturnWithin_map (apex H) (apex_adj_reflect H) S.Wᶜ
    (Cycle.vertices ((induced H (coreVertices H S.W)).liftCycle A)) _ hcore
  dsimp only [Selection.embedding]
  rw [protector_complement_eq, induced_apex_liftCycle_vertices]
  simpa only [Embedding.liftCycle_vertices] using hapex

/-- In particular the return exclusion used by the small-complement theorem
is inherited from the actual retained family, with no extra graph premise. -/
theorem selected_noReturnThrough {H : PhysicalGraph} {p₀ : CorePin H} {c σ n : ℝ}
    (S : Selection H p₀ c σ n)
    (F : Finset (coreApexGraph H).CycleWord) (hF : F ⊆ S.cycles)
    (R : Finset (coreApexGraph H).Vertex)
    (hR : R ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ)
    (hRV : R ⊆ (apexProtector H S.W)ᶜ) :
    ∀ C ∈ F, ConditionalMoments.NoShortExternalReturnThrough (coreApexGraph H) R
      (Cycle.vertices C) (cutoffQ σ (Real.logb 2 n)) := by
  intro C hC
  apply noShortExternalReturnThrough_of_region R (apexProtector H S.W)ᶜ
    (Cycle.vertices C) _ hRV
  · apply Finset.disjoint_left.mpr
    intro v hv hvC
    exact (Finset.mem_compl.mp (component_subset _ hR hv))
      (Finset.mem_biUnion.mpr ⟨C, hC, hvC⟩)
  · exact selected_noReturnWithin S C (hF hC)

end Erdos1016.Proof.SelectedReturnTransport

import Erdos1016.Expansion.ApexExpansion
import Erdos1016.Expansion.Connectors

set_option autoImplicit false

/-!
# A small connected protector in the literal apex graph

Connection paths are constructed in the subcubic core, then exactly one apex
and the chosen spoke are added. Every old anchor survives. The high-degree
apex is not used for the ball-growth estimate.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyApexProtectorDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (H : PhysicalGraph)

def liftCoreRegion (A : Finset H.Vertex) : Finset (coreApexGraph H).Vertex :=
  A.image (coreVertexLift H)

theorem lifted_core_adj {u v : H.Vertex} (huv : H.toSimpleGraph.Adj u v) :
    (coreApexGraph H).toSimpleGraph.Adj (coreVertexLift H u) (coreVertexLift H v) := by
  obtain ⟨e, _, he | he⟩ := huv
  · exact ⟨coreEdgeLift H e, one_ne_zero, Or.inl
      ⟨(coreEdgeLift_src H e).trans (congrArg (coreVertexLift H) he.1),
       (coreEdgeLift_dst H e).trans (congrArg (coreVertexLift H) he.2)⟩⟩
  · exact ⟨coreEdgeLift H e, one_ne_zero, Or.inr
      ⟨(coreEdgeLift_src H e).trans (congrArg (coreVertexLift H) he.1),
       (coreEdgeLift_dst H e).trans (congrArg (coreVertexLift H) he.2)⟩⟩

theorem inReach_liftCoreRegion {A : Finset H.Vertex} {u v : H.Vertex}
    (p : InReach H A u v) :
    InReach (coreApexGraph H) (liftCoreRegion H A) (coreVertexLift H u) (coreVertexLift H v) := by
  induction p with
  | refl hu => exact .refl _ (Finset.mem_image.2 ⟨u, hu, rfl⟩)
  | step p hw he ih =>
      exact .step ih (Finset.mem_image.2 ⟨_, hw, rfl⟩) (lifted_core_adj H he)

theorem liftCoreRegion_connected {A : Finset H.Vertex} (hA : ConnectedRegion H A) :
    ConnectedRegion (coreApexGraph H) (liftCoreRegion H A) := by
  refine ⟨hA.1.image _, ?_⟩
  intro u hu v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
  exact inReach_liftCoreRegion H (hA.2 x hx y hy)

theorem apex_not_mem_liftCoreRegion (A : Finset H.Vertex) :
    coreApexVertex H ∉ liftCoreRegion H A := by
  intro hz
  obtain ⟨v, hv, he⟩ := Finset.mem_image.1 hz
  exact coreVertex_ne_apex H v he

theorem liftCoreRegion_card (A : Finset H.Vertex) :
    (liftCoreRegion H A).card = A.card :=
  Finset.card_image_of_injective _ (coreVertexLift_injective H)

def apexProtector (A : Finset H.Vertex) : Finset (coreApexGraph H).Vertex :=
  insert (coreApexVertex H) (liftCoreRegion H A)

theorem apexProtector_card (A : Finset H.Vertex) :
    (apexProtector H A).card = A.card + 1 := by
  rw [apexProtector, Finset.card_insert_of_not_mem (apex_not_mem_liftCoreRegion H A),
    liftCoreRegion_card]

theorem apexProtector_connected {A : Finset H.Vertex} (hA : ConnectedRegion H A)
    (p₀ : CorePin H) (hp₀ : p₀.1 ∈ A) :
    ConnectedRegion (coreApexGraph H) (apexProtector H A) := by
  have hspoke : (coreApexGraph H).toSimpleGraph.Adj (coreApexVertex H) (coreVertexLift H p₀.1) :=
    ⟨apexSpoke H p₀, one_ne_zero, Or.inr ⟨apexSpoke_src H p₀, apexSpoke_dst H p₀⟩⟩
  have hcross : (crossing (coreApexGraph H) {coreApexVertex H} (liftCoreRegion H A)).Nonempty :=
    (crossing_nonempty_iff (coreApexGraph H) _ _).2
      ⟨coreApexVertex H, Finset.mem_singleton_self _, coreVertexLift H p₀.1,
        Finset.mem_image.2 ⟨p₀.1, hp₀, rfl⟩, hspoke⟩
  have hc := connected_union_of_edge (coreApexGraph H)
    (connectedRegion_singleton (coreApexGraph H) (coreApexVertex H))
    (liftCoreRegion_connected H hA) hcross
  simpa [apexProtector] using hc



end Erdos1016.CycleSupply

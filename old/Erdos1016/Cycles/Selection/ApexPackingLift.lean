import Erdos1016.Cycles.Selection.CorePackingProbability
import Erdos1016.Cycles.Geometry.ApexCycleLift

set_option autoImplicit false

/-!
# Packing data survives the one-apex cycle lift

The MANY estimate is stated in the apex graph, while the paper's packing is
found in the original subcubic core. This module transports an actual finite
cycle packing across that interface, preserving its size, lengths, support
disjointness, and avoidance of a core protector.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay

local instance coreCycleFamilyLiftDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable (H : PhysicalGraph)

/-- Lift a finite family of core cycles, retaining one word for every member. -/
def liftCoreCycleFamily (F : Finset H.CycleWord) :
    Finset (coreApexGraph H).CycleWord := F.image (liftApexCycleWord H)

theorem liftApexCycleWord_injective :
    Function.Injective (liftApexCycleWord H) := by
  intro C D h
  apply Subtype.ext
  funext e
  have he := congrArg (fun Z : (coreApexGraph H).CycleWord => Z.1
      (coreEdgeLift H e)) h
  simpa using he

@[simp] theorem mem_liftCoreCycleFamily (F : Finset H.CycleWord)
    (C : (coreApexGraph H).CycleWord) :
    C ∈ liftCoreCycleFamily H F ↔ ∃ A ∈ F, liftApexCycleWord H A = C := by
  simp [liftCoreCycleFamily]

theorem liftCoreCycleFamily_card (F : Finset H.CycleWord) :
    (liftCoreCycleFamily H F).card = F.card := by
  exact Finset.card_image_of_injective _ (liftApexCycleWord_injective H)

@[simp] theorem liftApexCycleWord_support (C : H.CycleWord) :
    Cycle.vertices (liftApexCycleWord H C) =
      (Cycle.vertices C).image (coreVertexLift H) := by
  exact liftApexCycleWord_vertices H C

theorem liftCoreCycleFamily_length_le {F : Finset H.CycleWord} {D : ℕ}
    (hD : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D) :
    ∀ C ∈ liftCoreCycleFamily H F, BoundaryDecay.Cycle.length C ≤ D := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := (mem_liftCoreCycleFamily H F C).1 hC
  simpa only [BoundaryDecay.Cycle.length, liftApexCycleWord_length] using hD A hA

theorem liftCoreCycleFamily_disjoint {F : Finset H.CycleWord}
    (hF : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      Disjoint (Cycle.vertices C) (Cycle.vertices D)) :
    ∀ C ∈ liftCoreCycleFamily H F, ∀ D ∈ liftCoreCycleFamily H F,
      C ≠ D → Disjoint (Cycle.vertices C) (Cycle.vertices D) := by
  intro C hC D hD hne
  obtain ⟨A, hA, rfl⟩ := (mem_liftCoreCycleFamily H F C).1 hC
  obtain ⟨B, hB, rfl⟩ := (mem_liftCoreCycleFamily H F D).1 hD
  have hAB : A ≠ B := by
    intro heq
    subst B
    exact hne rfl
  rw [liftApexCycleWord_support, liftApexCycleWord_support]
  apply Finset.disjoint_left.2
  intro v hvA hvB
  rcases Finset.mem_image.1 hvA with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.1 hvB with ⟨w, hw, hEq⟩
  have huw : u = w := coreVertexLift_injective H hEq.symm
  subst w
  exact (Finset.disjoint_left.1 (hF A hA B hB hAB)) hu hw



theorem liftCoreCycleFamily_avoid_region {F : Finset H.CycleWord}
    (W : Finset H.Vertex)
    (hF : ∀ C ∈ F, Disjoint (Cycle.vertices C) W) :
    ∀ C ∈ liftCoreCycleFamily H F,
      Disjoint (Cycle.vertices C) (apexProtector H W) := by
  intro C hC
  obtain ⟨A, hA, rfl⟩ := (mem_liftCoreCycleFamily H F C).1 hC
  rw [liftApexCycleWord_support]
  apply Finset.disjoint_left.2
  intro v hvC hvW
  rcases Finset.mem_image.1 hvC with ⟨u, hu, rfl⟩
  rcases Finset.mem_insert.1 hvW with hvz | hvW
  · exact coreVertex_ne_apex H u hvz
  · rcases Finset.mem_image.1 hvW with ⟨w, hw, hEq⟩
    have huw : u = w := coreVertexLift_injective H hEq.symm
    subst w
    exact (Finset.disjoint_left.1 (hF A hA)) hu hw

/-- The lifted support of every core cycle lies in the ordinary part of the
apex graph, where the host degree remains the original core degree. -/
theorem coreVertexLift_mem_interior (v : H.Vertex) :
    coreVertexLift H v ∈ BoundaryDecay.coreApexInterior H := by
  simp [BoundaryDecay.coreApexInterior, BoundaryDecay.physicalShore,
    BoundaryDecay.coreOrdinary, coreVertexLift]

/-- A disjoint core packing, together with an actual connected core
protector containing the pinned port, supplies all geometric MANY inputs in
the apex graph. The remaining scalar inequalities are exposed explicitly. -/
theorem coreBoundaryAverage_le_many_of_core_packing
    (hH : H.IsConnected) (p₀ : CorePin H)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hExp : HasExpansion H Finset.univ h)
    (W : Finset H.Vertex) (hW : ConnectedRegion H W) (hp₀ : p₀.1 ∈ W)
    (F : Finset H.CycleWord) (hFne : F.Nonempty) (D : ℕ)
    (hL : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E →
      Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W)
    (hroom : 2 * (D : ℝ) + 4 * (D : ℝ) / h < (H.vertexCount : ℝ) + 1)
    (hlarge : 4 * (D : ℝ) / h < W.card + 1) :
    BoundaryDecay.coreBoundaryAverage H ≤
      (2 : ℝ) ^ D * (manyCycleConflictBound (h / 2) D + 1) / F.card := by
  let W' := apexProtector H W
  let F' := liftCoreCycleFamily H F
  have hW' : ConnectedRegion (coreApexGraph H) W' :=
    apexProtector_connected H hW p₀ hp₀
  have hF' : F'.Nonempty := by
    rcases hFne with ⟨C, hC⟩
    exact ⟨liftApexCycleWord H C, Finset.mem_image.2 ⟨C, hC, rfl⟩⟩
  have hFU' : ∀ C ∈ F', Cycle.vertices C ⊆ BoundaryDecay.coreApexInterior H := by
    intro C hC v hv
    obtain ⟨A, hA, rfl⟩ := (mem_liftCoreCycleFamily H F C).1 hC
    rw [liftApexCycleWord_support] at hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    exact coreVertexLift_mem_interior H u
  have hL' := liftCoreCycleFamily_length_le H hL
  have hdis' := liftCoreCycleFamily_disjoint H hdis
  have havoid' := liftCoreCycleFamily_avoid_region H W havoid
  have hlarge' : 4 * (D : ℝ) / h < W'.card := by
    simp only [W', apexProtector_card]
    simpa only [Nat.cast_add, Nat.cast_one] using hlarge
  have hF'card : F'.card = F.card := liftCoreCycleFamily_card H F
  rw [← hF'card]
  exact coreBoundaryAverage_le_many H hH p₀ hmin hmax h hh hh1 hExp
    W' hW' F' hF' D hFU' hL' hdis' havoid' hroom hlarge'

end Erdos1016.CycleSupply

import Erdos1016.Cycles.Geometry.ApexCycleRestriction
import Erdos1016.Cycles.Selection.ProtectedApexComponents
import Erdos1016.Cycles.Filtering.ReturnMassLoss

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Proof.ApexGirthPacking

open Erdos1016
open Erdos1016.CycleSupply
open Erdos1016.SafeCore
open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking

local instance apexBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (H : PhysicalGraph)

/-! A cycle in the apex graph which avoids the apex restricts to an actual
cycle word in the physical core. The public restriction API already records
connectivity, length, and degree; the remaining cycle-word fields follow from
those facts and the canonical used-vertex support. -/

theorem restricted_apex_cycle_isCycleWord {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) :
    H.IsCycleWord (restrictApexWord H C.1) := by
  let x := restrictApexWord H C.1
  have hconn := apexCycle_restriction_connected H havoid
  have hdeg (v : H.Vertex) (hv : v ∈ H.usedVertices x) : H.selectedDegree x v = 2 := by
    have hvQ : coreVertexLift H v ∈ Cycle.vertices C := by
      change coreVertexLift H v ∈ (coreApexGraph H).usedVertices C.1
      obtain ⟨e, he, hi⟩ := (mem_usedVertices (G := H) x v).1 hv
      refine (mem_usedVertices (G := coreApexGraph H) C.1 _).2 ⟨coreEdgeLift H e, ?_, ?_⟩
      · exact he
      · change (coreApexGraph H).incident (coreEdgeLift H e) (coreVertexLift H v)
        rw [PhysicalGraph.incident, coreEdgeLift_src, coreEdgeLift_dst]
        rcases hi with hs | ht
        · exact Or.inl (congrArg (coreVertexLift H) hs)
        · exact Or.inr (congrArg (coreVertexLift H) ht)
    exact apexCycle_selectedDegree_eq_restriction H havoid v ▸ C.2.2.2.2 _ hvQ
  have hnonzero : x ≠ 0 := by
    intro hx
    apply C.2.1
    funext e
    cases hd : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
        have he : e = coreEdgeLift H f := by
          dsimp [coreEdgeLift]
          rw [← hd]
          exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
        subst e
        have := congrFun hx f
        simpa [x, restrictApexWord] using this
    | inr p =>
        have he : e = apexSpoke H p := by
          dsimp [apexSpoke]
          rw [← hd]
          exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
        subst e
        exact apexCycle_spoke_zero H havoid p
  have hboundary : H.boundary x = 0 := by
    funext v
    rw [boundary_eq_selectedDegree_cast]
    by_cases hv : v ∈ H.usedVertices x
    · rw [hdeg v hv]
      change ((2 : ℕ) : F₂) = 0
      have htwo : (2 : F₂) = 0 := by decide
      exact htwo
    · rw [selectedDegree_zero_of_not_used x v hv]
      norm_num
  exact ⟨hnonzero, hboundary, hconn, hdeg⟩

theorem apex_noShortCycles_of_core_noShortCycles
    (W : Finset H.Vertex) (D : ℕ)
    (hno : NoShortCycles H Wᶜ D) :
    NoShortCycles (coreApexGraph H) (apexProtector H W)ᶜ D := by
  intro C hC
  have havoid : coreApexVertex H ∉ Cycle.vertices C := by
    intro hz
    have hmem : coreApexVertex H ∈ apexProtector H (Finset.univ : Finset H.Vertex) :=
      Finset.mem_insert_self _ _
    exact (Finset.mem_compl.1 (hC hz)) (by simpa [apexProtector] using hmem)
  let x := restrictApexWord H C.1
  have hxcycle : H.IsCycleWord x := by
    simpa [x] using restricted_apex_cycle_isCycleWord H havoid
  let C0 : H.CycleWord := ⟨x, hxcycle⟩
  have hsupport : Cycle.vertices C0 ⊆ Wᶜ := by
    intro v hv
    have hvQ : coreVertexLift H v ∈ Cycle.vertices C := by
      change coreVertexLift H v ∈ (coreApexGraph H).usedVertices C.1
      obtain ⟨e, he, hi⟩ := (mem_usedVertices (G := H) x v).1 hv
      refine (mem_usedVertices (G := coreApexGraph H) C.1 _).2 ⟨coreEdgeLift H e, ?_, ?_⟩
      · exact he
      · change (coreApexGraph H).incident (coreEdgeLift H e) (coreVertexLift H v)
        rw [PhysicalGraph.incident, coreEdgeLift_src, coreEdgeLift_dst]
        rcases hi with hs | ht
        · exact Or.inl (congrArg (coreVertexLift H) hs)
        · exact Or.inr (congrArg (coreVertexLift H) ht)
    apply Finset.mem_compl.2
    intro hvW
    have : coreVertexLift H v ∈ apexProtector H W := by
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨v, hvW, rfl⟩)
    exact (Finset.mem_compl.1 (hC hvQ)) this
  have hlen : BoundaryDecay.Cycle.length C0 = BoundaryDecay.Cycle.length C := by
    change H.wordLength x = (coreApexGraph H).wordLength C.1
    exact (apexCycle_length_eq_restriction H havoid).symm
  have hshort := hno C0 hsupport
  change D < BoundaryDecay.Cycle.length C0 at hshort
  change D < BoundaryDecay.Cycle.length C
  rw [← hlen]
  exact hshort





end Erdos1016.Proof.ApexGirthPacking

end

import Erdos1016.Cycles.Selection.SmallComplementComponents
import Erdos1016.Expansion.ApexProtector

set_option autoImplicit false

/-!
# Section 7 FEW adapter on the one-apex owner

This packages the existing connected-core-anchor to apex-protector construction
with the FEW component adapter. The remaining FEW packing statement is kept
explicit: it must concern cycles in the actual apex graph that avoid the
apex-containing protector.
-/

noncomputable section
namespace Erdos1016.Proof.ProtectedApexComponents

open Erdos1016
open Erdos1016.CycleSupply
open Erdos1016.SafeCore
open Erdos1016.BoundaryDecay
open Erdos1016.Proof.SmallComplementComponents



/-- Conditional moment endpoint after the initial packing has been absorbed
into its protector. The initial packing scale is intentionally not an
argument here: its only required outputs are the supplied connected W and
the high-girth exterior. The separate moment family F has size at most
`Kmoment` and lengths at most L, so every nongiant component has order at most
`Kmoment * L / κ`.

The explicit hGirth premise is precisely the remaining maximality-to-protector
bridge from the initial packing to the one-apex exterior. -/
theorem two_scale_moment_component_bound
    (H : PhysicalGraph) (h : ℝ) (hh : 0 < h) (hh2 : h ≤ 2)
    (hExp : HasExpansion H Finset.univ h)
    (hmin : ∀ v, 2 ≤ H.degree v) (hdeg : ∀ v, H.degree v ≤ 3)
    (p₀ : CorePin H) (Kmoment L D Dpack : ℕ)
    (W : Finset (coreApexGraph H).Vertex)
    (hW : ConnectedRegion (coreApexGraph H) W)
    (hz : coreApexVertex H ∈ W)
    (hGirth : NoShortCycles (coreApexGraph H) Wᶜ Dpack)
    (hDle : D ≤ Dpack)
    (F : Finset (coreApexGraph H).CycleWord)
    (hFpack : IsCyclePacking (coreApexGraph H) F)
    (hFsize : F.card ≤ Kmoment)
    (hFlength : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ L)
    (hFavoid : ∀ C ∈ F, Cycle.vertices C ⊆ Wᶜ)
    (hlarge : (cutSize (coreApexGraph H) (F.biUnion Cycle.vertices) : ℝ) /
      (h / 2) < W.card)
    (hroom : ((F.biUnion Cycle.vertices).card : ℝ) +
      (cutSize (coreApexGraph H) (F.biUnion Cycle.vertices) : ℝ) /
        (h / 2) < (H.vertexCount + 1 : ℝ)) :
    ∃ giant ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ,
      ((coreApexGraph H).vertexCount : ℝ) / 2 < (giant.card : ℝ) ∧
      W ⊆ giant ∧
      ∀ C ∈ components (coreApexGraph H) (F.biUnion Cycle.vertices)ᶜ,
        C = giant ∨
          ((C.card : ℝ) ≤ ((coreApexGraph H).vertexCount : ℝ) / 2 ∧
            (C.card : ℝ) ≤ ((Kmoment * L : ℕ) : ℝ) / (h / 2) ∧
            NoShortCycles (coreApexGraph H) C D ∧
            Nonbacktracking.ShortWalks.GirthGreater
              ((coreApexGraph H).toSimpleGraph.induce (↑C : Set _)) D ∧
            (∀ v ∈ C, (coreApexGraph H).degree v = 3)) := by
  have hh0 : 0 ≤ h := hh.le
  have hExpQ := coreApex_hasExpansion H h hh0 hh2 hExp p₀
  have hdegree : ∀ v ∈ Wᶜ, (coreApexGraph H).degree v = 3 := by
    intro v hv
    rcases apex_vertex_cases H v with ⟨u, rfl⟩ | heq
    · exact coreApex_ordinary_cubic H hmin hdeg (coreVertexLift H u) (by
        simp [coreApexInterior, physicalShore, coreOrdinary, coreVertexLift])
    · exact False.elim ((Finset.mem_compl.1 hv) (heq ▸ hz))
  have hno : NoShortCycles (coreApexGraph H)
      (W ∪ (F.biUnion Cycle.vertices))ᶜ D := by
    intro C hC
    have hsubset : Cycle.vertices C ⊆ Wᶜ := by
      intro v hv
      have hnot : v ∉ W ∪ (F.biUnion Cycle.vertices) := by
        simpa only [Finset.mem_compl] using hC hv
      exact Finset.mem_compl.2 (fun hvW =>
        hnot (Finset.mem_union.2 (Or.inl hvW)))
    exact lt_of_le_of_lt hDle (hGirth C hsubset)
  have hFcubic : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C,
      (coreApexGraph H).degree v = 3 := by
    intro C hC v hv
    exact hdegree v (hFavoid C hC hv)
  have hWavoid : W ⊆ (F.biUnion Cycle.vertices)ᶜ := by
    intro v hvW
    apply Finset.mem_compl.2
    intro hvS
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hvS
    exact Finset.mem_compl.1 (hFavoid C hC hvC) hvW
  have hcomps := selected_cycle_complement_small_components
    (G := coreApexGraph H) F Kmoment L D (h / 2) (by positivity) hExpQ
    hFsize hFpack hFcubic hFlength W hW hWavoid hlarge (by
      simpa only [apex_order, Nat.cast_add, Nat.cast_one] using hroom) hno hdegree
  exact hcomps

end Erdos1016.Proof.ProtectedApexComponents

end

import Erdos1016.Expansion.CycleDeletionComponents
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

/-!
# FEW adapter: selected-cycle deletion to small high-girth components

The cycle-family and component expansion estimates are assembled here. The
remaining FEW inputs explicitly record the protector geometry: expansion of
the owner, room for a giant complement component, and absence of short cycles
outside the connected protector.
-/

noncomputable section
namespace Erdos1016.Proof.SmallComplementComponents

open Erdos1016
open Erdos1016.CycleSupply
open Erdos1016.SafeCore
open Erdos1016.BoundaryDecay
open Erdos1016.Proof.CycleDeletionComponents

variable {G : PhysicalGraph}

/-- For at most K disjoint cubic cycles of length at most L, every component
other than the protector's giant in the complement of their supports has
order at most KL/κ and inherits the girth exclusion outside the protector.
The `W`, `hroom`, and `hno` assumptions are the explicit outputs still needed
from the FEW protector construction. -/
theorem selected_cycle_complement_small_components
    (F : Finset G.CycleWord) (K L D : ℕ) (κ : ℝ)
    (hκ : 0 < κ) (hExp : HasExpansion G Finset.univ κ)
    (hcard : F.card ≤ K)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E →
      Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hcubic : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hlen : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ L)
    (W : Finset G.Vertex) (hW : ConnectedRegion G W)
    (hWS : W ⊆ (F.biUnion Cycle.vertices)ᶜ)
    (hlarge : (cutSize G (F.biUnion Cycle.vertices) : ℝ) / κ < W.card)
    (hroom : (((F.biUnion Cycle.vertices).card : ℕ) : ℝ) +
      (cutSize G (F.biUnion Cycle.vertices) : ℝ) / κ < G.vertexCount)
    (hno : NoShortCycles G (W ∪ (F.biUnion Cycle.vertices))ᶜ D)
    (hcubicOutsideW : ∀ v ∈ Wᶜ, G.degree v = 3) :
    ∃ giant ∈ components G (F.biUnion Cycle.vertices)ᶜ,
      (G.vertexCount : ℝ) / 2 < (giant.card : ℝ) ∧
      W ⊆ giant ∧
      ∀ C ∈ components G (F.biUnion Cycle.vertices)ᶜ,
        C = giant ∨
          ((C.card : ℝ) ≤ (G.vertexCount : ℝ) / 2 ∧
            (C.card : ℝ) ≤ ((K * L : ℕ) : ℝ) / κ ∧
            NoShortCycles G C D ∧
            Nonbacktracking.ShortWalks.GirthGreater
              (G.toSimpleGraph.induce (↑C : Set G.Vertex)) D ∧
            (∀ v ∈ C, G.degree v = 3)) := by
  let S := F.biUnion Cycle.vertices
  obtain ⟨w, hw⟩ := hW.1
  have hroot := root_small_complement_bound G κ hκ hExp S W
    (by simpa [S] using hroom) hW (by simpa [S] using hWS)
    (by simpa [S] using hlarge) w hw
  let giant := reachSet G Sᶜ w
  have hwS : w ∈ Sᶜ := hWS hw
  have hgiant : giant ∈ components G Sᶜ := root_component_mem G hwS
  have hbig : (G.vertexCount : ℝ) / 2 < (giant.card : ℝ) := by
    simpa [giant] using hroot.1
  obtain ⟨Wcomp, hWcomp, hWsubset⟩ := connected_subset_some_component G hW hWS
  have hWcompEq : Wcomp = giant := by
    have hwcomp : w ∈ Wcomp := hWsubset hw
    have heq := components_eq_of_mem G hWcomp hgiant hwcomp (self_mem_reachSet G hwS)
    simpa [giant] using heq
  have hWgiant : W ⊆ giant := by simpa [hWcompEq] using hWsubset
  refine ⟨giant, hgiant, hbig, hWgiant, ?_⟩
  intro C hC
  by_cases heq : C = giant
  · exact Or.inl heq
  · right
    have hsmall := nongiant_is_small G Sᶜ hC hgiant heq hbig
    have hsize := CycleDeletionComponents.small_component_card_le_cycle_budget
      F K L κ hκ hExp hcard hdis hcubic hlen C hC hsmall
    have hCW : Disjoint C W := by
      apply Finset.disjoint_left.2
      intro v hvC hvW
      exact (Finset.disjoint_left.1 (components_disjoint G hC hgiant heq)) hvC
        (hWgiant hvW)
    have hsubsetW : C ⊆ Wᶜ := by
      intro v hv
      exact Finset.mem_compl.2 (fun hvW => Finset.disjoint_left.1 hCW hv hvW)
    have hsubsetWS : C ⊆ (W ∪ S)ᶜ := by
      intro v hvC
      apply Finset.mem_compl.2
      intro hvUnion
      rcases Finset.mem_union.1 hvUnion with hvW | hvS
      · exact Finset.disjoint_left.1 hCW hvC hvW
      · exact (Finset.mem_compl.1 ((component_subset G hC) hvC)) hvS
    have hnoC : NoShortCycles G C D := noShortCycles_mono G hno hsubsetWS
    have hgirth := Nonbacktracking.girthGreater_induce_of_noShortCycles G C D hnoC
    have hdegree : ∀ v ∈ C, G.degree v = 3 := by
      intro v hv
      exact hcubicOutsideW v (hsubsetW hv)
    exact ⟨hsmall, hsize, hnoC, hgirth, hdegree⟩




end Erdos1016.Proof.SmallComplementComponents

end

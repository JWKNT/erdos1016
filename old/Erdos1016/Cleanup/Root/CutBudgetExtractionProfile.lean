import Erdos1016.Cleanup.Root.OutsideBoundaryCharging
import Erdos1016.Cleanup.Root.OutsideComponentPartitions
import Erdos1016.Cleanup.Root.ProtectedDeletionRankLedger

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CutBudgetExtractionProfile

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.OutsideComponentPartitions
open Erdos1016.Proof.ProtectedDeletionRankLedger
open Erdos1016.Proof.OutsideBoundaryCharging

/-- Assemble the bookkeeping portion of Section 10's extraction profile from
the protected-cut budget. The substantive inputs are the cubic degree law
and rank-sum estimate. The count and individual component-cut bounds follow
from the fact that every outside component attaches only to P; component
graph connectedness follows from the support-to-index equivalence. -/
def profileOfProtectedCutBudget
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (r R A : ℕ)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hcubic : ∀ v, v ∉ P → ambientDegree Γ v = 3)
    (hrank : (r : ℝ) / (10 * R) ≤
      ∑ c : OutsideComponent Γ P, (outsideComponentRank Γ P c : ℝ))
    (hcut : (cutEdges Γ P).card ≤ A) :
    ComponentExtractionProfile Γ P r R A := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hcountSetLike :
      @Fintype.card (OutsideComponent Γ P) SetLike.instFintype ≤
        (cutEdges Γ P).card := outside_component_count_le_cut hconn hP
  refine ⟨hcubic, ?_, hrank, ?_⟩
  · calc
      Fintype.card (OutsideComponent Γ P) ≤
          (cutEdges Γ P).card := hcountSetLike
      _ ≤ A := hcut
  · intro c
    exact (outside_component_cut_card_le_protected_cut c).trans hcut



end Erdos1016.Proof.CutBudgetExtractionProfile

end

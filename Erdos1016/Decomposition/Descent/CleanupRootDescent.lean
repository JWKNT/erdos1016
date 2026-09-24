import Erdos1016.Decomposition.Descent.ForestDescent
import Erdos1016.Cleanup.Root.PortExpansionConnectivity
import Erdos1016.Probability.Regions.RegionForestLaw
import Erdos1016.Decomposition.Regions.PortExpandedDecomposition
import Erdos1016.Cleanup.Transport.PortExpansionMarginal
import Erdos1016.Cleanup.Root.PortExpansionDegree

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Erdos1016.Proof.CleanupRootDescent

open Erdos1016 SafeCore
open CleanupSpecification PortExpansion PortExpansionCycleSpace
open PortExteriorComponentEquivalence
open PortExpandedDecomposition PortExpansionDegree
open PortExpansionMarginal
open FiniteForestDescent

variable {G : PhysicalGraph} {I : CleanupInput G}

/-- The port-expanded root keeps precisely the old vertices of the root. -/
theorem rootRegion_eq_image (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) : rootRegion M S h = oldVertexImage M S h S := by
  classical
  ext v
  simp [rootRegion, oldVertexImage]

/-- The original exterior count in the simple port expansion is exactly the
cleanup graph's actual exterior count. No leaf count is substituted for it. -/
theorem root_exterior_eq (O : CleanupOutput I) :
    (graph O.Γ O.root O.root_structure).originalExteriorComponents
      (rootRegion O.Γ O.root O.root_structure) = exteriorComponentCount O.Γ O.root := by
  classical
  rw [rootRegion_eq_image]
  have h := portExpansion_exteriorComponentCount_eq O.Γ O.root O.root
    O.root_structure (Finset.Subset.refl _)
  simpa only [PhysicalGraph.originalExteriorComponents, ← Nat.card_eq_fintype_card] using h

theorem root_proper (O : CleanupOutput I) :
    (rootRegion O.Γ O.root O.root_structure)ᶜ.Nonempty := by
  classical
  have hcard : O.root.card < (Finset.univ : Finset O.Γ.Vertex).card := by
    simpa using O.root_proper
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  exact ⟨oldVertex O.Γ O.root v, Finset.mem_compl.mpr
    (fun h => hv ((mem_rootRegion_oldVertex O.Γ O.root O.root_structure v).mp h))⟩

/-- Proposition 7.5 applies to every constructed cleanup output through its
simple port expansion. The only analytic premise is stopping for actual
connected expanding negative regions of that owner. Small-leaf packing and
the no-negative-leaf case are discharged by the finite descent theorem. -/
theorem root_additive_bound (O : CleanupOutput I) (hR : 5 ≤ I.R)
    (T₀ : ℕ → ℕ) (hTmono : Monotone T₀)
    (hstop : ∀ L ⊆ rootRegion O.Γ O.root O.root_structure,
      ConnectedRegion (graph O.Γ O.root O.root_structure) L →
      Expanded (graph O.Γ O.root O.root_structure) canonicalParameters L →
      potential (graph O.Γ O.root O.root_structure) canonicalParameters L < 0 →
      L.card < T₀ ((graph O.Γ O.root O.root_structure).originalExteriorComponents L)) :
    (O.root.card : ℝ) ^ (7 / 8 : ℝ) ≤ 16 * (cutEdges O.Γ O.root).card +
      (exteriorComponentCount O.Γ O.root + 2 * leafPackingThreshold T₀ I.R : ℝ) *
        (T₀ (exteriorComponentCount O.Γ O.root + leafPackingThreshold T₀ I.R) : ℝ) ^ (7 / 8 : ℝ) := by
  classical
  let P := graph O.Γ O.root O.root_structure
  let U := rootRegion O.Γ O.root O.root_structure
  have hconn : P.IsConnected := PortExpansionConnectivity.connected O.Γ O.root
    O.root_structure O.auxiliary_connected
  have hcubic : ∀ v ∈ U, P.degree v = 3 := by
    intro v hv
    rw [show U = oldVertexImage O.Γ O.root O.root_structure O.root from
      rootRegion_eq_image _ _ _] at hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact cleanup_expanded_root_degree_eq_three O hq
  have hprob : (1 / 2 : ℝ) + 1 / (I.R : ℝ) <
      P.outsideLinearForestProbability (SafeCore.internalEdges P U)ᶜ := by
    rw [← PhysicalRegionForestProbability.region_eq_outside]
    change (1 / 2 : ℝ) + 1 / (I.R : ℝ) <
      regionForestProbability (Physical O.Γ O.root O.root_structure)
        (rootRegion O.Γ O.root O.root_structure)
    rw [rootRegion_eq_image]
    exact I.outside_probability.trans_le (probability_domination_rootPortExpansion O)
  have h := FiniteForestDescent.root_additive_bound P hconn U
    (rootRegion_connectedRegion O.Γ O.root O.root_structure) (root_proper O)
    hcubic (SafeCore.internalEdges P U)ᶜ (by simp) I.R hR hprob T₀ hTmono hstop
  simpa only [U, P, rootRegion_card_eq, root_cut_card_eq, root_exterior_eq] using h

end Erdos1016.Proof.CleanupRootDescent

end

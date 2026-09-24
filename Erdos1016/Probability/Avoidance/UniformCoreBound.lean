import Erdos1016.Decomposition.TwoCore.NormalizedExtraction
import Erdos1016.Boundary.DegreeTwoDeficit
import Erdos1016.Boundary.InducedShoreApexLaw
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.UniformCoreDecay

open Erdos1016 SafeCore BoundaryDecay Extremal

/-- The single analytic estimate required by the finite cleanup/descent
argument. The onset and decay coefficient are uniform in the physical core;
the expansion and boundary constants are those produced by full two-core
normalization at the paper's fixed parameters. -/
def Estimate (N₀ : ℕ) (γ : ℝ) : Prop :=
  ∀ H : PhysicalGraph,
    H.IsConnected →
    (∀ v, 2 ≤ H.degree v ∧ H.degree v ≤ 3) →
    HasExpansion H Finset.univ
      (coreExpansion canonicalParameters * (H.vertexCount : ℝ) ^ (canonicalParameters.p - 1)) →
    (Nonbacktracking.degreeTwoCount H : ℝ) ≤
      coreBudget canonicalParameters * (H.vertexCount : ℝ) ^ canonicalParameters.p →
    N₀ ≤ H.vertexCount →
    coreBoundaryAverage H ≤
      (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (H.vertexCount : ℝ)))

/-- Applying the uniform physical-core estimate to the exact induced shore
also identifies its boundary law with the owner's actual one-apex law. -/
theorem normalized_oneApex_bound {N₀ : ℕ} {γ : ℝ} (hdecay : Estimate N₀ γ)
    (G : PhysicalGraph) (K : Finset G.Vertex)
    (hcubic : ∀ v ∈ K, G.degree v = 3)
    (hK : NormalizedRegion G canonicalParameters K) (hlarge : N₀ ≤ K.card) :
    G.oneApexForestFraction K ≤
      (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (K.card : ℝ))) := by
  have hcard : (inducedShoreGraph G K).vertexCount = K.card := by
    simp [inducedShoreGraph, Nonbacktracking.FiniteTwoCore.inducedPhysical,
      Nonbacktracking.FiniteTwoCore.inducedNetwork, BoundaryDecay.physicalize,
      BoundaryTrace.Network.Shore.InsideVertex]
  rw [oneApexForestFraction_eq_coreBoundaryAverage G K hcubic hK.minTwo]
  have h := hdecay (inducedShoreGraph G K)
    (inducedShore_connected_of_connectedRegion G K hK.connected)
    (fun v => ⟨inducedShore_minTwo G K hK.minTwo v, inducedShore_maxDegree G K hK.maxThree v⟩)
    (by simpa only [hcard] using inducedShore_hasExpansion G K _ hK.expansion)
    (by rw [hcard, inducedShore_degreeTwoCount_eq_cutSize G K hcubic hK.minTwo]; exact hK.boundary)
    (by rw [hcard]; exact hlarge)
  simpa only [hcard] using h

end Erdos1016.Proof.UniformCoreDecay

end

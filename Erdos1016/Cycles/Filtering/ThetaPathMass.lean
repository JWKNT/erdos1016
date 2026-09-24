import Erdos1016.Cycles.Filtering.EndpointPathMass
import Erdos1016.Cycles.Filtering.ThetaCandidates

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ThetaFilterAccounting

open scoped BigOperators
open Erdos1016.BoundaryDecay

variable (G : PhysicalGraph)

/-- The path-family mass that contains the physical candidates: base-cycle
weight times external-branch weight, summed over ordered base endpoints,
branch lengths, and fixed-endpoint simple paths. -/
def shortReturnPathThetaMass (bases : Finset G.CycleWord) (s L : ℕ) : ℝ :=
  ∑ C ∈ bases, (1 / 2 : ℝ) ^ G.wordLength C.1 *
    (∑ p ∈ Erdos1016.Proof.ExternalReturnPathMass.cycleEndpointPairs G C,
      ∑ a ∈ Finset.Ioc s L,
        (Fintype.card (Erdos1016.Proof.PathEndpointRunInjection.FixedEndpointSimplePaths
          G a p.1 p.2) : ℝ) * (1 / 2 : ℝ) ^ a)

/-- The full fixed-endpoint path-family mass obeys the paper's suffix bound.
This is the quantitative input available for `htheta`. -/
theorem shortReturnPathThetaMass_le
    (bases : Finset G.CycleWord) (s L D : ℕ)
    (hshort : ∀ C ∈ bases, G.wordLength C.1 ≤ L)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hg : Erdos1016.Nonbacktracking.ShortWalks.GirthGreater
      G.toSimpleGraph D)
    (hs : 0 < s) (hshortGirth : 2 * s ≤ D) :
    shortReturnPathThetaMass G bases s L ≤
      (3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s *
        (∑ C ∈ bases, (1 / 2 : ℝ) ^ G.wordLength C.1) := by
  exact Erdos1016.Proof.ExternalReturnPathMass.short_cycle_simple_path_mass_le
    G bases s L D hshort hmin hmax hg hs hshortGirth

end Erdos1016.Proof.ThetaFilterAccounting
end

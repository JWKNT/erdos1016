import Erdos1016.Cycles.Filtering.ThetaFibers

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.RejectedCycleEncoding

open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.ThetaArcUniqueness
open Erdos1016.Proof.ThetaSupportArcUniqueness
open Erdos1016.Proof.MinimumPairArcTransport
open Erdos1016.Proof.PhysicalThetaPairRelabel

variable (G : Erdos1016.PhysicalGraph)









/-- The finite family of physical cycle words of length at most `L`. -/
def shortCycleWords (L : ℕ) : Finset G.CycleWord := by
  classical
  exact Finset.univ.filter fun C => G.wordLength C.1 ≤ L



end Erdos1016.Proof.RejectedCycleEncoding
end

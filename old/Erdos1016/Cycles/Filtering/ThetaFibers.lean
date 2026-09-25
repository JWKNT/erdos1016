import Erdos1016.Cycles.Filtering.ThetaKeyMass

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Proof.ThetaMassFiberBridge

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.ThetaSupportArcUniqueness
open Erdos1016.Proof.ThetaArcUniqueness
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Nonbacktracking

/-- A theta path code together with the exact conditions making its base,
endpoints, and external branch a member of the finite candidate family. -/
structure CandidateThetaCode (G : Erdos1016.PhysicalGraph)
    (bases : Finset G.CycleWord) (s L : ℕ) {u v : G.Vertex}
    (huv : u ≠ v) where
  theta : ThetaPaths G.toSimpleGraph u v
  base_mem : cycleWordOfWalk G (leftRightCycle G.toSimpleGraph theta)
    (leftRightCycle_isCycle G.toSimpleGraph theta huv) ∈ bases
  branch_lower : s < theta.external.length
  branch_upper : theta.external.length ≤ L



def candidateKeyWeight (G : Erdos1016.PhysicalGraph) {bases : Finset G.CycleWord}
    {s L : ℕ} (w : Candidate G bases s L) : ℝ :=
    (1 / 2 : ℝ) ^ G.wordLength (candidateCycle G w).1 *
    (1 / 2 : ℝ) ^ candidateBranchLength G w



















end Erdos1016.Proof.ThetaMassFiberBridge
end

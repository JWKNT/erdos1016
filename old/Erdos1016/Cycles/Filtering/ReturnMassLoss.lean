import Erdos1016.Cycles.Filtering.WeightedThetaCharging

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Proof.ReturnMassLoss

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.RejectedCycleEncoding
open Erdos1016.Proof.WeightedThetaCharging
open Erdos1016.Proof.ThetaMassFiberBridge
open Erdos1016.Proof.ExternalReturnFilter

variable (G : Erdos1016.PhysicalGraph)

local instance cycleWordDecidableEq : DecidableEq G.CycleWord := Classical.decEq _

def cycleWordMass (C : G.CycleWord) : ℝ :=
  (1 / 2 : ℝ) ^ G.wordLength C.1

def shortCycleMass (L : ℕ) : ℝ :=
  ∑ C ∈ shortCycleWords G L, cycleWordMass G C



/-- Erasing the proof that a candidate is realizable only restricts its
finite candidate mass, so the realizable mass is bounded by the full path
family mass. -/
theorem realizable_candidate_mass_le_short_return_path_mass
    (bases : Finset G.CycleWord) (s L : ℕ) :
    (∑ w : RealizableCandidate G bases s L,
      realizableThetaMassWeight G w) ≤
      Erdos1016.Proof.ThetaFilterAccounting.shortReturnPathThetaMass G bases s L := by
  classical
  let p : Candidate G bases s L → Prop := fun w =>
    Nonempty (CandidateRealization G w)
  let realized := Finset.univ.filter p
  have hsubtype :
      (∑ w : RealizableCandidate G bases s L,
        realizableThetaMassWeight G w) =
        ∑ w ∈ realized, candidateKeyWeight G w := by
    symm
    exact Finset.sum_subtype realized (by
      intro w
      simp [realized, p]) (candidateKeyWeight G)
  have hsubset : realized ⊆ Finset.univ := Finset.subset_univ _
  have hall :
      (∑ w ∈ realized, candidateKeyWeight G w) ≤
        ∑ w : Candidate G bases s L, candidateKeyWeight G w := by
    calc
      (∑ w ∈ realized, candidateKeyWeight G w) ≤
          ∑ w ∈ (Finset.univ : Finset (Candidate G bases s L)),
            candidateKeyWeight G w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro w hw hnot
          simp only [candidateKeyWeight]
          positivity)
      _ = ∑ w : Candidate G bases s L, candidateKeyWeight G w := by simp
  calc
    _ = ∑ w ∈ realized, candidateKeyWeight G w := hsubtype
    _ ≤ ∑ w : Candidate G bases s L, candidateKeyWeight G w := hall
    _ = Erdos1016.Proof.ThetaFilterAccounting.shortReturnPathThetaMass G bases s L := by
      have hmass := ThetaMassBridge.candidate_key_mass_eq_shortReturnPathThetaMass
        G bases s L
      simpa [ThetaMassBridge.ThetaPathKey, ThetaMassBridge.keyWeight,
        candidateKeyWeight] using hmass







end Erdos1016.Proof.ReturnMassLoss

end

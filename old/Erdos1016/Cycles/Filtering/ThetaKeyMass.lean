import Erdos1016.Cycles.Filtering.ThetaSupportArcs
import Erdos1016.Cycles.Filtering.ThetaPathMass

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Proof.ThetaMassBridge

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Proof.PhysicalThetaCandidates

variable (G : Erdos1016.PhysicalGraph)

/-- The physical path-family key: base word, ordered endpoints, branch length,
and one fixed-endpoint simple path. This is exactly the existing candidate. -/
abbrev ThetaPathKey (bases : Finset G.CycleWord) (s L : ℕ) :=
  Candidate G bases s L

def keyWeight {bases : Finset G.CycleWord} {s L : ℕ}
    (k : ThetaPathKey G bases s L) : ℝ :=
  (1 / 2 : ℝ) ^ G.wordLength (candidateCycle G k).1 *
    (1 / 2 : ℝ) ^ candidateBranchLength G k

/-- Summing the weight of each path key gives the short-return path mass:
each fixed-endpoint simple path contributes one copy of its branch weight. -/
theorem candidate_key_mass_eq_shortReturnPathThetaMass
    (bases : Finset G.CycleWord) (s L : ℕ) :
    (∑ k : ThetaPathKey G bases s L, keyWeight G k) =
      Erdos1016.Proof.ThetaFilterAccounting.shortReturnPathThetaMass G bases s L := by
  classical
  unfold Erdos1016.Proof.ThetaFilterAccounting.shortReturnPathThetaMass
  simp only [ThetaPathKey, keyWeight, Candidate, candidateCycle,
    candidateBranchLength, Fintype.sum_sigma]
  have hcard (a : ℕ) (u v : G.Vertex) :
      (Fintype.card (Erdos1016.Proof.PathEndpointRunInjection.FixedEndpointSimplePaths
        G a u v) : ℝ) * (1 / 2 : ℝ) ^ a =
      ∑ _ : Erdos1016.Proof.PathEndpointRunInjection.FixedEndpointSimplePaths G a u v,
        (1 / 2 : ℝ) ^ a := by
    rw [Fintype.card_eq_sum_ones]
    simp [Finset.sum_mul]
  simp_rw [hcard]
  have hbase (f : G.CycleWord → ℝ) :
      (∑ C ∈ bases, f C) = (∑ C : {C // C ∈ bases}, f C) := by
    exact Finset.sum_subtype bases (by intro C; rfl) f
  have hendpoints (C : G.CycleWord)
      (f : G.Vertex × G.Vertex → ℝ) :
      (∑ p ∈ Erdos1016.Proof.ExternalReturnPathMass.cycleEndpointPairs G C,
        f p) =
      (∑ p : {p // p ∈ Erdos1016.Proof.ExternalReturnPathMass.cycleEndpointPairs G C},
        f p) := by
    exact Finset.sum_subtype _ (by intro p; rfl) f
  have hlength (f : ℕ → ℝ) :
      (∑ a ∈ Finset.Ioc s L, f a) =
      (∑ a : {a // a ∈ Finset.Ioc s L}, f a) := by
    exact Finset.sum_subtype _ (by intro a; rfl) f
  rw [hbase]
  simp_rw [hendpoints, hlength]
  simp_rw [Finset.mul_sum]
  rfl

end Erdos1016.Proof.ThetaMassBridge
end

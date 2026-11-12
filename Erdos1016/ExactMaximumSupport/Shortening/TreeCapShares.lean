import Erdos1016.ExactMaximumSupport.Shortening.TreeCapCycleBound
import Erdos1016.ExactMaximum.FourCutSides
import Erdos1016.ExactMaximumSupport.FourCutArithmeticProofStates

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The three actual tree caps, in the normalized four-pole coordinates.
The adapter has no pole, connectivity, or distinct-port assumption: its lower
count and rank bounds are valid for every finite labelled network. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.TreeCapShares
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
open ExactMaximum FourCutArithmeticProof

variable {V E : Type} [Fintype V] [Fintype E]

/-- The three cap pairings, retaining the original physical port labels. -/
def capOrder (α : Fin 3) : Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![0,2,1,3], ![0,3,1,2]] α

omit [Fintype V] in
/-- Normalization of the actual cap load: all six paths and the two complementary
pairing sectors, with no combinatorial counting premise. -/
theorem normalized_load (N : Network V E) (p : Fin 4 → V) (α : Fin 3) :
    (N.numCycles:ℝ)/(2:ℝ)^networkRank N + pathSum (pathShare N p) +
      forestSum (pairShare N p) - pairShare N p α =
    (TreeCapCycleBound.load N (p (capOrder α 0)) (p (capOrder α 1))
      (p (capOrder α 2)) (p (capOrder α 3)):ℝ)/(2:ℝ)^networkRank N := by
  have h2013 := numPathPairs_eq_pairCount N p 2 0 1 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h2103 := numPathPairs_eq_pairCount N p 2 1 0 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1023 := numPathPairs_eq_pairCount N p 1 0 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1203 := numPathPairs_eq_pairCount N p 1 2 0 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1032 := numPathPairs_eq_pairCount N p 1 0 3 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1302 := numPathPairs_eq_pairCount N p 1 3 0 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change N.numPathPairs (p 1) (p 3) (p 0) (p 2) = pairCount N p 1 at h1302
  norm_num [pairingOf] at h2013 h2103 h1023 h1203 h1032 h1302
  fin_cases α <;>
    simp [capOrder,TreeCapCycleBound.load,pathSum,forestSum,pathShare,pairShare,
      h2013,h2103,h1023,h1203,h1032,h1302,pairingOf,
      numPaths_symm N (p 2) (p 1),numPaths_symm N (p 3) (p 1),
      numPaths_symm N (p 3) (p 2)] <;>
    ring

/-- At large rank, all three normalized actual tree-cap loads are at most 4.001.
The threshold is uniform over the network and all four endpoint choices. -/
theorem exists_bound :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      B ≤ networkRank N → ∀ (p : Fin 4 → V) (α : Fin 3),
      (N.numCycles:ℝ)/(2:ℝ)^networkRank N + pathSum (pathShare N p) +
        forestSum (pairShare N p) - pairShare N p α ≤ 4001/1000 := by
  obtain ⟨B,hB⟩ := TreeCapCycleBound.exists_thousandth_bound
  refine ⟨B,?_⟩
  intro V E _ _ N hr p α
  rw [normalized_load]
  have hD : (0:ℝ)<(2:ℝ)^networkRank N := by positivity
  apply (div_le_iff₀ hD).mpr
  have hc := hB V E N hr (p (capOrder α 0)) (p (capOrder α 1))
    (p (capOrder α 2)) (p (capOrder α 3))
  have hcR : (1000:ℝ)*(TreeCapCycleBound.load N (p (capOrder α 0))
      (p (capOrder α 1)) (p (capOrder α 2)) (p (capOrder α 3)):ℝ) ≤
      4001*(2:ℝ)^networkRank N := by exact_mod_cast hc
  linarith

end Erdos1016.ExactMaximumSupport.Shortening.TreeCapShares

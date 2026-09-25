import Erdos1016.Extremal.Capacity.AlphaCapacity
import Erdos1016.Extremal.Capacity.WitnessSupport
import Erdos1016.Extremal.Capacity.RestrictedCapacityEquiv

set_option autoImplicit false

/-!
# Finite witness families give local α-capacity envelopes

The union support of a family witnessing every cycle length through `L` is
itself a graph in the defining class for `alphaCapacity L`. Restricting the
host graph to those support edges is exactly its physical support graph, so
the global supremum controls every restricted linear-forest multiplicity.
-/

noncomputable section
namespace Erdos1016
namespace PhysicalGraph

/-- The literal witness support graph is the physical reindexing of the
support edge set. -/
theorem witnessSupportGraph_eq_restrictPhysical (G : PhysicalGraph)
    (F : Finset G.CycleWord) :
    witnessSupportGraph G F = G.restrictPhysical (witnessSupportEdges G F) := by
  cases G
  rfl

/-- If a finite family contains a cycle of every length from three through
`L`, then each demand's restricted forest multiplicity on the support edges
is bounded by the local `α(L)` envelope times the support cycle-space size. -/
theorem restrictedMultiplicity_le_alpha_of_witnessFamily
    (G : PhysicalGraph) (F : Finset G.CycleWord) (L : ℕ)
    (witness : ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ L →
      ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ)
    (t : G.Demand) :
    (G.restrictedLinearForestMultiplicity (witnessSupportEdges G F) t : ℝ) ≤
      (2 : ℝ) ^ G.restrictedCycleRank (witnessSupportEdges G F) *
        alphaCapacity L := by
  let E := witnessSupportEdges G F
  let W := witnessSupportGraph G F
  have hcover : W.InitialCoverage L :=
    initialCoverage_of_witnessFamily G F L witness
  have hWmem : W.normalizedLinearForestCapacity ∈ alphaCapacitySet L := by
    exact ⟨W, hcover, rfl⟩
  have hα : W.normalizedLinearForestCapacity ≤ alphaCapacity L := by
    unfold alphaCapacity
    exact le_csSup (alphaCapacitySet_bddAbove L) hWmem
  have hμmax : (W.linearForestMultiplicity t : ℝ) ≤
      (W.maxLinearForestMultiplicity : ℝ) := by
    exact_mod_cast W.linearForestMultiplicity_le_max t
  have hscaled : (W.maxLinearForestMultiplicity : ℝ) ≤
      (2 : ℝ) ^ W.cycleRank * alphaCapacity L := by
    have hmul := mul_le_mul_of_nonneg_right hα (by positivity :
      0 ≤ (2 : ℝ) ^ W.cycleRank)
    rw [normalizedLinearForestCapacity] at hα
    rw [normalizedLinearForestCapacity] at hmul
    have hpow : (0 : ℝ) < (2 : ℝ) ^ W.cycleRank := by positivity
    have hcancel :
        ((W.maxLinearForestMultiplicity : ℝ) /
          (2 : ℝ) ^ W.cycleRank) * (2 : ℝ) ^ W.cycleRank =
          (W.maxLinearForestMultiplicity : ℝ) := by
      field_simp [ne_of_gt hpow]
    calc
      (W.maxLinearForestMultiplicity : ℝ) =
          ((W.maxLinearForestMultiplicity : ℝ) /
            (2 : ℝ) ^ W.cycleRank) * (2 : ℝ) ^ W.cycleRank := by
        symm
        exact hcancel
      _ ≤ alphaCapacity L * (2 : ℝ) ^ W.cycleRank := hmul
      _ = (2 : ℝ) ^ W.cycleRank * alphaCapacity L := by ring
  have hgraph : W = G.restrictPhysical E := by
    simpa [E, W] using witnessSupportGraph_eq_restrictPhysical G F
  have hmult : W.linearForestMultiplicity t =
      G.restrictedLinearForestMultiplicity E t := by
    change (G.restrictPhysical E).linearForestMultiplicity t =
      G.restrictedLinearForestMultiplicity E t
    exact G.restrictPhysical_linearForestMultiplicity E t
  have hrank : W.cycleRank = G.restrictedCycleRank E := by
    change (G.restrictPhysical E).cycleRank = G.restrictedCycleRank E
    exact G.restrictPhysical_cycleRank E
  simpa [hmult, hrank] using hμmax.trans hscaled

end PhysicalGraph
end Erdos1016

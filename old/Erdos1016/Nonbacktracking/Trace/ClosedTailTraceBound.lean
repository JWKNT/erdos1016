import Erdos1016.Nonbacktracking.Trace.ClosedRunNormalization

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking

variable {G : PhysicalGraph}

/-- The finite ordinary closed-run mass is bounded by three times `L` times
the source-normalized nonbacktracking trace mass, with both graph-side
decomposition and trace normalization discharged from existing run APIs. -/
theorem ordinaryClosedRunMass_prefix_le_three_L_nonbacktrackingTraceMass
    (hmax : ∀ v, G.degree v ≤ 3) (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L, ordinaryClosedRunMass (G := G) ell) ≤
      3 * (L : ℝ) * nonbacktrackingTraceMass (G := G) L := by
  exact ordinaryClosedRunMass_prefix_le_three_L_trace (G := G) hmax L
    (nonbacktrackingTraceMass (G := G) L)
    (reducedClosedRunMass_prefix_le_two_L_traceMass (G := G) L)

end Erdos1016.Nonbacktracking
end

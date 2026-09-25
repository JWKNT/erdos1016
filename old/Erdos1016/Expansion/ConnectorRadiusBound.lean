import Erdos1016.Boundary.DegreeTwoDeficit
import Erdos1016.Decomposition.TwoCore.DeletionDeficit
import Erdos1016.Nonbacktracking.Girth.CubicDeficit
import Erdos1016.Nonbacktracking.Walks.CycleWords
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Extremal

open Filter
open scoped Topology
open Erdos1016.CycleSupply



/-- When the expansion parameter is at most one, the connector radius is
bounded by the logarithmic radius obtained from `log (1 + h/3) ≥ h/4`.
This is the numerical estimate used to turn the FEW connector budget into an
asymptotic bound. -/
theorem connectorRadius_le_ceil_log_over_expansion
    (G : Erdos1016.PhysicalGraph) (h : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ G.vertexCount) :
    connectorRadius G h ≤
      Nat.ceil (4 * Real.log ((G.vertexCount : ℝ) + 1) / h) := by
  unfold connectorRadius
  apply Nat.ceil_mono
  let n : ℝ := (G.vertexCount : ℝ)
  have hx : 0 ≤ h / 3 := by positivity
  have hlogLower : h / 4 ≤ Real.log (1 + h / 3) := by
    have hlogineq := Real.le_log_one_add_of_nonneg hx
    have hsimple : h / 4 ≤ 2 * (h / 3) / (h / 3 + 2) := by
      have hden : 0 < h / 3 + 2 := by positivity
      rw [le_div_iff₀ hden]
      nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
    exact hsimple.trans hlogineq
  have hden : 0 < Real.log (1 + h / 3) := by
    exact Real.log_pos (by linarith)
  have hnum : 0 ≤ Real.log (n + 1) := by
    apply Real.log_nonneg
    dsimp [n]
    have hcast : (1 : ℝ) ≤ (G.vertexCount : ℝ) := by exact_mod_cast hn
    linarith
  have hratio : Real.log (n + 1) / Real.log (1 + h / 3) ≤
      4 * Real.log (n + 1) / h := by
    have hcmp : Real.log (n + 1) / Real.log (1 + h / 3) ≤
        Real.log (n + 1) / (h / 4) :=
      (div_le_div_iff₀ hden (by positivity)).2
        (mul_le_mul_of_nonneg_left hlogLower hnum)
    calc
      _ ≤ Real.log (n + 1) / (h / 4) := hcmp
      _ = 4 * Real.log (n + 1) / h := by field_simp; ring
  simpa [n] using hratio

end Erdos1016.Extremal

end

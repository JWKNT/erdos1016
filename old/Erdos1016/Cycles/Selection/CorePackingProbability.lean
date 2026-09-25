import Erdos1016.Expansion.ApexExpansion

set_option autoImplicit false

/-!
# The protected MANY estimate from expansion of the core itself

The apex expansion, original complement geometry, conflict graph, and event
independence are all derived. The remaining hypotheses concern the actual
connected protector and the actual disjoint short cycles. No mixing estimate
or pairwise-probability assertion is an input.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyCoreManyDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Source (9.3), finite form. The chosen core expansion parameter is
normalized to at most one, as in manuscript §9. -/
theorem coreBoundaryAverage_le_many
    (H : PhysicalGraph) (hH : H.IsConnected) (p₀ : CorePin H)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hExp : HasExpansion H Finset.univ h)
    (W : Finset (coreApexGraph H).Vertex)
    (hW : ConnectedRegion (coreApexGraph H) W)
    (F : Finset (coreApexGraph H).CycleWord) (hFne : F.Nonempty) (D : ℕ)
    (hFU : ∀ C ∈ F, Cycle.vertices C ⊆ coreApexInterior H)
    (hL : ∀ C ∈ F, BoundaryDecay.Cycle.length C ≤ D)
    (hdis : ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (havoid : ∀ C ∈ F, Disjoint (Cycle.vertices C) W)
    (hroom : 2 * (D : ℝ) + 4 * (D : ℝ) / h < (H.vertexCount : ℝ) + 1)
    (hlarge : 4 * (D : ℝ) / h < W.card) :
    coreBoundaryAverage H ≤
      (2 : ℝ) ^ D * (manyCycleConflictBound (h / 2) D + 1) / F.card := by
  have hhalf : 0 < h / 2 := div_pos hh (by norm_num)
  have harith : (2 * (D : ℝ)) / (h / 2) = 4 * (D : ℝ) / h := by
    field_simp [hh.ne'] <;> ring
  have hroom' : 2 * (D : ℝ) + (2 * (D : ℝ)) / (h / 2) <
      (coreApexGraph H).vertexCount := by
    rw [harith, apex_order]
    exact_mod_cast hroom
  have hlarge' : (2 * (D : ℝ)) / (h / 2) < W.card := by
    rwa [harith]
  exact boundaryAverage_le_protected_cycle_bound H hH p₀ hmin hmax
    (h / 2) hhalf (coreApex_hasExpansion H h hh.le (by linarith) hExp p₀)
    W hW F hFne D hFU hL hdis havoid hroom' hlarge'

end Erdos1016.CycleSupply

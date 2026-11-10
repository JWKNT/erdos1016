import Erdos1016.CycleCount.LowerBound

set_option autoImplicit false

/-!
# The maximum number of cycles

Let `maxCycles r` be the largest number of cycles of a simple graph with
cyclomatic number `r`. The cycle-count bound and the closed shortcut chain
give `maxCycles r / 2^r → 1/2`. This is the asymptotic form of the question
of Entringer and Slater.
-/

noncomputable section
open Filter Topology

namespace Erdos1016.CycleCount

/-- The numbers of cycles of the simple graphs with cyclomatic number `r`. -/
def cycleCounts (r : ℕ) : Set ℕ :=
  {c | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent ∧ numCycles G = c}

/-- The largest number of cycles of a simple graph with cyclomatic number `r`. -/
def maxCycles (r : ℕ) : ℕ := sSup (cycleCounts r)

theorem cycleCounts_bddAbove (r : ℕ) : BddAbove (cycleCounts r) := by
  refine ⟨2 ^ r, ?_⟩
  rintro c ⟨n, G, hr, rfl⟩
  exact (numCycles_lt_two_pow G r hr).le

/-- Every graph with cyclomatic number `r` has at most `maxCycles r` cycles. -/
theorem numCycles_le_maxCycles {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (hr : r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent) :
    numCycles G ≤ maxCycles r :=
  le_csSup (cycleCounts_bddAbove r) ⟨n, G, hr, rfl⟩

theorem cycleCounts_nonempty (r : ℕ) (hr : 3 ≤ r) : (cycleCounts r).Nonempty := by
  obtain ⟨n, G, hG, _⟩ := exists_graph_many_cycles (r - 1) (by omega)
  have hr1 : r - 1 + 1 = r := by omega
  rw [hr1] at hG
  exact ⟨numCycles G, n, G, hG, rfl⟩

/-- The maximum is attained. -/
theorem maxCycles_mem (r : ℕ) (hr : 3 ≤ r) : maxCycles r ∈ cycleCounts r :=
  Nat.sSup_mem (cycleCounts_nonempty r hr) (cycleCounts_bddAbove r)

/-- The elementary lower bound `2^(r-1) ≤ maxCycles r`. -/
theorem two_pow_le_maxCycles (r : ℕ) (hr : 3 ≤ r) : 2 ^ (r - 1) ≤ maxCycles r := by
  obtain ⟨n, G, hG, hc⟩ := exists_graph_many_cycles (r - 1) (by omega)
  have hr1 : r - 1 + 1 = r := by omega
  rw [hr1] at hG
  exact hc.trans (numCycles_le_maxCycles G r hG)

/-- The cycle-count bound for the maximum. -/
theorem maxCycles_le (h : CycleCountStatement) :
    ∃ r₁ : ℕ, ∀ r, r₁ ≤ r →
      (maxCycles r : ℝ) ≤
        (1 / 2 + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) * 2 ^ r := by
  obtain ⟨r₁, h₁⟩ := h
  refine ⟨max r₁ 3, fun r hr => ?_⟩
  obtain ⟨n, G, hG, hc⟩ := maxCycles_mem r (le_trans (le_max_right _ _) hr)
  rw [← hc]
  exact h₁ n G r hG (le_trans (le_max_left _ _) hr)

/-- The maximum number of cycles is asymptotically half of `2^r`. -/
def AsymptoticCycleCount : Prop :=
  Tendsto (fun r : ℕ => (maxCycles r : ℝ) / 2 ^ r) atTop (𝓝 (1 / 2))

/-- The cycle-count bound and the lower bound give the asymptotic statement. -/
theorem asymptoticCycleCount_of_statement (h : CycleCountStatement) :
    AsymptoticCycleCount := by
  obtain ⟨r₁, h₁⟩ := maxCycles_le h
  have htl : Tendsto
      (fun r : ℕ => Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp
      ((Real.tendsto_logb_atTop one_lt_two).comp
        ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop))
  have h0 : Tendsto
      (fun r : ℕ => (21 : ℝ) / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ))))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop htl
  have hupper : Tendsto
      (fun r : ℕ => (1 / 2 : ℝ) + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ))))
      atTop (𝓝 (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with r hr
    have hpow : (0 : ℝ) < 2 ^ r := by positivity
    rw [le_div_iff₀ hpow]
    have h2 : ((2 ^ (r - 1) : ℕ) : ℝ) ≤ (maxCycles r : ℝ) := by
      exact_mod_cast two_pow_le_maxCycles r hr
    have h3 : (1 / 2 : ℝ) * 2 ^ r = ((2 ^ (r - 1) : ℕ) : ℝ) := by
      push_cast
      have hr1 : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hr1, pow_succ]
      ring
    rw [h3]
    exact h2
  · filter_upwards [eventually_ge_atTop r₁] with r hr
    have hpow : (0 : ℝ) < 2 ^ r := by positivity
    rw [div_le_iff₀ hpow]
    exact h₁ r hr

end Erdos1016.CycleCount

import Erdos1016.Nonbacktracking.Trace.TailAttachmentCounts
import Erdos1016.Nonbacktracking.Trace.TailMassArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Nonbacktracking

open scoped BigOperators
variable {G : PhysicalGraph}

/-- Unnormalized mass of ordinary closed endpoint runs at edge length `ell`. -/
def ordinaryClosedRunMass (ell : ℕ) : ℝ :=
  (Fintype.card (ClosedEndpointRuns (G := G) (ell - 1)) : ℝ) / (2 : ℝ) ^ ell

/-- Unnormalized mass of cyclically reduced closed runs at edge length `ell`. -/
def reducedClosedRunMass (ell : ℕ) : ℝ :=
  (Fintype.card (ReducedClosedEndpointRuns (G := G) (ell - 1)) : ℝ) / (2 : ℝ) ^ ell

private theorem normalized_tail_factor (ell i : ℕ) (hi : 2 * (i + 1) < ell) :
    (2 : ℝ) ^ i * (1 / 2 : ℝ) ^ ell =
      (1 / 2 : ℝ) ^ (i + 2) * (1 / 2 : ℝ) ^ (ell - 2 * (i + 1)) := by
  have hie : i ≤ ell := by omega
  have hpower : (2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  have hsumPow : (1 / 2 : ℝ) ^ ell =
      (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ (ell - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsumPow]
  calc
    (2 : ℝ) ^ i * ((1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ (ell - i)) =
        (2 : ℝ) ^ i * (1 / 2 : ℝ) ^ i * (1 / 2 : ℝ) ^ (ell - i) := by ring
    _ = (1 / 2 : ℝ) ^ (ell - i) := by rw [hpower]; simp
    _ = (1 / 2 : ℝ) ^ (i + 2 + (ell - 2 * (i + 1))) := by
      congr 1
      omega
    _ = (1 / 2 : ℝ) ^ (i + 2) * (1 / 2 : ℝ) ^ (ell - 2 * (i + 1)) := by
      rw [pow_add]

private theorem div_two_pow_eq_mul_invpow (x : ℝ) (n : ℕ) :
    x / (2 : ℝ) ^ n = x * (1 / 2 : ℝ) ^ n := by
  rw [div_eq_mul_inv, ← inv_pow, one_div]

/-- The unnormalized finite tail count becomes exactly the paper's geometric
kernel after the `2^(-ell)` normalization. -/
theorem normalized_reducedRunTailCount_eq (ell : ℕ) :
    (reducedRunTailCount
      (fun k => Fintype.card (ReducedClosedEndpointRuns (G := G) k))
      (ell - 1) : ℝ) / (2 : ℝ) ^ ell =
      ∑ i ∈ Finset.range ((ell - 1) / 2),
        (1 / 2 : ℝ) ^ (i + 2) * reducedClosedRunMass (G := G)
          (ell - 2 * (i + 1)) := by
  unfold reducedRunTailCount
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt : 2 * (i + 1) < ell := by
    have h := Finset.mem_range.mp hi
    omega
  have hidx : ell - 1 - 2 * (i + 1) = ell - 2 * (i + 1) - 1 := by omega
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold reducedClosedRunMass
  rw [hidx]
  calc
    ((2 : ℝ) ^ i *
        (Fintype.card (ReducedClosedEndpointRuns (G := G)
          (ell - 2 * (i + 1) - 1)) : ℝ)) / (2 : ℝ) ^ ell
        = (Fintype.card (ReducedClosedEndpointRuns (G := G)
            (ell - 2 * (i + 1) - 1)) : ℝ) *
            ((2 : ℝ) ^ i * (1 / 2 : ℝ) ^ ell) := by
          rw [div_two_pow_eq_mul_invpow]
          ring
    _ = (1 / 2 : ℝ) ^ (i + 2) *
          ((Fintype.card (ReducedClosedEndpointRuns (G := G)
            (ell - 2 * (i + 1) - 1)) : ℝ) *
              (1 / 2 : ℝ) ^ (ell - 2 * (i + 1))) := by
          rw [normalized_tail_factor ell i hlt]
          ring
    _ = (1 / 2 : ℝ) ^ (i + 2) *
          ((Fintype.card (ReducedClosedEndpointRuns (G := G)
            (ell - 2 * (i + 1) - 1)) : ℝ) /
              (2 : ℝ) ^ (ell - 2 * (i + 1))) := by
          rw [div_two_pow_eq_mul_invpow]

/-- The graph-side pointwise ordinary-walk to cyclic-core inequality, in the
paper's normalized counts and exact tail kernel. -/
theorem ordinaryClosedRunMass_le_core_and_tails
    (hmax : ∀ v, G.degree v ≤ 3) (ell : ℕ) :
    ordinaryClosedRunMass (G := G) ell ≤ reducedClosedRunMass (G := G) ell +
      ∑ i ∈ Finset.range ((ell - 1) / 2),
        (1 / 2 : ℝ) ^ (i + 2) * reducedClosedRunMass (G := G)
          (ell - 2 * (i + 1)) := by
  have hcount := closedEndpointRuns_card_le_reducedRunTailCount (G := G) hmax
    (ell - 1)
  have hdiv := div_le_div_of_nonneg_right (Nat.cast_le.mpr hcount)
    (show 0 ≤ (2 : ℝ) ^ ell by positivity)
  rw [Nat.cast_add] at hdiv
  rw [add_div] at hdiv
  rw [normalized_reducedRunTailCount_eq (G := G) ell] at hdiv
  simpa [ordinaryClosedRunMass, reducedClosedRunMass] using hdiv

/-- Finite tail/kernel double-sum reindexing: each admissible pair
`(ell, i)` corresponds to `j = i + 1` and core length `t = ell - 2j`. -/
theorem tailKernel_double_sum_reindex (L : ℕ) (T : ℕ → ℝ) :
    (∑ ell ∈ Finset.Icc 1 L, ∑ i ∈ Finset.range ((ell - 1) / 2),
      (1 / 2 : ℝ) ^ (i + 2) * T (ell - 2 * (i + 1))) =
    ∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1) *
      ∑ t ∈ Finset.Icc 1 (L - 2 * j), T t := by
  rw [Finset.sum_sigma']
  simp_rw [Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_sigma']
  apply Finset.sum_bij
    (fun x _ => ⟨x.2 + 1, x.1 - 2 * (x.2 + 1)⟩)
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hx ⊢
    obtain ⟨⟨hEllLo, hEllHi⟩, hIdx⟩ := hx
    constructor
    · constructor <;> omega
    · constructor
      · omega
      · omega
  · intro x hx y hy hxy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hx hy
    simp only [Sigma.mk.inj_iff] at hxy
    obtain ⟨hIdx, hCore⟩ := hxy
    have hI : x.2 = y.2 := by omega
    have hxbound : 2 * (x.2 + 1) ≤ x.1 := by omega
    have hybound : 2 * (y.2 + 1) ≤ y.1 := by omega
    have hCore' : x.1 - 2 * (x.2 + 1) = y.1 - 2 * (x.2 + 1) := by
      simpa [hI] using hCore
    have hEll : x.1 = y.1 := by
      have := congrArg (fun n => n + 2 * (x.2 + 1)) hCore'
      have hybound' : 2 * (x.2 + 1) ≤ y.1 := by omega
      simp only [Nat.sub_add_cancel hxbound, Nat.sub_add_cancel hybound'] at this
      exact this
    cases x
    cases y
    simp_all
  · intro b hb
    cases b with
    | mk j t =>
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hb
      obtain ⟨⟨hJLo, hJHi⟩, hTLo, hTHi⟩ := hb
      refine ⟨⟨t + 2 * j, j - 1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range]
        constructor
        · constructor <;> omega
        · omega
      · simp only [Sigma.mk.inj_iff]
        have hj : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
        rw [hj, Nat.add_sub_cancel_right]
        exact ⟨rfl, HEq.rfl⟩
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hx
    obtain ⟨_, hIdx⟩ := hx
    simp only [Sigma.mk.inj_iff]

/-- Summing the pointwise seam-stripping estimate over lengths gives the
finite aggregate tail decomposition used by the paper. -/
theorem ordinaryClosedRunMass_prefix_le_core_and_tails
    (hmax : ∀ v, G.degree v ≤ 3) (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L, ordinaryClosedRunMass (G := G) ell) ≤
      (∑ ell ∈ Finset.Icc 1 L, reducedClosedRunMass (G := G) ell) +
        ∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1) *
          ∑ t ∈ Finset.Icc 1 (L - 2 * j), reducedClosedRunMass (G := G) t := by
  calc
    _ ≤ ∑ ell ∈ Finset.Icc 1 L,
        (reducedClosedRunMass (G := G) ell +
          ∑ i ∈ Finset.range ((ell - 1) / 2),
            (1 / 2 : ℝ) ^ (i + 2) * reducedClosedRunMass (G := G)
              (ell - 2 * (i + 1))) := by
          apply Finset.sum_le_sum
          intro ell hell
          exact ordinaryClosedRunMass_le_core_and_tails (G := G) hmax ell
    _ = (∑ ell ∈ Finset.Icc 1 L,
          reducedClosedRunMass (G := G) ell) +
        ∑ ell ∈ Finset.Icc 1 L,
          ∑ i ∈ Finset.range ((ell - 1) / 2),
            (1 / 2 : ℝ) ^ (i + 2) * reducedClosedRunMass (G := G)
              (ell - 2 * (i + 1)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ ell ∈ Finset.Icc 1 L,
          reducedClosedRunMass (G := G) ell) +
        ∑ j ∈ Finset.Icc 1 L, (1 / 2 : ℝ) ^ (j + 1) *
          ∑ t ∈ Finset.Icc 1 (L - 2 * j), reducedClosedRunMass (G := G) t := by
          rw [tailKernel_double_sum_reindex]

/-- The graph-side estimate discharges `hdecomp` in the abstract aggregate
trace-to-core inequality. Only the separate cyclic-trace normalization remains
as an explicit premise. -/
theorem ordinaryClosedRunMass_prefix_le_three_L_trace
    (hmax : ∀ v, G.degree v ≤ 3) (L : ℕ) (traceMass : ℝ)
    (htrace :
      (∑ t ∈ Finset.Icc 1 L, reducedClosedRunMass (G := G) t) ≤
        2 * (L : ℝ) * traceMass) :
    (∑ ell ∈ Finset.Icc 1 L, ordinaryClosedRunMass (G := G) ell) ≤
      3 * (L : ℝ) * traceMass := by
  have hcore : 0 ≤ ∑ ell ∈ Finset.Icc 1 L,
      reducedClosedRunMass (G := G) ell := by
    apply Finset.sum_nonneg
    intro ell hell
    dsimp [reducedClosedRunMass]
    positivity
  exact Erdos1016.Proof.CycleRunTailArithmetic.ordinary_closed_mass_le_three_L_trace
    L
    (∑ ell ∈ Finset.Icc 1 L, ordinaryClosedRunMass (G := G) ell)
    (∑ ell ∈ Finset.Icc 1 L, reducedClosedRunMass (G := G) ell)
    traceMass (reducedClosedRunMass (G := G)) hcore
    (ordinaryClosedRunMass_prefix_le_core_and_tails (G := G) hmax L)
    (by
      intro t ht
      dsimp [reducedClosedRunMass]
      positivity)
    rfl htrace

end Erdos1016.Nonbacktracking
end

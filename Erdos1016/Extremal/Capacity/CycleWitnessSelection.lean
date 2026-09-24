import Erdos1016.Extremal.Capacity.WitnessRankBounds

set_option autoImplicit false

/-!
# Finite short-cycle witness selection

Given initial coverage, choose one physical cycle for each required length.
The resulting finite family gives the quadratic support bound used by the
paper's witness-preserving reduction.
-/

noncomputable section
namespace Erdos1016.Proof.Capacity

private def chosenCycle (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) (k : {n // n ∈ Finset.Icc 3 L}) : G.CycleWord :=
  Classical.choose (by
    have hk := hcov k.2
    unfold PhysicalGraph.cycleLengths at hk
    rcases Finset.mem_image.mp hk with ⟨C, _, hlen⟩
    exact ⟨C, hlen⟩)

private theorem chosenCycle_length (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) (k : {n // n ∈ Finset.Icc 3 L}) :
    G.wordLength (chosenCycle G L hcov k).1 = k.1 := by
  unfold chosenCycle
  exact Classical.choose_spec (by
    have hk := hcov k.2
    unfold PhysicalGraph.cycleLengths at hk
    rcases Finset.mem_image.mp hk with ⟨C, _, hlen⟩
    exact ⟨C, hlen⟩)

/-- The chosen family contains a cycle of every required length. -/
def canonicalCycleWitnesses (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) : Finset G.CycleWord := by
  classical
  exact Finset.univ.image (chosenCycle G L hcov)

theorem canonicalCycleWitnesses_has_all_lengths (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) :
    G.HasCycleWitnessFamily (canonicalCycleWitnesses G L hcov) L := by
  classical
  intro ℓ hℓL hLℓ
  let k : {n // n ∈ Finset.Icc 3 L} := ⟨ℓ, Finset.mem_Icc.mpr ⟨hℓL, hLℓ⟩⟩
  refine ⟨chosenCycle G L hcov k, ?_, ?_⟩
  · change chosenCycle G L hcov k ∈ Finset.univ.image (chosenCycle G L hcov)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  exact chosenCycle_length G L hcov k

/-- A coarse but sufficient quadratic upper bound on the sum of selected
cycle lengths: each selected length is at most `L`, and image-cardinality
cannot exceed the `L - 2` required lengths. -/
theorem canonicalCycleWitnesses_sum_lengths_le (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) :
    (∑ C ∈ canonicalCycleWitnesses G L hcov, G.wordLength C.1) ≤ (L - 2) * L := by
  classical
  let F := canonicalCycleWitnesses G L hcov
  have hcard : F.card ≤ L - 2 := by
    dsimp [F, canonicalCycleWitnesses]
    calc
      (Finset.univ.image (chosenCycle G L hcov)).card ≤ Finset.univ.card := Finset.card_image_le
      _ = (Finset.Icc 3 L).card := by simp
      _ = L - 2 := by simp [Nat.card_Icc]
  have hsum : (∑ C ∈ F, G.wordLength C.1) ≤ ∑ _C ∈ F, L := by
    apply Finset.sum_le_sum
    intro C hC
    have hmem : C ∈ Finset.univ.image (chosenCycle G L hcov) := by
      change C ∈ Finset.univ.image (chosenCycle G L hcov) at hC
      exact hC
    rcases Finset.mem_image.mp hmem with ⟨k, _, hCeq⟩
    subst C
    rw [chosenCycle_length]
    exact (Finset.mem_Icc.mp k.2).2
  calc
    (∑ C ∈ F, G.wordLength C.1) ≤ ∑ _C ∈ F, L := hsum
    _ = F.card * L := by simp
    _ ≤ (L - 2) * L := Nat.mul_le_mul_right L hcard

/-- The literal union support retains every cycle length represented by the
canonical witness family. -/
theorem canonicalWitnessSupport_initialCoverage (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) :
    (witnessSupportGraph G (canonicalCycleWitnesses G L hcov)).InitialCoverage L := by
  exact Erdos1016.initialCoverage_of_witnessFamily G (canonicalCycleWitnesses G L hcov) L
    (canonicalCycleWitnesses_has_all_lengths G L hcov)

/-- The selected support graph has enough cycle rank to encode the whole
initial interval. -/
theorem canonicalWitnessSupport_rank_bound (G : PhysicalGraph) (L : ℕ)
    (hcov : G.InitialCoverage L) :
    L ≤ 2 ^ (witnessSupportGraph G (canonicalCycleWitnesses G L hcov)).cycleRank + 1 :=
  (witnessSupportGraph G (canonicalCycleWitnesses G L hcov)).coverage_bound
    (canonicalWitnessSupport_initialCoverage G L hcov)

/-- The canonical short-cycle support satisfies the reduction's exponential
edge budget at the scale `L = 2^(2R)+1`. -/
theorem canonicalWitnessSupport_add_one_le_power (G : PhysicalGraph) (R : ℕ)
    (hR : 5 ≤ R) (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    (witnessSupportGraph G (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).edgeCount + 1
      ≤ 2 ^ (4 * R) := by
  have hsum := canonicalCycleWitnesses_sum_lengths_le G (2 ^ (2 * R) + 1) hcov
  have hedge := G.witnessSupport_edgeCount_le_sum_lengths
    (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)
  have hX : 2 ≤ 2 ^ (2 * R) := by
    have he : 1 ≤ 2 * R := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by omega) he
  let X : ℕ := 2 ^ (2 * R)
  have hX' : 1 ≤ X := by
    dsimp [X]
    exact (show 1 ≤ 2 by omega).trans hX
  have hpow : X ^ 2 = 2 ^ (4 * R) := by
    dsimp [X]
    rw [← pow_mul]
    congr 1
    omega
  have hprod : (X - 1) * (X + 1) + 1 ≤ 2 ^ (4 * R) := by
    have hsub : X - 1 + 1 = X := Nat.sub_add_cancel hX'
    calc
      (X - 1) * (X + 1) + 1 ≤ X ^ 2 := by nlinarith [hsub]
      _ = 2 ^ (4 * R) := hpow
  have hLsub : (2 ^ (2 * R) + 1) - 2 = X - 1 := by dsimp [X]; omega
  have hL : 2 ^ (2 * R) + 1 = X + 1 := by rfl
  have hsum' := Nat.add_le_add_right hsum 1
  calc
    _ ≤ (∑ C ∈ canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov,
          G.wordLength C.1) + 1 := Nat.add_le_add_right hedge 1
    _ ≤ ((2 ^ (2 * R) + 1) - 2) * (2 ^ (2 * R) + 1) + 1 := hsum'
    _ = (X - 1) * (X + 1) + 1 := by rw [hLsub, hL]
    _ ≤ 2 ^ (4 * R) := hprod

end Erdos1016.Proof.Capacity

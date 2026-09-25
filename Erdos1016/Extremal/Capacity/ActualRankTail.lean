import Erdos1016.Extremal.Capacity.CycleLengths

set_option autoImplicit false

/-!
# Tail density at the actual cycle rank

The supremum uses the actual rank of each graph, rather than a rank budget
used to define an initial-coverage extremum. The zero baseline makes the
supremum nonempty without a graph-padding argument; all positive witnesses
are precisely the normalized initial-coverage densities of actual graphs.
-/

noncomputable section
namespace Erdos1016.ShortProof

/-- The normalized length of an initial interval of cycle lengths in one graph. -/
def coverageDensity (G : PhysicalGraph) (L : ℕ) : ℝ :=
  ((L : ℝ) - 2) / (2 : ℝ) ^ G.cycleRank

theorem coverageDensity_nonneg (G : PhysicalGraph) {L : ℕ} (hL : 2 ≤ L) :
    0 ≤ coverageDensity G L := by
  unfold coverageDensity
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hL)) (by positivity)

theorem coverageDensity_le_one (G : PhysicalGraph) {L : ℕ}
    (hL : G.InitialCoverage L) : coverageDensity G L ≤ 1 := by
  have hbound : (L : ℝ) ≤ (2 : ℝ) ^ G.cycleRank + 1 := by
    exact_mod_cast G.coverage_bound hL
  unfold coverageDensity
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ G.cycleRank)).2
  linarith

/-- Actual-rank coverage densities, together with the zero baseline. -/
def rankTailDensities (R : ℕ) : Set ℝ :=
  {x | x = 0 ∨ ∃ (G : PhysicalGraph) (L : ℕ),
    R ≤ G.cycleRank ∧ G.InitialCoverage L ∧ x = coverageDensity G L}

/-- The tail supremum over graphs whose actual cycle rank is at least `R`. -/
def actualRankTail (R : ℕ) : ℝ := sSup (rankTailDensities R)

theorem rankTailDensities_nonempty (R : ℕ) : (rankTailDensities R).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem rankTailDensities_bddAbove (R : ℕ) : BddAbove (rankTailDensities R) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨G, L, _, hL, rfl⟩)
  · norm_num
  · exact coverageDensity_le_one G hL

theorem actualRankTail_bounds (R : ℕ) :
    0 ≤ actualRankTail R ∧ actualRankTail R ≤ 1 := by
  constructor
  · exact le_csSup (rankTailDensities_bddAbove R) (Or.inl rfl)
  · apply csSup_le (rankTailDensities_nonempty R)
    rintro x (rfl | ⟨G, L, _, hL, rfl⟩)
    · norm_num
    · exact coverageDensity_le_one G hL

theorem actualRankTail_antitone : Antitone actualRankTail := by
  intro a b hab
  apply csSup_le_csSup (rankTailDensities_bddAbove a) (rankTailDensities_nonempty b)
  rintro x (rfl | ⟨G, L, hb, hL, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨G, L, hab.trans hb, hL, rfl⟩

/-- Every realized cycle-length prefix is controlled at every smaller rank threshold. -/
theorem coverageDensity_le_actualRankTail (G : PhysicalGraph) {R L : ℕ}
    (hR : R ≤ G.cycleRank) (hL : G.InitialCoverage L) :
    coverageDensity G L ≤ actualRankTail R := by
  exact le_csSup (rankTailDensities_bddAbove R) (Or.inr ⟨G, L, hR, hL, rfl⟩)

/-- A pointwise estimate on actual graph densities passes to the tail supremum. -/
theorem actualRankTail_le {R : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hgraphs : ∀ (G : PhysicalGraph) (L : ℕ), R ≤ G.cycleRank →
      G.InitialCoverage L → coverageDensity G L ≤ B) :
    actualRankTail R ≤ B := by
  apply csSup_le (rankTailDensities_nonempty R)
  rintro x (rfl | ⟨G, L, hR, hL, rfl⟩)
  · exact hB
  · exact hgraphs G L hR hL

/-- The normalized tail bound, expressed as a length bound for a greedy step. -/
theorem coverage_le_actualRankTail_mul (G : PhysicalGraph) {R L : ℕ}
    (hR : R ≤ G.cycleRank) (hL : G.InitialCoverage L) :
    (L : ℝ) ≤ actualRankTail R * (2 : ℝ) ^ G.cycleRank + 2 := by
  have h := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ G.cycleRank)).1
    (coverageDensity_le_actualRankTail G hR hL)
  linarith

end Erdos1016.ShortProof

import Erdos1016.Extremal.Capacity.CoverageExtraction
import Erdos1016.Extremal.Capacity.WitnessProbabilityComposition
import Erdos1016.Extremal.Capacity.HighCycleTailRecurrence

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.FiniteGreedyStages

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Extremal
open Erdos1016.Proof.FiniteAlphaBridge
open Erdos1016.Proof.FiniteAlphaExtraction

/-- Every length through `k` has a host cycle supported on `E`. -/
def SupportedPrefix (G : PhysicalGraph) (E : Finset G.Edge) (k : ℕ) : Prop :=
  ∀ ℓ, 3 ≤ ℓ → ℓ ≤ k →
    ∃ C : G.CycleWord, G.wordLength C.1 = ℓ ∧ G.edgeSupport C.1 ⊆ E

/-- Transfer a supported host-cycle prefix to the physical restriction. -/
theorem restrictPhysical_initialCoverage_of_supportedPrefix
    (G : PhysicalGraph) (E : Finset G.Edge) (k : ℕ)
    (hprefix : SupportedPrefix G E k) :
    (G.restrictPhysical E).InitialCoverage k := by
  intro ℓ hℓ
  rcases Finset.mem_Icc.mp hℓ with ⟨h3, hℓk⟩
  obtain ⟨C, hlen, hsupp⟩ := hprefix ℓ h3 hℓk
  obtain ⟨D, hD⟩ := restrictCycleWord_isCycle G E C hsupp
  have hlenD : (G.restrictPhysical E).wordLength D.1 = ℓ := by
    calc
      (G.restrictPhysical E).wordLength D.1 =
          (G.restrictPhysical E).wordLength (restrictCycleWord G E C) :=
        congrArg (G.restrictPhysical E).wordLength hD
      _ = G.wordLength C.1 := restrictCycleWord_length G E C hsupp
      _ = ℓ := hlen
  unfold cycleLengths
  exact Finset.mem_image.mpr ⟨D, Finset.mem_univ _, hlenD⟩

/-- State invariant for the greedy extension. The function `cost` records
new edges at their preceding cycle rank; later skipped ranks have cost zero. -/
def GreedyInvariant (G : PhysicalGraph) (E : Finset G.Edge) (k : ℕ)
    (cost : ℕ → ℕ) : Prop :=
  SupportedPrefix G E k ∧
  (∀ s, s < G.restrictedCycleRank E → cost s ≤ initialCapacity s + 1) ∧
  (∀ s, G.restrictedCycleRank E ≤ s → cost s = 0) ∧
  E.card ≤ ∑ s ∈ Finset.range (G.restrictedCycleRank E), cost s

private theorem sum_range_update_of_tail_zero
    (c : ℕ → ℕ) (p q d : ℕ) (hpq : p < q)
    (htail : ∀ s, p ≤ s → c s = 0) :
    (∑ s ∈ Finset.range q, Function.update c p d s) =
      (∑ s ∈ Finset.range p, c s) + d := by
  have hdecomp := Finset.sum_range_add_sum_Ico
    (fun s => Function.update c p d s) (Nat.le_of_lt hpq)
  have hlow : (∑ s ∈ Finset.range p, Function.update c p d s) =
      ∑ s ∈ Finset.range p, c s := by
    apply Finset.sum_congr rfl
    intro s hs
    have hslt : s < p := Finset.mem_range.mp hs
    simp [Function.update_of_ne, ne_of_lt hslt]
  have hpmem : p ∈ Finset.Ico p q := Finset.mem_Ico.mpr ⟨le_rfl, hpq⟩
  have hzero : (∑ s ∈ (Finset.Ico p q).erase p,
      Function.update c p d s) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hsIco : s ∈ Finset.Ico p q := Finset.mem_of_mem_erase hs
    have hsne : s ≠ p := (Finset.mem_erase.mp hs).1
    have hszero := htail s (Finset.mem_Ico.mp hsIco).1
    simp [Function.update_of_ne, hsne, hszero]
  have hIco : (∑ s ∈ Finset.Ico p q, Function.update c p d s) = d := by
    rw [← Finset.sum_erase_add (Finset.Ico p q)
      (fun s => Function.update c p d s) hpmem, hzero]
    simp
  rw [← hdecomp, hlow, hIco]

/-- Extend one greedy stage. If length `k+1` is already represented inside
the current support, retain the state. Otherwise add a host cycle of that
length and charge its whole length at the preceding rank. -/
theorem greedy_extend_one
    (G : PhysicalGraph) (L k : ℕ) (hcov : G.InitialCoverage L)
    (hk2 : 2 ≤ k) (hkL : k < L)
    (E : Finset G.Edge) (cost : ℕ → ℕ)
    (hstate : GreedyInvariant G E k cost) :
    ∃ E' cost', GreedyInvariant G E' (k + 1) cost' := by
  rcases hstate with ⟨hprefix, hcostBound, hcostTail, hedge⟩
  let p := G.restrictedCycleRank E
  by_cases hexists : ∃ C : G.CycleWord,
      G.wordLength C.1 = k + 1 ∧ G.edgeSupport C.1 ⊆ E
  · refine ⟨E, cost, ?_⟩
    refine ⟨?_, hcostBound, hcostTail, hedge⟩
    intro ℓ hℓ3 hℓk
    by_cases hℓ : ℓ ≤ k
    · exact hprefix ℓ hℓ3 hℓ
    · have hℓeq : ℓ = k + 1 := by omega
      rcases hexists with ⟨C, hlen, hsupp⟩
      exact ⟨C, by omega, by simpa [hℓeq] using hsupp⟩
  · have hmem : k + 1 ∈ G.cycleLengths := by
      apply hcov
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hcycleSet : ∃ C : G.CycleWord, G.wordLength C.1 = k + 1 := by
      unfold cycleLengths at hmem
      rcases Finset.mem_image.mp hmem with ⟨C, _, hlen⟩
      exact ⟨C, hlen⟩
    obtain ⟨C, hlen⟩ := hcycleSet
    have hnew : ¬ G.edgeSupport C.1 ⊆ E := by
      intro hsupp
      exact hexists ⟨C, hlen, hsupp⟩
    let F := E ∪ G.edgeSupport C.1
    let q := G.restrictedCycleRank F
    let d := G.wordLength C.1
    let cost' := Function.update cost p d
    have hEF : E ⊆ F := Finset.subset_union_left
    have hcycleF : G.edgeSupport C.1 ⊆ F := Finset.subset_union_right
    have hpq : p < q := by
      dsimp [p, q, F]
      exact restrictedCycleRank_lt_of_new_cycle G E (E ∪ G.edgeSupport C.1)
        C Finset.subset_union_left Finset.subset_union_right hnew
    have hprefixF : SupportedPrefix G F (k + 1) := by
      intro ℓ hℓ3 hℓk
      by_cases hℓ : ℓ ≤ k
      · obtain ⟨D, hlenD, hsuppD⟩ := hprefix ℓ hℓ3 hℓ
        exact ⟨D, hlenD, Finset.Subset.trans hsuppD hEF⟩
      · have hℓeq : ℓ = k + 1 := by omega
        subst ℓ
        exact ⟨C, hlen, by simpa [F]⟩
    have hHcov : (G.restrictPhysical E).InitialCoverage k :=
      restrictPhysical_initialCoverage_of_supportedPrefix G E k hprefix
    have hI : k ≤ initialCapacity p := by
      have hpc : (G.restrictPhysical E).cycleRank ≤ p := by
        rw [G.restrictPhysical_cycleRank]
      exact coverage_le_initialCapacity (G.restrictPhysical E) hpc hHcov
    have hcostD : d ≤ initialCapacity p + 1 := by
      dsimp [d]
      rw [hlen]
      exact Nat.add_le_add_right hI 1
    have hcostBound' : ∀ s, s < q → cost' s ≤ initialCapacity s + 1 := by
      intro s hs
      by_cases hsp : s = p
      · subst s
        simp [cost', Function.update_same, hcostD]
      · have hupdate : cost' s = cost s := by simp [cost', Function.update_of_ne, hsp]
        rw [hupdate]
        by_cases hlt : s < p
        · exact hcostBound s hlt
        · have hle : p ≤ s := by omega
          rw [hcostTail s hle]
          omega
    have hcostTail' : ∀ s, q ≤ s → cost' s = 0 := by
      intro s hs
      have hne : s ≠ p := by omega
      simp [cost', Function.update_of_ne, hne, hcostTail s (by omega)]
    have hsum' : (∑ s ∈ Finset.range q, cost' s) =
        (∑ s ∈ Finset.range p, cost s) + d := by
      dsimp [cost']
      exact sum_range_update_of_tail_zero cost p q d hpq hcostTail
    have hedgeF : F.card ≤ E.card + d := by
      dsimp [F, d]
      calc
        (E ∪ G.edgeSupport C.1).card ≤ E.card + (G.edgeSupport C.1).card :=
          Finset.card_union_le _ _
        _ = E.card + G.wordLength C.1 := by simp [wordLength]
    have hedge' : F.card ≤ ∑ s ∈ Finset.range q, cost' s := by
      rw [hsum']
      exact hedgeF.trans (Nat.add_le_add_right hedge d)
    exact ⟨F, cost', hprefixF, hcostBound', hcostTail', hedge'⟩

private theorem greedy_base (G : PhysicalGraph) :
    GreedyInvariant G ∅ 2 (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ℓ h3 hℓ
    omega
  · intro s hs
    simp
  · intro s hs
    simp
  · simp

/-- Run the finite prefix extension from 2 through any target `L ≥ 2`. -/
theorem greedy_prefix_state (G : PhysicalGraph) (L : ℕ) (hL : 2 ≤ L)
    (hcov : G.InitialCoverage L) :
    ∃ E : Finset G.Edge, ∃ cost : ℕ → ℕ,
      GreedyInvariant G E L cost := by
  have hrun : ∀ n : ℕ, 2 + n ≤ L →
      ∃ E : Finset G.Edge, ∃ cost : ℕ → ℕ,
        GreedyInvariant G E (2 + n) cost := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨∅, fun _ => 0, greedy_base G⟩
    | succ n ih =>
        intro hn
        obtain ⟨E, cost, hstate⟩ := ih (by omega)
        obtain ⟨E', cost', hstate'⟩ := greedy_extend_one G L (2 + n)
          hcov (by omega) (by omega) E cost hstate
        exact ⟨E', cost', by simpa [Nat.add_assoc] using hstate'⟩
  have hstate := hrun (L - 2) (by omega)
  obtain ⟨E, cost, hstate⟩ := hstate
  refine ⟨E, cost, ?_⟩
  have hidx : 2 + (L - 2) = L := by omega
  simpa [hidx] using hstate

/-- Initial coverage through `2^(2R)+1` yields the actual greedy edge budget
required by the finite alpha bridge. -/
theorem edgeBudgetCertificate_of_initialCoverage
    (G : PhysicalGraph) (R : ℕ) (hR : 5 ≤ R)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    EdgeBudgetCertificate R (tailCapacity R) G := by
  let L := 2 ^ (2 * R) + 1
  have hL : 2 ≤ L := by
    dsimp [L]
    have hpowpos : 0 < 2 ^ (2 * R) := by positivity
    omega
  obtain ⟨E, cost, hstate⟩ := greedy_prefix_state G L hL
    (by simpa [L] using hcov)
  rcases hstate with ⟨hprefix, hcostBound, hcostTail, hedge⟩
  let p := G.restrictedCycleRank E
  have hHcov : (G.restrictPhysical E).InitialCoverage L :=
    restrictPhysical_initialCoverage_of_supportedPrefix G E L hprefix
  have hcover : L ≤ 2 ^ p + 1 := by
    have h := (G.restrictPhysical E).coverage_bound hHcov
    simpa [p, G.restrictPhysical_cycleRank] using h
  have hpow : 2 ^ (2 * R) ≤ 2 ^ p := by
    dsimp [L] at hcover
    omega
  have hp : 2 * R ≤ p :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow
  have hRp : R ≤ p := by omega
  have htail : ∀ s : ℕ, R ≤ s → initialCapacityExcess s ≤ tailCapacity R := by
    intro s hs
    have hbdd : BddAbove
        {x : ℝ | ∃ r : ℕ, R ≤ r ∧ x = initialCapacityExcess r} := by
      refine ⟨1, ?_⟩
      rintro x ⟨r, _, rfl⟩
      exact initialCapacityExcess_le_one r
    unfold tailCapacity
    exact le_csSup hbdd ⟨s, hs, rfl⟩
  have hsum := rank_indexed_greedy_cost_sum_le R p (tailCapacity R) hR hRp
    htail cost hcostBound
  have hedgeCast :
      (((G.restrictPhysical E).edgeCount + 1 : ℕ) : ℝ) ≤
        (((∑ s ∈ Finset.range p, cost s : ℕ) + 1 : ℕ) : ℝ) := by
    have hEdgeCount : (G.restrictPhysical E).edgeCount = E.card := by
      rfl
    rw [hEdgeCount]
    exact_mod_cast Nat.add_le_add_right hedge 1
  have hbudget := hedgeCast.trans hsum
  refine ⟨E, p, hp, rfl, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hbudget

/-- The greedy stages complete the finite alpha-to-tail bridge without an
additional graph-specific hypothesis. -/
theorem alphaCapacity_le_tail_of_initialCoverage
    (R : ℕ) (hR : 5 ≤ R) :
    alphaCapacity (2 ^ (2 * R) + 1) ≤
      tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
  apply alphaCapacity_le_tail_of_edgeBudgetCertificate R hR
  intro G hcov
  exact edgeBudgetCertificate_of_initialCoverage G R hR hcov

private theorem inv_two_pow_le_sub_rpow (N m n : ℕ)
    (hm : m ≤ N) (hn : N ≤ n) :
    1 / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ ((m : ℝ) - (N : ℝ)) := by
  let k := N - m
  have hk : k ≤ n := by dsimp [k]; omega
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk)
  have hinv : 1 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ k :=
    one_div_le_one_div_of_le (by positivity) hpow
  have hcast : (k : ℝ) = (N : ℝ) - m := by
    dsimp [k]
    rw [Nat.cast_sub hm]
  have hexp : (m : ℝ) - (N : ℝ) = -(k : ℝ) := by rw [hcast]; ring
  calc
    1 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ k := hinv
    _ = (2 : ℝ) ^ (-(k : ℝ)) := by
      rw [one_div]
      rw [← Real.rpow_natCast (2 : ℝ) k]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (2 : ℝ) ^ ((m : ℝ) - (N : ℝ)) := by rw [hexp]

/-- The finite alpha bridge and witness-composition inequality give the exact
Section 10 numerical output once the complement-loss argument supplies its
forest-probability bound and both pure-side rank exponents are large. -/
theorem normalizedCycleCount_le_of_witnessForestBound
    (G : PhysicalGraph) (R r : ℕ) (hR : 5 ≤ R) (hrank : G.cycleRank ≤ r)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1))
    (F : Finset G.CycleWord)
    (witness : ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ 2 ^ (2 * R) + 1 →
      ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ)
    (E : Finset G.Edge) (hE : E = witnessSupportEdges G F)
    (hprob : G.outsideLinearForestProbability E ≤ (1 / 2 : ℝ) + 1 / (R : ℝ))
    (houtside : 2 * R ≤
      G.outsideCycleRank E + G.commonBoundaryRank E)
    (hinside : 2 * R ≤ G.restrictedCycleRank E + G.commonBoundaryRank E) :
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
        (2 : ℝ) ^ (2 - (R : ℝ)) := by
  let L := 2 ^ (2 * R) + 1
  let q : ℝ := (1 / 2 : ℝ) + 1 / (R : ℝ)
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast (by omega : 2 ≤ R)
    have hinv : 1 / (R : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hRreal
    linarith
  have hα := alphaCapacity_le_tail_of_initialCoverage R hR
  have hαnonneg : 0 ≤ alphaCapacity L := (alphaCapacity_bounds L).1
  have hαprod : alphaCapacity L * G.outsideLinearForestProbability E ≤
      q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) := by
    have hαL : alphaCapacity L ≤ tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
      simpa [L] using hα
    have hprob' : G.outsideLinearForestProbability E ≤ q := by simpa [q] using hprob
    calc
      alphaCapacity L * G.outsideLinearForestProbability E =
          G.outsideLinearForestProbability E * alphaCapacity L := by ring
      _ ≤ q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) :=
        mul_le_mul hprob' hαL hαnonneg hqnonneg
  have hcompose := G.normalized_cycleLengths_card_le_witness_forest_probability
    F L witness
  have hrankDen : (2 : ℝ) ^ G.cycleRank ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hrank)
  have hnorm : (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · exact hrankDen
  have hout' : 1 / (2 : ℝ) ^
      (G.outsideCycleRank E + G.commonBoundaryRank E) ≤
        (2 : ℝ) ^ (1 - (2 * R : ℝ)) := by
    convert inv_two_pow_le_sub_rpow (2 * R) 1
      (G.outsideCycleRank E + G.commonBoundaryRank E) (by omega) houtside using 1 <;>
        norm_num [Nat.cast_mul]
  have hin' : 1 / (2 : ℝ) ^
      (G.restrictedCycleRank E + G.commonBoundaryRank E) ≤
        (2 : ℝ) ^ (1 - (2 * R : ℝ)) := by
    convert inv_two_pow_le_sub_rpow (2 * R) 1
      (G.restrictedCycleRank E + G.commonBoundaryRank E) (by omega) hinside using 1 <;>
        norm_num [Nat.cast_mul]
  have hsmall : (2 : ℝ) ^ (1 - (2 * R : ℝ)) ≤
      (2 : ℝ) ^ (1 - (R : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hRreal : (0 : ℝ) ≤ R := by positivity
    linarith
  have herror : q * (2 : ℝ) ^ (1 - (R : ℝ)) +
      2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) ≤ (2 : ℝ) ^ (2 - (R : ℝ)) := by
    have hqerr : q * (2 : ℝ) ^ (1 - (R : ℝ)) ≤
        (2 : ℝ) ^ (1 - (R : ℝ)) :=
      calc
        q * (2 : ℝ) ^ (1 - (R : ℝ)) ≤
            1 * (2 : ℝ) ^ (1 - (R : ℝ)) :=
          mul_le_mul_of_nonneg_right hqle
            (by positivity : 0 ≤ (2 : ℝ) ^ (1 - (R : ℝ)))
        _ = (2 : ℝ) ^ (1 - (R : ℝ)) := by ring
    have hsmall2 : 2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) ≤
        (2 : ℝ) ^ (1 - (R : ℝ)) := by
      have hid : 2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) =
          (2 : ℝ) ^ (1 - (2 * R : ℝ) + 1) := by
        calc
          2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) =
              (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (1 - (2 * R : ℝ)) := by
            rw [Real.rpow_one]
          _ = (2 : ℝ) ^ (1 - (2 * R : ℝ) + 1) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1 <;> ring
      rw [hid]
      have hexp : (1 : ℝ) - (2 * R : ℝ) + 1 ≤ 1 - (R : ℝ) := by
        have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
        linarith
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    rw [show (2 : ℝ) ^ (2 - (R : ℝ)) =
      (2 : ℝ) ^ (1 - (R : ℝ)) * 2 by
        calc
          (2 : ℝ) ^ (2 - (R : ℝ)) =
              (2 : ℝ) ^ ((1 - (R : ℝ)) + 1) := by congr 1 <;> ring
          _ = (2 : ℝ) ^ (1 - (R : ℝ)) * (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
          _ = (2 : ℝ) ^ (1 - (R : ℝ)) * 2 := by rw [Real.rpow_one]]
    nlinarith [hqerr, hsmall2]
  calc
    (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r ≤
        (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank := hnorm
    _ ≤ alphaCapacity L * G.outsideLinearForestProbability E +
        1 / (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
        1 / (2 : ℝ) ^ (G.restrictedCycleRank E + G.commonBoundaryRank E) := by
      simpa [L, hE] using hcompose
    _ ≤ q * tailCapacity R + (2 : ℝ) ^ (2 - (R : ℝ)) := by
      have hbase : q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) +
          2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) ≤
            q * tailCapacity R + (2 : ℝ) ^ (2 - (R : ℝ)) := by
        calc
          q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) +
              2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) =
            q * tailCapacity R +
              (q * (2 : ℝ) ^ (1 - (R : ℝ)) +
                2 * (2 : ℝ) ^ (1 - (2 * R : ℝ))) := by ring
          _ ≤ q * tailCapacity R + (2 : ℝ) ^ (2 - (R : ℝ)) :=
            add_le_add_left herror _
      have hsum := add_le_add hαprod (add_le_add hout' hin')
      calc
        alphaCapacity L * G.outsideLinearForestProbability E +
            1 / (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
            1 / (2 : ℝ) ^ (G.restrictedCycleRank E + G.commonBoundaryRank E)
            ≤ q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) +
                2 * (2 : ℝ) ^ (1 - (2 * R : ℝ)) := by
              calc
                _ = (alphaCapacity L * G.outsideLinearForestProbability E) +
                    (1 / (2 : ℝ) ^ (G.outsideCycleRank E + G.commonBoundaryRank E) +
                     1 / (2 : ℝ) ^ (G.restrictedCycleRank E + G.commonBoundaryRank E)) := by ring
                _ ≤ q * (tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ))) +
                    ((2 : ℝ) ^ (1 - (2 * R : ℝ)) + (2 : ℝ) ^ (1 - (2 * R : ℝ))) := hsum
                _ = _ := by ring
        _ ≤ q * tailCapacity R + (2 : ℝ) ^ (2 - (R : ℝ)) := hbase

/-- Exact structural output still needed from the §10 complement-loss proof
for a graph in the high-cycle branch. -/
def WitnessBounds (G : PhysicalGraph) (R : ℕ)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) : Prop :=
  let F := Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
    (2 ^ (2 * R) + 1) hcov
  let E := witnessSupportEdges G F
  G.outsideLinearForestProbability E ≤ (1 / 2 : ℝ) + 1 / (R : ℝ) ∧
    2 * R ≤ G.outsideCycleRank E + G.commonBoundaryRank E

/-- The canonical short-cycle support automatically has restricted rank at
least `2R`; the inner pure-side rank condition needs no complement-loss input. -/
theorem canonicalWitnessSupport_restrictedRank_ge
    (G : PhysicalGraph) (R : ℕ)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1)) :
    2 * R ≤ G.restrictedCycleRank
      (witnessSupportEdges G
        (Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
          (2 ^ (2 * R) + 1) hcov)) := by
  let F := Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
    (2 ^ (2 * R) + 1) hcov
  let W := witnessSupportGraph G F
  let E := witnessSupportEdges G F
  have hWrank : W.cycleRank = G.restrictedCycleRank E := by
    dsimp [W, E]
    rw [witnessSupportGraph_eq_restrictPhysical]
    exact G.restrictPhysical_cycleRank _
  have hbound : 2 ^ (2 * R) + 1 ≤ 2 ^ W.cycleRank + 1 := by
    dsimp [W, F]
    exact Erdos1016.Proof.Capacity.canonicalWitnessSupport_rank_bound G
      (2 ^ (2 * R) + 1) hcov
  have hpow : 2 ^ (2 * R) ≤ 2 ^ W.cycleRank := by omega
  have hrank : 2 * R ≤ W.cycleRank :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow
  rw [← hWrank]
  exact hrank

/-- The Section 10 estimate at one fixed quartic scale and for all sufficiently
large `R`. This matches the order of choices in the complement-loss proof:
first choose `C`, then a threshold `Rmin`. -/
def HighCycleBoundsAt (C Rmin : ℕ) : Prop :=
  ∀ (R r : ℕ), Rmin ≤ R → 2 ^ (C * R ^ 4) ≤ r →
    ∀ (G : PhysicalGraph),
    G.cycleRank ≤ r →
    G.InitialCoverage (initialCapacity r) →
    2 ^ (2 * R) + 1 ≤ initialCapacity r →
    (hcovL : G.InitialCoverage (2 ^ (2 * R) + 1)) →
    tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r →
    WitnessBounds G R hcovL

/-- The constants in the complement-loss estimate are absolute but chosen
once for the whole recurrence. -/
def HighCycleBounds : Prop :=
  ∃ C Rmin : ℕ, 8 ≤ C ∧ 5 ≤ Rmin ∧ HighCycleBoundsAt C Rmin

/-- A stronger all-scales estimate still implies the older high-cycle branch
interface. The paper only needs the fixed-scale interface above. -/
def HighCycleBoundsAllScales : Prop :=
  ∀ (C R r : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hr : 2 ^ (C * R ^ 4) ≤ r) (G : PhysicalGraph),
    G.cycleRank ≤ r →
    G.InitialCoverage (initialCapacity r) →
    2 ^ (2 * R) + 1 ≤ initialCapacity r →
    (hcovL : G.InitialCoverage (2 ^ (2 * R) + 1)) →
    tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r →
    WitnessBounds G R hcovL



/-- The exact §10 forest-probability and pure-rank outputs imply the
pointwise quartic step. This uses only the recurrence's coefficient
`1/2+1/R`; the older direct high-cycle estimate demanded the stronger
`tailCapacity/2` coefficient. -/
theorem initialCapacityExcess_le_quartic_step_of_highCycleBounds
    (C R r : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hr : 2 ^ (C * R ^ 4) ≤ r)
    (hSection : ∀ G : PhysicalGraph, G.cycleRank ≤ r →
      G.InitialCoverage (initialCapacity r) →
      2 ^ (2 * R) + 1 ≤ initialCapacity r →
      (hcovL : G.InitialCoverage (2 ^ (2 * R) + 1)) →
      tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r →
      WitnessBounds G R hcovL) :
    initialCapacityExcess r ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
        (2 : ℝ) ^ (2 - (R : ℝ)) := by
  rcases quartic_pointwise_or_large_cycle_branch C R r hC hR hr with hpoint | hlarge
  · exact hpoint
  · obtain ⟨G, hGr, hcov, hlargeCoverage, hlargeCount⟩ := hlarge
    have hlargeL : 2 ^ (2 * R) + 1 ≤ initialCapacity r := by omega
    have hcovL : G.InitialCoverage (2 ^ (2 * R) + 1) := by
      intro ℓ hℓ
      apply hcov
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hℓ).1,
        (Finset.mem_Icc.mp hℓ).2.trans hlargeL⟩
    have hbounds := hSection G hGr hcov hlargeL hcovL hlargeCount
    dsimp [WitnessBounds] at hbounds
    let F := Erdos1016.Proof.Capacity.canonicalCycleWitnesses G
      (2 ^ (2 * R) + 1) hcovL
    let E := witnessSupportEdges G F
    have hinside : 2 * R ≤ G.restrictedCycleRank E + G.commonBoundaryRank E := by
      have hrank := canonicalWitnessSupport_restrictedRank_ge G R hcovL
      dsimp [E, F]
      omega
    have hcount := normalizedCycleCount_le_of_witnessForestBound G R r hR hGr
      hcovL F (Erdos1016.Proof.Capacity.canonicalCycleWitnesses_has_all_lengths
      G (2 ^ (2 * R) + 1) hcovL)
      E rfl hbounds.1 hbounds.2 hinside
    have hcapacity := initialCapacityExcess_le_normalized_cycle_count r G hcov
    exact hcapacity.trans hcount

/-- The structural §10 witness bounds directly close the quartic tail
recurrence once supplied uniformly on its high-cycle branch. -/
theorem tailCapacity_quartic_recurrence_of_highCycleBounds
    (C R : ℕ) (hC : 8 ≤ C) (hR : 5 ≤ R)
    (hSection : ∀ r : ℕ, 2 ^ (C * R ^ 4) ≤ r →
      ∀ G : PhysicalGraph, G.cycleRank ≤ r →
      G.InitialCoverage (initialCapacity r) →
      2 ^ (2 * R) + 1 ≤ initialCapacity r →
      (hcovL : G.InitialCoverage (2 ^ (2 * R) + 1)) →
      tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r →
      WitnessBounds G R hcovL) :
    tailCapacity (2 ^ (C * R ^ 4)) ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
        (2 : ℝ) ^ (2 - (R : ℝ)) := by
  apply tailCapacity_quartic_recurrence_of_pointwise C R
  intro r hr
  exact initialCapacityExcess_le_quartic_step_of_highCycleBounds
    C R r hC hR hr (hSection r hr)

end Erdos1016.Proof.FiniteGreedyStages
end

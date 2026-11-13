import Erdos1016.ExactMaximum.GirthFive
import Erdos1016.ExactMaximum.GirthFive.BasePacking
import Erdos1016.ExactMaximumSupport.Shortening.ChainForestProbability

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Theorem 7.1 of the text at girth five

`girthForestStatement_five : GirthForestStatement 5`. Let `G` be a connected cubic multigraph of
large rank `r`, and let `P` be a set of at most `3 log r` vertices such that `G[P]` is connected.
If `G - P` has no cycle of length less than five, then `q(G,P) < 2/5`.

The proof follows `Shortening/ChainForestProbability.lean`, which has the same statement for
girth at least a constant `D ≥ 256`. That proof deletes maximal families of pairwise disjoint
short cyclic regions at the scales `D, 2 D, 4 D, ...` (`RegionPackingSequence.vertices`), bounds
the deleted sets, and ends with `LargeOrderChain.bound_of_budgets`. The girth of `G - P` is used
in one place: the packing bound for the first family, at the scale `D`.

Here the first family is bounded by `exists_base_finset_packing`, which needs girth five only.
Its bound is a constant `K₀` that is much larger than the bound for girth `D`. The later
families are bounded as before, because the graph outside the deleted set has no short cycle.
So the deleted set after the stage `m` is larger by a constant factor `2^c`. The exponent
`2 · 2^m D + 6 (log (2^m D))²` of the size bound has room for `c` if `m ≥ c`
(`shifted_size_bound`). The sequence of the stages `c, c + 1, ...` is therefore a
`HighGirthPackingSequence` at the base scale `2^c D`, and the last part of the proof is the
same.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open FiniteMultiGraph Erdos1016.ExactMaximumSupport.LargeGirth
open Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
open Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
open Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds
open Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence
open Erdos1016.ExactMaximumSupport.Shortening

local instance forestProbabilityDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem scale_scale (D a b : ℕ) : scale (scale D a) b = scale D (a + b) := by
  simp only [scale, pow_add]
  ring

/-- **The size bound with a larger first step.** If the first deleted set has fewer than `2^c`
vertices and the later steps satisfy the recurrence of the packing bound, then the size bound
of the dyadic construction holds from the stage `c`. -/
theorem shifted_size_bound (D c : ℕ) (hD : 256 ≤ D) (S : ℕ → ℕ) (hzero : S 0 = 0)
    (hfirst : S 1 + 1 ≤ 2 ^ c)
    (hstep : ∀ j, 1 ≤ j → S (j + 1) + 1 ≤
      151 * (scale D j) ^ 4 * 2 ^ scale D j * (S j + 1))
    (m : ℕ) (hm : c ≤ m) :
    S (m + 1) + 1 ≤ 2 ^ (2 * scale D m + 6 * (Nat.clog 2 (scale D m)) ^ 2) := by
  have hrec := recurrence_le_pow_sum S
    (fun i => scale D i + 4 * Nat.clog 2 (scale D i) + 8 + c) hzero ?_ (m + 1)
  · refine hrec.trans (Nat.pow_le_pow_right (by decide) ?_)
    let L := Nat.clog 2 (scale D m)
    have hL : m + 5 ≤ L := by
      have hp : 0 < 2 ^ m := by positivity
      have hs : 2 ^ (m + 4) < scale D m := by
        dsimp [scale]
        rw [pow_add]
        nlinarith
      have h := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hs
      omega
    have hsum : (∑ i ∈ Finset.range (m + 1),
        (scale D i + 4 * Nat.clog 2 (scale D i) + 8 + c)) ≤
        (∑ i ∈ Finset.range (m + 1), scale D i) + (m + 1) * (4 * L + 8 + c) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (m + 1), (scale D i + (4 * L + 8 + c)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hij : i ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
          have hc := Nat.clog_mono_right 2 (scale_mono D hij)
          dsimp [L]
          omega
        _ = _ := by simp [Finset.sum_add_distrib]
    have hsmall : (m + 1) * (4 * L + 8 + c) ≤ 6 * L ^ 2 := by
      have h1 := Nat.mul_le_mul_right (4 * L + 8 + c) (show m + 1 ≤ L by omega)
      have h2 := Nat.mul_le_mul_left L (show 8 + c ≤ 2 * L by omega)
      nlinarith
    exact hsum.trans (Nat.add_le_add (sum_scale_le D m) hsmall)
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hzero]
      calc
        S (0 + 1) + 1 ≤ 2 ^ c := hfirst
        _ ≤ 2 ^ (scale D 0 + 4 * Nat.clog 2 (scale D 0) + 8 + c) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ (scale D 0 + 4 * Nat.clog 2 (scale D 0) + 8 + c) * (0 + 1) := by
          rw [zero_add, mul_one]
    · calc
        S (j + 1) + 1 ≤ 151 * (scale D j) ^ 4 * 2 ^ scale D j * (S j + 1) := hstep j hj
        _ ≤ 2 ^ (scale D j + 4 * Nat.clog 2 (scale D j) + 8) * (S j + 1) :=
          Nat.mul_le_mul_right _ (ChainGirthRaiseBounds.packing_multiplier_le _)
        _ ≤ 2 ^ (scale D j + 4 * Nat.clog 2 (scale D j) + 8 + c) * (S j + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

end Erdos1016.ExactMaximum.GirthFive

namespace Erdos1016.ExactMaximum

open FiniteMultiGraph Erdos1016.ExactMaximumSupport.LargeGirth
open Erdos1016.ExactMaximumSupport.LargeGirth.ParameterBudget
open Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
open Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds
open Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence
open Erdos1016.ExactMaximumSupport.Shortening
open GirthFive

local instance girthFiveForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Theorem 7.1 of the text.** For a connected cubic multigraph `G` of large rank `r` and a
set `P` of at most `3 log r` vertices such that `G[P]` is connected: if `G - P` has no cycle of
length less than five, then `q(G,P) < 2/5`. -/
theorem girthForestStatement_five : GirthForestStatement 5 := by
  obtain ⟨D, hD, hpack⟩ := ChainPacking.exists_finset_cutoff
  obtain ⟨q, hbase⟩ := exists_base_finset_packing D (by omega)
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, K₀ = (3 * (D * ((D + 0 + 2) * q)) + 6 * D) * 2 ^ D :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = K₀ * D + 1 := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ℕ, D' = scale D c := ⟨_, rfl⟩
  have hD'pos : 0 < D' := by
    rw [hD']
    dsimp [scale]
    have hp : 0 < 2 ^ c := by positivity
    nlinarith
  obtain ⟨R, hR⟩ := exists_rank_threshold D' hD'pos LargeOrderChain.constant
    LargeOrderChain.constant_pos.le
  refine ⟨max R 1, ?_⟩
  intro G P hG hcubic hr hP hPsize hshort
  by_contra hnot
  have hprob : (2 / 5 : ℝ) ≤ G.regionForestProbability Pᶜ := le_of_not_gt hnot
  have hmax (v : G.Vertex) : G.degree v ≤ 3 := (hcubic v).le
  have hPne : P.Nonempty := by
    obtain ⟨v⟩ := hP.nonempty
    exact ⟨v.1, v.2⟩
  have hscale2 : ∀ n, 2 ≤ scale D n := by
    intro n
    have hp := Nat.one_le_two_pow (n := n)
    dsimp [scale]
    nlinarith
  -- the first family, at girth five
  have hfirst : (vertices G P (scale D) 1).card + 1 ≤ 2 ^ c := by
    have h0 : scale D 0 = D := by simp [scale]
    have hs := selected_spec G (P ∪ ∅) D
    have hsel : (selected G (P ∪ ∅) D).card ≤ K₀ := by
      have hb := hbase G P ∅ (selected G (P ∪ ∅) D) hG hcubic hP hPne
        (by simpa only [Finset.union_empty] using hshort)
        (by simpa only [Finset.union_empty] using hprob)
        hs.2.1 (fun U hU => (hs.1 U hU).connected) (fun U hU => (hs.1 U hU).outside)
        (fun U hU => (hs.1 U hU).cyclic) (fun U hU => (hs.1 U hU).cut)
      rw [Finset.card_empty] at hb
      rw [hK₀]
      exact hb
    have hcard := vertices_step_card G P (scale D) 0
    rw [vertices_zero, Finset.card_empty, zero_add, h0] at hcard
    have hmul := Nat.mul_le_mul_right D hsel
    have hlt : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  -- the later families, as for large girth
  have hstep : ∀ n, 1 ≤ n → (vertices G P (scale D) (n + 1)).card + 1 ≤
      151 * (scale D n) ^ 4 * 2 ^ scale D n * ((vertices G P (scale D) n).card + 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply ChainGirthRaiseBounds.vertices_step_bound G P (scale D) (m + 1)
      (by have := hscale2 (m + 1); omega)
    have hs := selected_spec G (P ∪ vertices G P (scale D) (m + 1)) (scale D (m + 1))
    exact hpack G P (vertices G P (scale D) (m + 1)) (incomingScale D (m + 1))
      (scale D (m + 1))
      (selected G (P ∪ vertices G P (scale D) (m + 1)) (scale D (m + 1))) hG hcubic
      (incomingScale_ge D (m + 1)) (hscale2 (m + 1))
      (scale_le_twice_incoming D (m + 1)) hP hPne
      (vertices_no_short G P (scale D) m (hscale2 m) hmax)
      (stage_probability_lower G P D (m + 1) (2 / 5) hprob)
      hs.2.1 (fun U hU => (hs.1 U hU).connected) (fun U hU => (hs.1 U hU).outside)
      (fun U hU => (hs.1 U hU).cyclic) (fun U hU => (hs.1 U hU).cut)
  have hsizes : ∀ m, c ≤ m → (vertices G P (scale D) (m + 1)).card + 1 ≤
      2 ^ (2 * scale D m + 6 * (Nat.clog 2 (scale D m)) ^ 2) :=
    fun m hm => shifted_size_bound D c hD (fun n => (vertices G P (scale D) n).card)
      (by simp) hfirst hstep m hm
  -- the sequence from the stage `c`
  have hDD : ∀ j, scale D' j = scale D (c + j) := by
    intro j
    rw [hD']
    exact scale_scale D c j
  let seq : HighGirthPackingSequence G P D' := {
    family := fun j => families G P (scale D) (c + j + 1)
    region := fun j => vertices G P (scale D) (c + j + 1)
    region_eq := fun _ => rfl
    nested := fun i j hij => vertices_mono G P (scale D) (by omega)
    outside := fun j => vertices_outside G P (scale D) (scale_mono D) (c + j + 1)
    spec := fun j => by
      rw [hDD j]
      exact families_spec G P (scale D) (scale_mono D) (c + j)
    disjoint := fun j => families_disjoint G P (scale D) (c + j + 1)
    hits := fun j => by
      rw [hDD j]
      exact RegionPackingSequence.hits G P (scale D) (c + j)
    no_short := fun j => by
      rw [hDD j]
      exact vertices_no_short G P (scale D) (c + j) (hscale2 _) hmax
    size := fun j => by
      rw [hDD j]
      exact hsizes (c + j) (by omega) }
  -- the last part of the proof for large girth
  let r := G.cycleRank
  let x : ℝ := Real.logb 2 (r : ℝ)
  let i := scaleIndex D' (Real.sqrt x)
  let j := scaleIndex D' (x / 16)
  let lo := scale D' i
  let hi := scale D' j
  let S := seq.region i
  let T := seq.region j
  let Q := seq.family j
  let V := (P ∪ T)ᶜ
  have hPT : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvT
    exact (Finset.mem_compl.mp (seq.outside j hvT)) hvP
  have hdel : (P ∪ T).card = P.card + T.card := Finset.card_union_of_disjoint hPT
  have horder : G.vertexCount + 2 = 2 * r := by
    have hh := G.order_add_two_eq_twice_rank_add_marked_deficit ∅ hG
      (fun v => (hcubic v).le) (fun v _ => hcubic v)
    simpa only [Finset.sum_empty, add_zero] using hh
  have hledger : V.card + P.card + T.card + 2 = 2 * r := by
    have hh := Finset.card_add_card_compl (P ∪ T)
    simp only [Fintype.card_fin, hdel] at hh
    change P.card + T.card + V.card = G.vertexCount at hh
    omega
  have hpow : (2 : ℝ) ^ x = (r : ℝ) :=
    Real.rpow_logb (by norm_num) (by norm_num)
      (by exact_mod_cast (show 0 < r by dsimp [r]; omega))
  have hledgerR : (V.card : ℝ) + P.card + T.card + 2 = 2 * (2 : ℝ) ^ x := by
    rw [hpow]
    exact_mod_cast hledger
  have hb : FiniteBudgets LargeOrderChain.constant x hi lo V.card
      (P.card + T.card) S.card :=
    hR r (by dsimp [r]; omega) P.card T.card S.card V.card hPsize (seq.size j) (seq.size i)
      hledgerR
  have hQregion : Q.biUnion id = T := (seq.region_eq j).symm
  have hcontr := LargeOrderChain.bound_of_budgets G P S Q hi (parallelDepth x)
    (traceStart x) (halfCutoff x) (hi / 2) (blockSpan x) (lo + 1) hG hcubic hP
    (seq.spec j) (by
      intro U hU
      rw [hQregion]
      exact seq.hits j U hU)
    hb.large_girth hb.cutoff_ge hb.depth_pos hb.link_geometry hprob
    hb.trace_pos hb.trace_interval hb.cutoff_pos hb.radius_pos hb.radius_girth
    (by simpa only [hQregion] using hb.order_pos)
    (by simpa only [hQregion, hdel] using hb.deficit_lt)
    (by simpa only [hQregion, hdel] using hb.trace_main)
    (by simpa only [hQregion] using hb.trace_error)
    hb.collision hb.trace_log hb.joined_load hb.link_load hb.clean_chain hb.block_width
    hb.small_girth (by simpa only [Nat.cast_add, Nat.cast_one] using hb.small_log)
    (seq.no_short i)
  exact not_lt_of_ge hprob hcontr.2

end Erdos1016.ExactMaximum

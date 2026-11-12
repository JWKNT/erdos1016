import Erdos1016.ExactMaximum.FourCutSides
import Erdos1016.ExactMaximum.FourCutStructure
import Erdos1016.ExactMaximum.NetCutFour
import Erdos1016.ExactMaximum.HorakKim
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.Cases

set_option autoImplicit false

/-!
# A cyclic cut of size four

This file proves Theorem 6.8 of the paper "The maximum number of cycles in a graph of large
rank" (Case 3 of the proof of Theorem 1.1) from five statements:

* `GapStatement` (Theorem 5.10) and `RingCaseStatement` (the rings), stated in `FullPairs.lean`;
* `FourCutArithmeticStatement` (Lemmas 6.5 and 6.6 and the four cases, as arithmetic), stated in
  `FourCutArithmetic.lean`;
* `FewCyclesStatement` (Theorem 5.4 for `ε = 1/1000`) and `PoleCycleBoundStatement`
  (Corollary 3.11 for poles), which are proved in other files.

The theorem is `fourCutStatement_of_parts`. The steps are:

1. the structure of the cut (`exists_isFourCut`): two poles `X`, `Y` with four ports;
2. the count `c(G) = c(X) + c(Y) + 2^(h+k) 𝓑` (`numCycles_of_four_crossing`), as an equation of
   real numbers (`four_cut_count`);
3. the hypotheses of the arithmetic statement for the numbers of `X` and `Y`
   (`fourState_of_pole`, `largeState_of_pole`, and the side of rank one);
4. the conclusion: fewer than `2^(r-1) ≤ H(r)` cycles, or the hypotheses of the ring case.

Only one side must be large. So `numCycles_le_of_four_cut_inside` takes the first side as the
large side `Y`, and `numCycles_le_of_four_cut` applies it to the cut or to its complement.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance fourCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The ring case for networks of rank at least `R`: the statement inside `RingCaseStatement`. -/
def RingCaseWith (R : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.graph.Connected →
    N.IsCubic → (∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) → R ≤ networkRank N →
    ∀ (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V),
      (∀ g, N.crosses S g → ∃ i, g = e i) → (∀ i, N.Joins (e i) (x i) (y i)) →
      (∀ i, S (x i)) → (∀ i, ¬ S (y i)) → Function.Injective x → Function.Injective y →
      (N.sub (N.inside S)).IsWeakPole → (N.sub (N.outside S)).IsWeakPole →
      (∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
        (N.sub (N.inside S)).IsFullPair (x i) (x j) ∧
          (N.sub (N.outside S)).IsFullPair (y i) (y j)) →
      N.numCycles ≤ horakKim (networkRank N)

theorem ringCaseStatement_iff : RingCaseStatement ↔ ∃ R, RingCaseWith R := Iff.rfl

/-! ### The count as an equation of real numbers -/

/-- **Equation (6.2) of the paper.** Let `c` be the number of cycles of a graph that consists of
the poles `X` and `Y` and four edges between their ports. Then `c / 2^(h+k)` is the sum of
`c(X) / 2^(h+k)`, `c(Y) / 2^(h+k)`, the sum of the products of the path shares, and the sum of
the products of the pair shares for different pairings. -/
theorem four_cut_count {V E₁ E₂ : Type} [Fintype V] [Fintype E₁] [Fintype E₂]
    (MX : Network V E₁) (MY : Network V E₂) (x y : Fin 4 → V) (c : ℕ)
    (hc : c = MY.numCycles + MX.numCycles +
      (MY.numPaths (x 0) (x 1) * MX.numPaths (y 0) (y 1) +
        MY.numPaths (x 0) (x 2) * MX.numPaths (y 0) (y 2) +
        MY.numPaths (x 0) (x 3) * MX.numPaths (y 0) (y 3) +
        MY.numPaths (x 1) (x 2) * MX.numPaths (y 1) (y 2) +
        MY.numPaths (x 1) (x 3) * MX.numPaths (y 1) (y 3) +
        MY.numPaths (x 2) (x 3) * MX.numPaths (y 2) (y 3)) +
      (pairCount MY x 0 * (pairCount MX y 1 + pairCount MX y 2) +
        pairCount MY x 1 * (pairCount MX y 0 + pairCount MX y 2) +
        pairCount MY x 2 * (pairCount MX y 0 + pairCount MX y 1))) :
    (c : ℝ) = ((MX.numCycles : ℝ) / 2 ^ networkRank MX / 2 ^ networkRank MY +
      (MY.numCycles : ℝ) / 2 ^ networkRank MY / 2 ^ networkRank MX +
      (pairSum (pathShare MX y) (pathShare MY x) +
        pairingSum (pairShare MX y) (pairShare MY x))) *
      (2 ^ networkRank MX * 2 ^ networkRank MY) := by
  have hX : (2 : ℝ) ^ networkRank MX ≠ 0 := by positivity
  have hY : (2 : ℝ) ^ networkRank MY ≠ 0 := by positivity
  rw [hc]
  unfold pairSum pairingSum pathShare pairShare
  push_cast
  field_simp
  ring

/-! ### A side of rank one -/

/-- **A side of rank one has even degrees.** In a cubic network, let the cut `S` have four
crossing edges, and let `x 0, …, x 3` be four different vertices of `S` that are ports of the
first side. If the first side has rank one, then every vertex has even degree in it. -/
theorem boundary_ones_eq_zero_of_rank_one {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop) (hS : N.cutSize S = 4)
    (x : Fin 4 → V) (hx : ∀ i, S (x i)) (hinj : Function.Injective x)
    (hport : ∀ i, (N.sub (N.inside S)).IsPort (x i))
    (h1 : networkRank (N.sub (N.inside S)) = 1) :
    (N.sub (N.inside S)).boundary (fun _ => 1) = 0 := by
  funext v
  rw [boundary_eq_deg]
  by_cases hv : S v
  · obtain ⟨i, rfl⟩ := N.exists_eq_of_rank_one hcubic S hS x hx hinj h1 v hv
    have h2 : (N.sub (N.inside S)).deg (fun _ => 1) (x i) = 2 := hport i
    rw [h2]
    exact ZMod.natCast_self 2
  · rw [N.deg_inside_of_not_mem S hv]
    exact Nat.cast_zero

/-! ### The large side is the first side -/

/-- **Theorem 6.8 of the paper, when the first side of the cut is large.** Let `N` be a connected
cubic network in which every cyclic cut has at least four crossing edges, and let `S` be a cyclic
cut with four crossing edges whose first side has large rank. Then `N` has at most `H(r)`
cycles. -/
theorem numCycles_le_of_four_cut_inside (hgap : GapStatement)
    (harith : FourCutArithmeticStatement) {K B R : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K)
    (hG : PoleCycleBoundWith B) (hring : RingCaseWith R) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 4) (hcyc : N.IsCyclicCut S) (hR : R ≤ networkRank N)
    (hk : max B (4000000 * K) ≤ networkRank (N.sub (N.inside S))) :
    N.numCycles ≤ horakKim (networkRank N) := by
  obtain ⟨e, x, y, hfc⟩ := N.exists_isFourCut hN hcubic hmin S hS hcyc
  obtain ⟨n01, n02, n03, n12, n13, n23⟩ := fin4_distinct
  have hS' : N.cutSize (fun v => ¬ S v) = 4 := by
    rw [N.cutSize_not S]
    exact hS
  -- the ranks
  have hkpow : 4000000 * K ≤ 2 ^ networkRank (N.sub (N.inside S)) :=
    le_trans (le_trans (le_max_right _ _) hk) Nat.lt_two_pow_self.le
  have hB : B ≤ networkRank (N.sub (N.inside S)) := le_trans (le_max_left _ _) hk
  have hXpos : 1 ≤ networkRank (N.sub (N.outside S)) := by
    have h1 := (N.sub (N.outside S)).numCycles_lt_two_pow
    have h2 := hcyc.2
    refine Nat.le_of_not_lt fun h0 => ?_
    have h3 : networkRank (N.sub (N.outside S)) = 0 := by omega
    rw [h3, pow_zero] at h1
    omega
  -- the numbers of the two sides
  have hX := fourState_of_pole hgap (N.sub (N.outside S)) hfc.pole_out y hfc.inj_y hfc.port_out
  have hY := largeState_of_pole hgap hF (N.sub (N.inside S)) hfc.pole_in x hfc.inj_x
    hfc.port_in hkpow
  have hDX : (0 : ℝ) < 2 ^ networkRank (N.sub (N.outside S)) := by positivity
  have hDY : (0 : ℝ) < 2 ^ networkRank (N.sub (N.inside S)) := by positivity
  have h2X : (2 : ℝ) ≤ 2 ^ networkRank (N.sub (N.outside S)) := by
    have h : 2 ≤ 2 ^ networkRank (N.sub (N.outside S)) := Nat.le_self_pow (by omega) 2
    exact_mod_cast h
  have h1000 : (1000 : ℝ) ≤ 2 ^ networkRank (N.sub (N.inside S)) := by
    have h : 1000 ≤ 2 ^ networkRank (N.sub (N.inside S)) := by omega
    exact_mod_cast h
  -- a side of rank one
  have hrank1 : (2 : ℝ) ^ networkRank (N.sub (N.outside S)) < 4 →
      ∀ α, pairShare (N.sub (N.outside S)) y α ≤ 1 / 2 := by
    intro hlt α
    have h1 : networkRank (N.sub (N.outside S)) = 1 := by
      refine Classical.not_not.1 fun hne => ?_
      have h2 : 2 ≤ networkRank (N.sub (N.outside S)) := by omega
      have h3 : 2 ^ 2 ≤ 2 ^ networkRank (N.sub (N.outside S)) :=
        Nat.pow_le_pow_right (by norm_num) h2
      have h4 : (4 : ℝ) ≤ 2 ^ networkRank (N.sub (N.outside S)) := by exact_mod_cast h3
      linarith
    have heven : (N.sub (N.outside S)).boundary (fun _ => 1) = 0 :=
      boundary_ones_eq_zero_of_rank_one N hcubic (fun v => ¬ S v) hS' y hfc.not_mem hfc.inj_y
        hfc.port_out h1
    exact pairShare_le_half_of_rank_one _ y heven h1 α
  -- the cycles of the sides
  have hcX0 : (0 : ℝ) ≤ ((N.sub (N.outside S)).numCycles : ℝ) /
      2 ^ networkRank (N.sub (N.outside S)) := div_nonneg (Nat.cast_nonneg _) hDX.le
  have hcX1 : ((N.sub (N.outside S)).numCycles : ℝ) /
      2 ^ networkRank (N.sub (N.outside S)) < 1 := by
    rw [div_lt_one hDX]
    exact_mod_cast (N.sub (N.outside S)).numCycles_lt_two_pow
  have hcY0 : (0 : ℝ) ≤ ((N.sub (N.inside S)).numCycles : ℝ) /
      2 ^ networkRank (N.sub (N.inside S)) := div_nonneg (Nat.cast_nonneg _) hDY.le
  have hcY1 : ((N.sub (N.inside S)).numCycles : ℝ) /
      2 ^ networkRank (N.sub (N.inside S)) ≤ 9 / 16 := by
    rw [div_le_iff₀ hDY]
    have h := hG _ _ (N.sub (N.inside S)) hfc.pole_in hB
    have h' : (16 : ℝ) * ((N.sub (N.inside S)).numCycles : ℝ) ≤
        9 * 2 ^ networkRank (N.sub (N.inside S)) := by exact_mod_cast h
    linarith
  have hcY2 : (∃ i j, i ≠ j ∧ 501 / 1000 ≤ pathShare (N.sub (N.inside S)) x i j) →
      ((N.sub (N.inside S)).numCycles : ℝ) / 2 ^ networkRank (N.sub (N.inside S)) ≤
        1 / 1000 := by
    rintro ⟨i, j, hij, hshare⟩
    have hmany : 501 * 2 ^ networkRank (N.sub (N.inside S)) ≤
        1000 * (N.sub (N.inside S)).numPaths (x i) (x j) := by
      unfold pathShare at hshare
      rw [le_div_iff₀ hDY] at hshare
      have h' : (501 : ℝ) * 2 ^ networkRank (N.sub (N.inside S)) ≤
          1000 * ((N.sub (N.inside S)).numPaths (x i) (x j) : ℝ) := by linarith
      exact_mod_cast h'
    have h1 := hF _ _ (N.sub (N.inside S)) hfc.pole_in (x i) (x j) (hfc.port_in i)
      (hfc.port_in j) (fun h => hij (hfc.inj_x h)) hmany
    have h2 : (N.sub (N.inside S)).numCycles ^ 2 ≤
        2 * K * 2 ^ networkRank (N.sub (N.inside S)) := by
      have e2 : 2 * K * 2 ^ networkRank (N.sub (N.inside S)) =
          K * 2 ^ networkRank (N.sub (N.inside S)) +
            K * 2 ^ networkRank (N.sub (N.inside S)) := by ring
      omega
    have h3 := thousand_mul_le h2 (by omega)
    rw [div_le_iff₀ hDY]
    have h4 : (1000 : ℝ) * ((N.sub (N.inside S)).numCycles : ℝ) ≤
        2 ^ networkRank (N.sub (N.inside S)) := by exact_mod_cast h3
    linarith
  -- the arithmetic
  rcases harith (pathShare (N.sub (N.outside S)) y) (pathShare (N.sub (N.inside S)) x)
      (pairShare (N.sub (N.outside S)) y) (pairShare (N.sub (N.inside S)) x)
      (((N.sub (N.outside S)).numCycles : ℝ) / 2 ^ networkRank (N.sub (N.outside S)))
      (((N.sub (N.inside S)).numCycles : ℝ) / 2 ^ networkRank (N.sub (N.inside S)))
      (2 ^ networkRank (N.sub (N.outside S))) (2 ^ networkRank (N.sub (N.inside S)))
      hX hY h2X h1000 hrank1 hcX0 hcX1 hcY0 hcY1 hcY2 with
    hlt | ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hx1, hx2, hx3, hx4, ha1, ha2, ha3, ha4⟩
  · -- fewer than `2^(r-1)` cycles
    have hC' : ∀ g, N.crosses S g → g = e 0 ∨ g = e 1 ∨ g = e 2 ∨ g = e 3 := by
      intro g hg
      obtain ⟨m, rfl⟩ := hfc.crosses g hg
      fin_cases m
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    have hcount := N.numCycles_of_four_crossing S hC' (hfc.joins 0) (hfc.joins 1) (hfc.joins 2)
      (hfc.joins 3) (hfc.mem 0) (hfc.mem 1) (hfc.mem 2) (hfc.mem 3) (hfc.not_mem 0)
      (hfc.not_mem 1) (hfc.not_mem 2) (hfc.not_mem 3) (hfc.inj_x.ne n01) (hfc.inj_x.ne n02)
      (hfc.inj_x.ne n03) (hfc.inj_x.ne n12) (hfc.inj_x.ne n13) (hfc.inj_x.ne n23)
      (hfc.inj_y.ne n01) (hfc.inj_y.ne n02) (hfc.inj_y.ne n03) (hfc.inj_y.ne n12)
      (hfc.inj_y.ne n13) (hfc.inj_y.ne n23)
    have hreal := four_cut_count (N.sub (N.outside S)) (N.sub (N.inside S)) x y N.numCycles
      hcount
    have hlt' : (N.numCycles : ℝ) < 4 * (2 ^ networkRank (N.sub (N.outside S)) *
        2 ^ networkRank (N.sub (N.inside S))) := by
      rw [hreal]
      exact mul_lt_mul_of_pos_right hlt (mul_pos hDX hDY)
    have hnat : N.numCycles < 4 * (2 ^ networkRank (N.sub (N.outside S)) *
        2 ^ networkRank (N.sub (N.inside S))) := by exact_mod_cast hlt'
    have hr := hfc.rank
    have hpow : 4 * (2 ^ networkRank (N.sub (N.outside S)) *
        2 ^ networkRank (N.sub (N.inside S))) = 2 ^ (networkRank N - 1) := by
      have h1 : networkRank N - 1 = 2 + (networkRank (N.sub (N.outside S)) +
          networkRank (N.sub (N.inside S))) := by omega
      rw [h1, pow_add, pow_add]
      norm_num
    have h3 : 3 ≤ networkRank N := by omega
    have h4 := two_pow_le_horakKim (networkRank N) h3
    omega
  · -- the ring case
    have hσ := renumber_injective i j k l hij hik hil hjk hjl hkl
    refine hring V E N hN hcubic hmin hR S (e ∘ renumber i j k l) (x ∘ renumber i j k l)
      (y ∘ renumber i j k l) ?_ (fun m => hfc.joins _) (fun m => hfc.mem _)
      (fun m => hfc.not_mem _) (hfc.inj_x.comp hσ) (hfc.inj_y.comp hσ) hfc.pole_in hfc.pole_out
      ?_
    · intro g hg
      obtain ⟨m₀, hm₀⟩ := hfc.crosses g hg
      obtain ⟨n, rfl⟩ := renumber_surjective i j k l hij hik hil hjk hjl hkl m₀
      exact ⟨n, hm₀⟩
    · intro m n hm hn
      show (N.sub (N.inside S)).IsFullPair (x (renumber i j k l m)) (x (renumber i j k l n)) ∧
        (N.sub (N.outside S)).IsFullPair (y (renumber i j k l m)) (y (renumber i j k l n))
      rcases renumber_low i j k l m hm with h1 | h1 <;>
        rcases renumber_high i j k l n hn with h2 | h2 <;> rw [h1, h2]
      · exact ⟨isFullPair_of_pathShare_eq_one _ x ha1, isFullPair_of_pathShare_eq_one _ y hx1⟩
      · exact ⟨isFullPair_of_pathShare_eq_one _ x ha2, isFullPair_of_pathShare_eq_one _ y hx2⟩
      · exact ⟨isFullPair_of_pathShare_eq_one _ x ha3, isFullPair_of_pathShare_eq_one _ y hx3⟩
      · exact ⟨isFullPair_of_pathShare_eq_one _ x ha4, isFullPair_of_pathShare_eq_one _ y hx4⟩

/-! ### Theorem 6.8 for networks -/

/-- **Theorem 6.8 of the paper for networks.** Let `N` be a connected cubic network of large
rank `r` in which every cyclic cut has at least four crossing edges, and let `N` have a cyclic
cut with four crossing edges. Then `N` has at most `H(r)` cycles. -/
theorem numCycles_le_of_four_cut (hgap : GapStatement) (harith : FourCutArithmeticStatement)
    {K B R : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K) (hG : PoleCycleBoundWith B)
    (hring : RingCaseWith R) {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 4) (hcyc : N.IsCyclicCut S)
    (hR : max R (2 * max B (4000000 * K) + 3) ≤ networkRank N) :
    N.numCycles ≤ horakKim (networkRank N) := by
  obtain ⟨e, x, y, hfc⟩ := N.exists_isFourCut hN hcubic hmin S hS hcyc
  have hr := hfc.rank
  have hR1 : R ≤ networkRank N := le_trans (le_max_left _ _) hR
  have hR2 : 2 * max B (4000000 * K) + 3 ≤ networkRank N := le_trans (le_max_right _ _) hR
  by_cases hk : max B (4000000 * K) ≤ networkRank (N.sub (N.inside S))
  · exact numCycles_le_of_four_cut_inside hgap harith hK hF hG hring N hN hcubic hmin S hS hcyc
      hR1 hk
  · have hk' : max B (4000000 * K) ≤ networkRank (N.sub (N.outside S)) := by
      generalize max B (4000000 * K) = m at hk hR2
      omega
    have hS' : N.cutSize (fun v => ¬ S v) = 4 := by
      rw [N.cutSize_not S]
      exact hS
    exact numCycles_le_of_four_cut_inside hgap harith hK hF hG hring N hN hcubic hmin
      (fun v => ¬ S v) hS' hcyc.not hR1 hk'

/-! ### Theorem 6.8 for multigraphs -/

/-- **Theorem 6.8 of the paper with Corollary 6.2 (Case 3 of the proof of Theorem 1.1)**, from
the gap theorem, the ring case, the arithmetic of the four cases, Theorem 5.4 for `ε = 1/1000`
and Corollary 3.11 for poles. A connected cubic multigraph of large rank `r`, without a loop,
with a cyclic cut of size four and without a cyclic cut of smaller size, has at most `H(r)`
cycles. -/
theorem fourCutStatement_of_parts (hgap : GapStatement) (hring : RingCaseStatement)
    (harith : FourCutArithmeticStatement) (hF : FewCyclesStatement)
    (hG : PoleCycleBoundStatement) : FourCutStatement := by
  obtain ⟨K, hK, hF⟩ := hF
  obtain ⟨B, hG⟩ := hG
  obtain ⟨R, hring⟩ := ringCaseStatement_iff.1 hring
  refine ⟨max R (2 * max B (4000000 * K) + 3), ?_⟩
  rintro M hconn hcubic hloop hR hno3 ⟨U, hU, hcard⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  -- the cut edges of a vertex set are the crossing edges
  have hcutcard : ∀ W : Finset M.Vertex,
      (M.cutEdges W).card = M.looplessNetwork.cutSize (fun v => v ∈ W) := by
    intro W
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges W} = (M.cutEdges W).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ W) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} := rfl
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} →
        {e : M.Edge // e ∈ M.cutEdges W}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses W e.1).2 e.2⟩, fun _ => rfl⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
        exact Subtype.ext (Subtype.ext h1)
      · intro b
        refine ⟨⟨⟨b.1, hl b.1⟩, (M.mem_cutEdges_iff_crosses W ⟨b.1, hl b.1⟩).1 b.2⟩, ?_⟩
        apply Subtype.ext
        rw [hf]
    have h1 := Nat.card_eq_of_bijective f hbij
    omega
  -- every cyclic cut of the network has at least four crossing edges
  have hmin : ∀ S : M.Vertex → Prop, M.looplessNetwork.IsCyclicCut S →
      4 ≤ M.looplessNetwork.cutSize S := by
    intro S hS
    obtain ⟨W, hW⟩ : ∃ W : Finset M.Vertex, (fun v => v ∈ W) = S :=
      ⟨Finset.univ.filter S, funext fun v => propext (by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩)⟩
    subst hW
    refine Nat.le_of_not_lt fun hlt => ?_
    apply hno3
    refine ⟨W, ⟨?_, ?_⟩, ?_⟩
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl W).2 ⟨z, hz, hw⟩
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl Wᶜ).2 ⟨z, hz, fun g hg =>
        ⟨Finset.mem_compl.2 (hw g hg).1, Finset.mem_compl.2 (hw g hg).2⟩⟩
    · rw [hcutcard W]
      omega
  -- the given cut
  have hcyc : M.looplessNetwork.IsCyclicCut (fun v => v ∈ U) := by
    constructor
    · obtain ⟨z, hz, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl U).1 hU.1
      exact numCycles_sub_pos _ _ hz hw
    · obtain ⟨z, hz, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl Uᶜ).1 hU.2
      exact numCycles_sub_pos _ _ hz
        (fun g hg => ⟨Finset.mem_compl.1 (hw g hg).1, Finset.mem_compl.1 (hw g hg).2⟩)
  have hsize : M.looplessNetwork.cutSize (fun v => v ∈ U) = 4 := by
    have h1 := hmin _ hcyc
    have h2 := hcutcard U
    omega
  have h := numCycles_le_of_four_cut hgap harith hK hF hG hring M.looplessNetwork hN hcub hmin
    (fun v => v ∈ U) hsize hcyc (by rw [← M.cycleRank_eq_networkRank hl]; exact hR)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h

end Erdos1016.ExactMaximum

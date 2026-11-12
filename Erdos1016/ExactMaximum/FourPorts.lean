import Erdos1016.ExactMaximum.PoleSides
import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.Gadgets
import Erdos1016.ExactMaximum.ThreeCut
import Erdos1016.ExactMaximum.CountTools
import Erdos1016.ExactMaximum.NetPairs

set_option autoImplicit false

/-!
# Pairs of disjoint paths between four vertices

This file proves the facts about pairs of disjoint paths that the case of a cyclic cut of size
four uses (Section 6.2 of the paper "The maximum number of cycles in a graph of large rank").

* `numPathPairs_add_le`: `F ≤ 1`. In a network of rank `b`, the pairs of disjoint paths between
  four vertices, for the three pairings together, are at most `2^b`.
* `IsFullPair.isPathWord_of_boundary`: if the pair `s`, `t` is full, then every word with odd
  degree exactly at `s` and `t` is a path (Lemma 5.1, one direction).
* `IsFullPair.exists_cycle_at`: a port of a full pair lies on a cycle.
* `two_mul_numPathPairs_le_of_full`: Lemma 6.7. If the pairs `a`, `j` and `a`, `k` are full, then
  at most `2^(b-1)` pairs of disjoint paths join `a` to `j` and `k` to `l`.
* `numPathPairs_le_one_of_rank_one`: in a network of rank one in which every vertex has even
  degree, at most one pair of disjoint paths joins `a` to `b` and `c` to `d`.

The proof of Lemma 6.7 is shorter than the proof in the paper. A pair of disjoint paths `Q`, `Q'`
is determined by `Q`, because `Q + Q'₁ + Q'₂` is a path for two such pairs. The path `Q` does not
use an edge `g` at `k`. Some cycle `Z` uses `g`: if not, then `g` is a bridge, and the pair `a`,
`k` is not full (`two_mul_numPaths_le_of_same_side`, `two_mul_numPaths_le_of_bridge_at`). The map
`Q ↦ Q + Z` takes the words that avoid `g` to the words that use `g`, so the words that avoid
`g` are at most half of all `2^b` words with odd degree exactly at `a` and `j`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance fourPortsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Pairs of disjoint paths are joins of the four ends -/

/-- The sum of the two paths determines a pair of disjoint paths. -/
theorem numPathPairs_le_of_sums (N : Network V E) (a b c d : V) (P : N.Word → Prop)
    (hP : ∀ y, P y ↔ ∃ A B, N.IsPathPair a b c d A B ∧ y = A + B) :
    N.numPathPairs a b c d ≤ Nat.card {y : N.Word // P y} := by
  obtain ⟨f, hf⟩ : ∃ f : {AB : N.Word × N.Word // N.IsPathPair a b c d AB.1 AB.2} →
      {y : N.Word // P y}, ∀ AB, (f AB).1 = AB.1.1 + AB.1.2 :=
    ⟨fun AB => ⟨AB.1.1 + AB.1.2, (hP _).2 ⟨AB.1.1, AB.1.2, AB.2, rfl⟩⟩, fun _ => rfl⟩
  apply Nat.card_le_card_of_injective f
  intro AB AB' h
  have h1 : AB.1.1 + AB.1.2 = AB'.1.1 + AB'.1.2 := by rw [← hf AB, ← hf AB', h]
  obtain ⟨h2, h3⟩ := AB.2.eq_of_add_eq AB'.2 h1
  exact Subtype.ext (Prod.ext h2 h3)

/-- **`F ≤ 1`.** In a network of rank `b`, the pairs of disjoint paths between the four vertices
`a`, `b`, `c`, `d`, for the three pairings together, are at most `2^b`. The sum of the two paths
is a word with odd degree exactly at the four vertices, and it determines the pairing and the
pair. -/
theorem numPathPairs_add_le (N : Network V E) (a b c d : V) :
    N.numPathPairs a b c d + N.numPathPairs a c b d + N.numPathPairs a d b c ≤
      2 ^ networkRank N := by
  obtain ⟨P₁, hP₁⟩ : ∃ P : N.Word → Prop,
      ∀ y, P y ↔ ∃ A B, N.IsPathPair a b c d A B ∧ y = A + B := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P : N.Word → Prop,
      ∀ y, P y ↔ ∃ A B, N.IsPathPair a c b d A B ∧ y = A + B := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₃, hP₃⟩ : ∃ P : N.Word → Prop,
      ∀ y, P y ↔ ∃ A B, N.IsPathPair a d b c A B ∧ y = A + B := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₁₂, hP₁₂⟩ : ∃ P : N.Word → Prop, ∀ y, P y ↔ (P₁ y ∨ P₂ y) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : N.Word → Prop,
      ∀ y, R y ↔ N.boundary y = N.pathDemand a b + N.pathDemand c d := ⟨_, fun _ => Iff.rfl⟩
  have h1 := N.numPathPairs_le_of_sums a b c d P₁ hP₁
  have h2 := N.numPathPairs_le_of_sums a c b d P₂ hP₂
  have h3 := N.numPathPairs_le_of_sums a d b c P₃ hP₃
  have hδ2 : N.pathDemand a c + N.pathDemand b d = N.pathDemand a b + N.pathDemand c d := by
    unfold pathDemand
    abel
  have hδ3 : N.pathDemand a d + N.pathDemand b c = N.pathDemand a b + N.pathDemand c d := by
    unfold pathDemand
    abel
  have k1 := natCard_add_le_of_imp P₁ P₂ P₁₂ (fun y h => (hP₁₂ y).2 (Or.inl h))
    (fun y h => (hP₁₂ y).2 (Or.inr h)) (by
      intro y h h'
      obtain ⟨A, B, hAB, rfl⟩ := (hP₁ y).1 h
      obtain ⟨A', B', hAB', h''⟩ := (hP₂ _).1 h'
      exact hAB.false_of_add_eq hAB' h'' hAB.2.1.deg_left_pos)
  have k2 := natCard_add_le_of_imp P₁₂ P₃ R
    (by
      intro y h
      rw [hR]
      rcases (hP₁₂ y).1 h with h | h
      · obtain ⟨A, B, hAB, rfl⟩ := (hP₁ y).1 h
        exact hAB.boundary_add
      · obtain ⟨A, B, hAB, rfl⟩ := (hP₂ y).1 h
        rw [hAB.boundary_add, hδ2])
    (by
      intro y h
      rw [hR]
      obtain ⟨A, B, hAB, rfl⟩ := (hP₃ y).1 h
      rw [hAB.boundary_add, hδ3])
    (by
      intro y h h'
      obtain ⟨A', B', hAB', h''⟩ := (hP₃ y).1 h'
      rcases (hP₁₂ y).1 h with h | h
      · obtain ⟨A, B, hAB, rfl⟩ := (hP₁ y).1 h
        exact hAB.false_of_add_eq hAB' h'' hAB.2.1.deg_right_pos
      · obtain ⟨A, B, hAB, rfl⟩ := (hP₂ y).1 h
        exact hAB.false_of_add_eq hAB' h'' hAB.2.1.deg_right_pos)
  have k3 : Nat.card {y : N.Word // R y} ≤ 2 ^ networkRank N :=
    le_trans (natCard_le_of_imp (fun y h => (hR y).1 h))
      (N.natCard_boundary_eq_le (N.pathDemand a b + N.pathDemand c d))
  omega

/-! ### Full pairs -/

/-- **Lemma 5.1 of the paper, one direction.** If the pair `s`, `t` is full, then every word with
odd degree exactly at `s` and `t` is a path. -/
theorem IsFullPair.isPathWord_of_boundary {N : Network V E} {s t : V} (h : N.IsFullPair s t)
    {y : N.Word} (hy : N.boundary y = N.pathDemand s t) : N.IsPathWord s t y := by
  obtain ⟨f, hf⟩ : ∃ f : {x : N.Word // N.IsPathWord s t x} →
      {y : N.Word // N.boundary y = N.pathDemand s t}, ∀ x, (f x).1 = x.1 :=
    ⟨fun x => ⟨x.1, x.2.boundary_eq⟩, fun _ => rfl⟩
  have hinj : Function.Injective f := by
    intro x x' hxx
    apply Subtype.ext
    rw [← hf x, ← hf x', hxx]
  have hcard : Nat.card {y : N.Word // N.boundary y = N.pathDemand s t} ≤
      Nat.card {x : N.Word // N.IsPathWord s t x} := by
    have h1 := N.natCard_boundary_eq_le (N.pathDemand s t)
    have h2 : Nat.card {x : N.Word // N.IsPathWord s t x} = 2 ^ networkRank N := h
    omega
  obtain ⟨x, hx⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨y, hy⟩
  have h3 : x.1 = y := by rw [← hf x, hx]
  rw [← h3]
  exact x.2

/-- **A port of a full pair lies on a cycle.** In a pole, let the pair `a`, `k` be full, where
`k` is a port. Then every edge at `k` lies on a cycle. -/
theorem IsFullPair.exists_cycle_at {N : Network V E} (hN : N.IsWeakPole) {a k : V}
    (hk : N.IsPort k) (h : N.IsFullPair a k) {g : E} (hg : N.src g = k ∨ N.dst g = k) :
    ∃ Z : N.Word, N.IsCycleWord Z ∧ Z g ≠ 0 := by
  refine Classical.not_not.1 fun hno => ?_
  have hbr : ∀ Z : N.Word, N.IsCycleWord Z → Z g = 0 := fun Z hZ =>
    Classical.not_not.1 fun hne => hno ⟨Z, hZ, hne⟩
  obtain ⟨w, hw⟩ := N.exists_joins hg
  have hSw : ¬ N.sideOf g k w := N.not_reachable_of_bridge hbr hw
  have hC : ∀ g', N.crosses (N.sideOf g k) g' → g' = g := fun g' h' =>
    N.eq_of_crosses_sideOf g k h'
  have hdeg := fun v => hN.deg_zero_or_two_le v
  have hfull : N.numPaths a k = 2 ^ networkRank N := h
  have hpos : 0 < 2 ^ networkRank N := Nat.two_pow_pos _
  by_cases ha : N.sideOf g k a
  · have h1 := N.two_mul_numPaths_le_of_same_side hdeg (N.sideOf g k) hw (N.sideOf_self g k)
      hSw hC ha (N.sideOf_self g k)
    omega
  · have h1 := N.two_mul_numPaths_le_of_bridge_at hdeg (N.sideOf g k) hw (N.sideOf_self g k)
      hSw hC (le_of_eq hk) ha
    rw [Erdos1016.ExactMaximum.numPaths_symm N k a] at h1
    omega

/-- **Lemma 6.7 of the paper.** In a pole of rank `b`, let the pairs `a`, `j` and `a`, `k` be
full, where `k` is a port. Then at most `2^(b-1)` pairs of disjoint paths join `a` to `j` and
`k` to `l`. -/
theorem two_mul_numPathPairs_le_of_full {N : Network V E} (hN : N.IsWeakPole) {a j k : V}
    (l : V) (hk : N.IsPort k) (hfj : N.IsFullPair a j) (hfk : N.IsFullPair a k) :
    2 * N.numPathPairs a j k l ≤ 2 ^ networkRank N := by
  -- an edge at `k`, and a cycle through it
  obtain ⟨g, f, u, w, -, hg, -, -⟩ := N.exists_two_edges_of_deg_two hk
  have hgk : N.src g = k ∨ N.dst g = k := hg.at_right
  obtain ⟨Z, hZ, hZg⟩ := hfk.exists_cycle_at hN hk hgk
  obtain ⟨J₀, hJ₀⟩ : ∃ J : N.Word → Prop,
      ∀ y, J y ↔ (N.boundary y = N.pathDemand a j ∧ y g = 0) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨J₁, hJ₁⟩ : ∃ J : N.Word → Prop,
      ∀ y, J y ↔ (N.boundary y = N.pathDemand a j ∧ y g ≠ 0) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : N.Word → Prop, ∀ y, R y ↔ N.boundary y = N.pathDemand a j :=
    ⟨_, fun _ => Iff.rfl⟩
  -- the first path of a pair determines the pair, and it does not use `g`
  have h1 : N.numPathPairs a j k l ≤ Nat.card {y : N.Word // J₀ y} := by
    obtain ⟨φ, hφ⟩ : ∃ φ : {AB : N.Word × N.Word // N.IsPathPair a j k l AB.1 AB.2} →
        {y : N.Word // J₀ y}, ∀ AB, (φ AB).1 = AB.1.1 := by
      refine ⟨fun AB => ⟨AB.1.1, (hJ₀ _).2 ⟨AB.2.1.boundary_eq, ?_⟩⟩, fun _ => rfl⟩
      exact N.eq_zero_of_deg_eq_zero (AB.2.2.2.deg_left_eq_zero AB.2.2.1.deg_left_pos) hgk
    apply Nat.card_le_card_of_injective φ
    intro AB AB' hAB
    have hA : AB.1.1 = AB'.1.1 := by rw [← hφ AB, ← hφ AB', hAB]
    have hB : AB.1.2 = AB'.1.2 := by
      apply word_eq_of_add_eq_zero
      -- the word `A + (B + B')` is a path, because the pair `a`, `j` is full
      have hb : N.boundary (AB.1.1 + (AB.1.2 + AB'.1.2)) = N.pathDemand a j := by
        rw [map_add, map_add, AB.2.1.boundary_eq, AB.2.2.1.boundary_eq,
          AB'.2.2.1.boundary_eq, word_add_self, add_zero]
      have hpath := hfj.isPathWord_of_boundary hb
      apply hpath.minimal
      · intro e he
        have hor : AB.1.2 e ≠ 0 ∨ AB'.1.2 e ≠ 0 := by
          rcases Classical.em (AB.1.2 e = 0) with h0 | h0
          · right
            intro h0'
            apply he
            show AB.1.2 e + AB'.1.2 e = 0
            rw [h0, h0', add_zero]
          · exact Or.inl h0
        have hA0 : AB.1.1 e = 0 := by
          rcases hor with hB | hB
          · exact N.eq_zero_of_deg_eq_zero
              (AB.2.2.2.deg_left_eq_zero (N.deg_src_pos hB)) (Or.inl rfl)
          · rw [hA]
            exact N.eq_zero_of_deg_eq_zero
              (AB'.2.2.2.deg_left_eq_zero (N.deg_src_pos hB)) (Or.inl rfl)
        show AB.1.1 e + (AB.1.2 + AB'.1.2) e ≠ 0
        rw [hA0, zero_add]
        exact he
      · rw [map_add, AB.2.2.1.boundary_eq, AB'.2.2.1.boundary_eq]
        exact word_add_self _
    exact Subtype.ext (Prod.ext hA hB)
  -- adding the cycle `Z`
  have h2 : Nat.card {y : N.Word // J₀ y} ≤ Nat.card {y : N.Word // J₁ y} := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : {y : N.Word // J₀ y} → {y : N.Word // J₁ y},
        ∀ y, (ψ y).1 = y.1 + Z := by
      refine ⟨fun y => ⟨y.1 + Z, (hJ₁ _).2 ⟨?_, ?_⟩⟩, fun _ => rfl⟩
      · rw [map_add, ((hJ₀ _).1 y.2).1, hZ.boundary_eq_zero, add_zero]
      · show y.1 g + Z g ≠ 0
        rw [((hJ₀ _).1 y.2).2, zero_add]
        exact hZg
    apply Nat.card_le_card_of_injective ψ
    intro y y' hyy
    have h' : y.1 + Z = y'.1 + Z := by rw [← hψ y, ← hψ y', hyy]
    exact Subtype.ext (add_right_cancel h')
  have h3 := natCard_add_le_of_imp J₀ J₁ R (fun y h => (hR y).2 ((hJ₀ y).1 h).1)
    (fun y h => (hR y).2 ((hJ₁ y).1 h).1) (fun y h h' => ((hJ₁ y).1 h').2 ((hJ₀ y).1 h).2)
  have h4 : Nat.card {y : N.Word // R y} ≤ 2 ^ networkRank N :=
    le_trans (natCard_le_of_imp (fun y h => (hR y).1 h))
      (N.natCard_boundary_eq_le (N.pathDemand a j))
  omega

/-! ### A network of rank one -/

omit [Fintype V] in
/-- A selected edge at a vertex gives a positive selected degree. -/
theorem deg_pos_of_apply_ne_zero (N : Network V E) {x : N.Word} {g : E} {v : V}
    (hx : x g ≠ 0) (hg : N.src g = v ∨ N.dst g = v) : 0 < N.deg x v := by
  rcases hg with h | h
  · rw [← h]
    exact N.deg_src_pos hx
  · rw [← h]
    exact N.deg_dst_pos hx

/-- In a network of rank one in which every vertex has even degree, two pairs of disjoint paths
between the same ends have the same first path. The sum of two different first paths is the word
of all edges, and this word has an edge at an end of the second paths. -/
theorem IsPathPair.left_eq_of_rank_one {N : Network V E}
    (heven : N.boundary (fun _ => 1) = 0) (h1 : networkRank N = 1) {a b c d : V}
    {A B A' B' : N.Word} (h : N.IsPathPair a b c d A B) (h' : N.IsPathPair a b c d A' B') :
    A = A' := by
  refine Classical.not_not.1 fun hne => ?_
  -- two nonzero words with even degrees are equal
  have hcard : Nat.card {x : N.Word // N.boundary x = 0} = 2 := by
    rw [N.natCard_even, h1, pow_one]
  obtain ⟨y₀, -, huniq⟩ :=
    (Nat.card_eq_two_iff' (⟨0, map_zero _⟩ : {x : N.Word // N.boundary x = 0})).1 hcard
  have key : ∀ z : N.Word, N.boundary z = 0 → z ≠ 0 → z = y₀.1 := by
    intro z hz hz0
    have h2 := huniq ⟨z, hz⟩ (fun hh => hz0 (congrArg Subtype.val hh))
    exact congrArg Subtype.val h2
  -- the word of all edges
  obtain ⟨g, -, hgc⟩ := N.exists_edge_of_deg_pos h.2.1.deg_left_pos
  have hone : (fun _ : E => (1 : Bit)) ≠ 0 := fun hh => one_ne_zero (congrFun hh g)
  have hAA : N.boundary (A + A') = 0 := by
    rw [map_add, h.1.boundary_eq, h'.1.boundary_eq]
    exact word_add_self _
  have hAA0 : A + A' ≠ 0 := fun hh => hne (word_eq_of_add_eq_zero hh)
  have heq : A + A' = fun _ => 1 := (key _ hAA hAA0).trans (key _ heven hone).symm
  have hg1 : A g + A' g = 1 := congrFun heq g
  rcases Classical.em (A g = 0) with h0 | h0
  · have hA'g : A' g ≠ 0 := by
      intro hh
      rw [h0, hh, add_zero] at hg1
      exact zero_ne_one hg1
    have d1 := N.deg_pos_of_apply_ne_zero hA'g hgc
    have d2 := h'.2.1.deg_left_pos
    rcases h'.2.2 c with d | d <;> omega
  · have d1 := N.deg_pos_of_apply_ne_zero h0 hgc
    have d2 := h.2.1.deg_left_pos
    rcases h.2.2 c with d | d <;> omega

/-- **A network of rank one.** In a network of rank one in which every vertex has even degree, at
most one pair of disjoint paths joins `a` to `b` and `c` to `d`. -/
theorem numPathPairs_le_one_of_rank_one (N : Network V E)
    (heven : N.boundary (fun _ => 1) = 0) (h1 : networkRank N = 1) (a b c d : V) :
    N.numPathPairs a b c d ≤ 1 := by
  unfold numPathPairs
  rw [Finite.card_le_one_iff_subsingleton]
  refine ⟨fun AB AB' => ?_⟩
  have hA := AB.2.left_eq_of_rank_one heven h1 AB'.2
  have hB := (show N.IsPathPair c d a b AB.1.2 AB.1.1 from
    ⟨AB.2.2.1, AB.2.1, AB.2.2.2.symm⟩).left_eq_of_rank_one heven h1
    (show N.IsPathPair c d a b AB'.1.2 AB'.1.1 from ⟨AB'.2.2.1, AB'.2.1, AB'.2.2.2.symm⟩)
  exact Subtype.ext (Prod.ext hA hB)

end Erdos1016.BoundaryTrace.Network

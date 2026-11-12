import Erdos1016.ExactMaximum.NetAddVertex

set_option autoImplicit false

/-!
# Lemma 5.7: the consequences of Theorem 5.4 for a pole with three or four ports

Let `N` be a pole of rank `h`, and let `K` be the constant of Theorem 5.4 for `ε = 1/1000`
(`FewCyclesWith K`). Lemma 5.7 of the paper "The maximum number of cycles in a graph of large
rank" has four parts. Part (a) is Theorem 5.4. This file proves the other parts, for ports
`a, b, c, d` of `N`:

* `gadget_third_pair` (b): if `P_ac + P_bc ≥ 1.002 · 2^h`, then `P_ab² ≤ 2K 2^h`;
* `gadget_cross_pairs` (c): if `P_ac + P_bc + P_ad + P_bd ≥ 2.004 · 2^h`, then the number of
  pairs of disjoint paths that join `a, b` to `c, d` has a square of at most `4K 2^h`;
* `gadget_opposite_pair` (d): if the number of paths from `c` to `d` plus the number of these
  pairs is at least `1.002 · 2^h`, then `P_ab² ≤ 2K 2^h`.

Each proof adds a new vertex that is joined to `a` and `b` (`NetAddVertex.lean`), in part (c) also
a new vertex that is joined to `c` and `d`, and applies `FewCyclesWith K` to the new pole.
The file also has the symmetries of the number of pairs of disjoint paths.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance gadgetsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Symmetries of the number of pairs of disjoint paths -/

omit [Fintype V] in
/-- The first path of a pair can be taken in the other direction. -/
theorem numPathPairs_swap_left (N : Network V E) (a b c d : V) :
    N.numPathPairs a b c d = N.numPathPairs b a c d :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => ⟨h.1.symm, h.2.1, h.2.2⟩, fun h => ⟨h.1.symm, h.2.1, h.2.2⟩⟩)

omit [Fintype V] in
/-- The second path of a pair can be taken in the other direction. -/
theorem numPathPairs_swap_right (N : Network V E) (a b c d : V) :
    N.numPathPairs a b c d = N.numPathPairs a b d c :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => ⟨h.1, h.2.1.symm, h.2.2⟩, fun h => ⟨h.1, h.2.1.symm, h.2.2⟩⟩)

omit [Fintype V] in
/-- The two paths of a pair can be exchanged. -/
theorem numPathPairs_comm (N : Network V E) (a b c d : V) :
    N.numPathPairs a b c d = N.numPathPairs c d a b := by
  obtain ⟨f, hf⟩ : ∃ f : {AB : N.Word × N.Word // N.IsPathPair a b c d AB.1 AB.2} →
      {AB : N.Word × N.Word // N.IsPathPair c d a b AB.1 AB.2},
      ∀ AB, (f AB).1 = (AB.1.2, AB.1.1) :=
    ⟨fun AB => ⟨(AB.1.2, AB.1.1), AB.2.2.1, AB.2.1, AB.2.2.2.symm⟩, fun _ => rfl⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro AB AB' h
      have h1 : (AB.1.2, AB.1.1) = (AB'.1.2, AB'.1.1) := by rw [← hf AB, ← hf AB', h]
      exact Subtype.ext (Prod.ext (congrArg Prod.snd h1) (congrArg Prod.fst h1))
    · intro AB
      refine ⟨⟨(AB.1.2, AB.1.1), AB.2.2.1, AB.2.1, AB.2.2.2.symm⟩, ?_⟩
      apply Subtype.ext
      rw [hf]
  exact Nat.card_eq_of_bijective f hbij

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance gadgetsDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Lemma 5.7 (b) of the paper.** Let `a, b, c` be ports of a pole of rank `h`. If
`P_ac + P_bc ≥ 1.002 · 2^h`, then `P_ab² ≤ 2K 2^h`. -/
theorem gadget_third_pair {K : ℕ} (hF : FewCyclesWith K) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.IsWeakPole) {a b c : V} (ha : N.IsPort a) (hb : N.IsPort b)
    (hc : N.IsPort c) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hmany : 1002 * 2 ^ networkRank N ≤ 1000 * (N.numPaths a c + N.numPaths b c)) :
    N.numPaths a b ^ 2 ≤ 2 * K * 2 ^ networkRank N := by
  have hpole := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank := N.networkRank_addVertex_le a b
  have hpaths := N.numPaths_add_le_numPaths_addVertex a b c
  have hcyc := N.numPaths_le_numCycles_addVertex a b
  have hpow : 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) :=
    Nat.pow_le_pow_right (by norm_num) hrank
  have hF' := hF (Option V) (E ⊕ Bool) (N.addVertex a b) hpole none (some c)
    (N.isPort_addVertex_none a b) (N.isPort_addVertex_some a b hca hcb hc)
    (fun k => Option.noConfusion k) (by
      rw [pow_succ] at hpow
      omega)
  calc N.numPaths a b ^ 2 ≤ (N.addVertex a b).numCycles ^ 2 := Nat.pow_le_pow_left hcyc 2
    _ ≤ K * 2 ^ networkRank (N.addVertex a b) := hF'
    _ ≤ K * 2 ^ (networkRank N + 1) := Nat.mul_le_mul_left K hpow
    _ = 2 * K * 2 ^ networkRank N := by
        rw [pow_succ]
        ring

/-- **Lemma 5.7 (d) of the paper.** Let `a, b, c, d` be ports of a pole of rank `h`. If the
number of paths from `c` to `d` plus the number of pairs of disjoint paths that join `c, d` to
`a, b` is at least `1.002 · 2^h`, then `P_ab² ≤ 2K 2^h`. -/
theorem gadget_opposite_pair {K : ℕ} (hF : FewCyclesWith K) {V E : Type} [Fintype V]
    [Fintype E] (N : Network V E) (hN : N.IsWeakPole) {a b c d : V} (ha : N.IsPort a)
    (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d) (hab : a ≠ b) (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hmany : 1002 * 2 ^ networkRank N ≤
      1000 * (N.numPaths c d + N.numPathPairs c a b d + N.numPathPairs c b a d)) :
    N.numPaths a b ^ 2 ≤ 2 * K * 2 ^ networkRank N := by
  have hpole := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank := N.networkRank_addVertex_le a b
  have hpaths := N.numPaths_pairs_le_numPaths_addVertex a b c d
  have hcyc := N.numPaths_le_numCycles_addVertex a b
  have hpow : 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) :=
    Nat.pow_le_pow_right (by norm_num) hrank
  have hF' := hF (Option V) (E ⊕ Bool) (N.addVertex a b) hpole (some c) (some d)
    (N.isPort_addVertex_some a b hca hcb hc) (N.isPort_addVertex_some a b hda hdb hd)
    (fun k => hcd (Option.some.inj k)) (by
      rw [pow_succ] at hpow
      omega)
  calc N.numPaths a b ^ 2 ≤ (N.addVertex a b).numCycles ^ 2 := Nat.pow_le_pow_left hcyc 2
    _ ≤ K * 2 ^ networkRank (N.addVertex a b) := hF'
    _ ≤ K * 2 ^ (networkRank N + 1) := Nat.mul_le_mul_left K hpow
    _ = 2 * K * 2 ^ networkRank N := by
        rw [pow_succ]
        ring

/-- **Lemma 5.7 (c) of the paper.** Let `a, b, c, d` be ports of a pole of rank `h`. If
`P_ac + P_bc + P_ad + P_bd ≥ 2.004 · 2^h`, then the number `f` of pairs of disjoint paths that
join `c, d` to `a, b` satisfies `f² ≤ 4K 2^h`. -/
theorem gadget_cross_pairs {K : ℕ} (hF : FewCyclesWith K) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.IsWeakPole) {a b c d : V} (ha : N.IsPort a) (hb : N.IsPort b)
    (hc : N.IsPort c) (hd : N.IsPort d) (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hmany : 2004 * 2 ^ networkRank N ≤
      1000 * (N.numPaths a c + N.numPaths b c + (N.numPaths a d + N.numPaths b d))) :
    (N.numPathPairs c a b d + N.numPathPairs c b a d) ^ 2 ≤ 4 * K * 2 ^ networkRank N := by
  -- the first new vertex, at `a` and `b`
  have hpole₁ := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank₁ := N.networkRank_addVertex_le a b
  have hc₁ := N.isPort_addVertex_some a b hca hcb hc
  have hd₁ := N.isPort_addVertex_some a b hda hdb hd
  have hz₁ := N.isPort_addVertex_none a b
  have hcd₁ : (some c : Option V) ≠ some d := fun k => hcd (Option.some.inj k)
  -- the second new vertex, at `c` and `d`
  have hpole₂ := (N.addVertex a b).isWeakPole_addVertex (some c) (some d) hpole₁ hcd₁ hc₁ hd₁
  have hrank₂ := (N.addVertex a b).networkRank_addVertex_le (some c) (some d)
  have hw₂ := (N.addVertex a b).isPort_addVertex_none (some c) (some d)
  have hz₂ := (N.addVertex a b).isPort_addVertex_some (some c) (some d)
    (fun k : (none : Option V) = some c => Option.noConfusion k)
    (fun k : (none : Option V) = some d => Option.noConfusion k) hz₁
  -- the paths between the two new vertices
  have hp₂ := (N.addVertex a b).numPaths_add_le_numPaths_addVertex (some c) (some d) none
  rw [numPaths_symm (N.addVertex a b) (some c) none,
    numPaths_symm (N.addVertex a b) (some d) none] at hp₂
  have hpc := N.numPaths_add_le_numPaths_addVertex a b c
  have hpd := N.numPaths_add_le_numPaths_addVertex a b d
  -- the cycles through the two new vertices
  have hcyc₂ := (N.addVertex a b).numPaths_le_numCycles_addVertex (some c) (some d)
  have hpairs := N.numPaths_pairs_le_numPaths_addVertex a b c d
  have hpow : 2 ^ networkRank ((N.addVertex a b).addVertex (some c) (some d)) ≤
      2 ^ (networkRank N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF' := hF (Option (Option V)) ((E ⊕ Bool) ⊕ Bool)
    ((N.addVertex a b).addVertex (some c) (some d)) hpole₂ none (some none) hw₂ hz₂
    (fun k => Option.noConfusion k) (by
      rw [pow_succ, pow_succ] at hpow
      omega)
  calc (N.numPathPairs c a b d + N.numPathPairs c b a d) ^ 2
      ≤ ((N.addVertex a b).addVertex (some c) (some d)).numCycles ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
    _ ≤ K * 2 ^ networkRank ((N.addVertex a b).addVertex (some c) (some d)) := hF'
    _ ≤ K * 2 ^ (networkRank N + 2) := Nat.mul_le_mul_left K hpow
    _ = 4 * K * 2 ^ networkRank N := by
        rw [pow_succ, pow_succ]
        ring

end Erdos1016.ExactMaximum

import Erdos1016.ExactMaximum.PoleSides
import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false

/-!
# Lemma 5.2 (b): the induction along the bridges of a pole

Lemma 5.2 (b) of the paper "The maximum number of cycles in a graph of large rank" cuts a pole
with the two ports `s`, `t` and many paths at its bridges. The parts `N_i` are bridgeless poles
with two ports, and `b = Σ b_i`, `P_st = Π P(N_i)`, `c = Σ c(N_i)`. The paper then uses
`Σ 2^(b_i/2) ≤ 2 · 2^(b/2)`.

This file proves the reduction as an induction on the number of edges. For a constant `κ` the
inequality `(c + 2κ)² ≤ 4κ² 2^b` holds for the two sides of a bridge if and only if it can be
added: it then holds for the pole (`invariant_add`). For a bridgeless pole it follows from
`c² ≤ K₁ 2^b` with `κ = K₁ + 2` (`invariant_base`).

The result is `twoPoleFewCyclesStatement_of_bridgeless`: Theorem 5.4 for connected bridgeless
poles with two ports (`BridgelessFewCyclesStatement`) implies Theorem 5.4 for poles with two
ports (`TwoPoleFewCyclesStatement`). A bridgeless pole with isolated vertices is first replaced
by the connected network on its vertices of positive degree (`isBridgelessTwoPole_induce`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleBridgesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### A part with all edges -/

omit [Fintype V] in
/-- A part with all edges has the cycles of the network. -/
theorem numCycles_sub_of_forall (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (hp : ∀ e, p e) : (N.sub p).numCycles = N.numCycles := by
  rw [numCycles_sub]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun _ => ⟨fun h => h.1, fun h => ⟨h, fun e _ => hp e⟩⟩)

omit [Fintype V] in
/-- A part with all edges has the paths of the network. -/
theorem numPaths_sub_of_forall (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (hp : ∀ e, p e) (s t : V) : (N.sub p).numPaths s t = N.numPaths s t := by
  rw [numPaths_sub]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun _ => ⟨fun h => h.1, fun h => ⟨h, fun e _ => hp e⟩⟩)

/-- A part with all edges has the rank of the network. -/
theorem networkRank_sub_of_forall (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (hp : ∀ e, p e) : networkRank (N.sub p) = networkRank N := by
  have h3 : Nat.card {y : N.Word // N.boundary y = 0 ∧ Within y p} =
      Nat.card {x : N.Word // N.boundary x = 0} :=
    Nat.card_congr
      (Equiv.subtypeEquivRight fun _ => ⟨fun h => h.1, fun h => ⟨h, fun e _ => hp e⟩⟩)
  rw [N.natCard_even_within p, N.natCard_even] at h3
  exact Nat.pow_right_injective (le_refl 2) h3

omit [Fintype V] in
/-- The degree in the network on a set of vertices is the degree in the part of the edges with
both ends in the set. -/
theorem deg_induce (N : Network V E) (S : V → Prop) (y : {e : E // N.inside S e} → Bit)
    (v : {v : V // S v}) : (N.induce S).deg y v = (N.sub (N.inside S)).deg y v.1 := by
  unfold deg
  apply congrArg Finset.card
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : (N.induce S).src g = v ↔ (N.sub (N.inside S)).src g = v.1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : (N.induce S).dst g = v ↔ (N.sub (N.inside S)).dst g = v.1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, h2]

/-- **A bridgeless pole without its isolated vertices.** Let `N` be a pole with the two ports
`s`, `t`, possibly with isolated vertices, in which every edge is on a cycle. Then the network on
the vertices of positive degree is a connected bridgeless pole with the two ports `s`, `t`. It
has the same number of cycles, the same rank, and the same number of paths from `s` to `t`. -/
theorem isBridgelessTwoPole_induce (N : Network V E) {s t : V} (hN : N.IsWeakTwoPole s t)
    (hbl : N.IsBridgeless) :
    ∃ (hs : 0 < N.deg (fun _ => 1) s) (ht : 0 < N.deg (fun _ => 1) t),
      (N.induce fun v => 0 < N.deg (fun _ => 1) v).IsBridgelessTwoPole ⟨s, hs⟩ ⟨t, ht⟩ ∧
      (N.induce fun v => 0 < N.deg (fun _ => 1) v).numCycles = N.numCycles ∧
      networkRank (N.induce fun v => 0 < N.deg (fun _ => 1) v) = networkRank N ∧
      (N.induce fun v => 0 < N.deg (fun _ => 1) v).numPaths ⟨s, hs⟩ ⟨t, ht⟩ =
        N.numPaths s t := by
  have hs : 0 < N.deg (fun _ => 1) s := by
    have h : N.deg (fun _ => 1) s = 2 := hN.port_s
    omega
  have ht : 0 < N.deg (fun _ => 1) t := by
    have h : N.deg (fun _ => 1) t = 2 := hN.port_t
    omega
  -- every edge has both ends of positive degree
  have hone : ∀ g : E, (fun _ : E => (1 : Bit)) g ≠ 0 := fun _ => one_ne_zero
  have hall : ∀ g, N.inside (fun v => 0 < N.deg (fun _ => 1) v) g :=
    fun g => ⟨N.deg_src_pos (hone g), N.deg_dst_pos (hone g)⟩
  have hrestrict : restrict (fun _ => (1 : Bit))
      (N.inside fun v => 0 < N.deg (fun _ => 1) v) = fun _ => 1 := by
    funext g
    exact restrict_apply_of_pos _ (hall g)
  have hdeg : ∀ v : {v : V // 0 < N.deg (fun _ => 1) v},
      (N.induce fun v => 0 < N.deg (fun _ => 1) v).deg (fun _ => 1) v =
        N.deg (fun _ => 1) v.1 := by
    intro v
    rw [N.deg_induce, N.deg_sub_ones, hrestrict]
  refine ⟨hs, ht, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact N.connected_induce (fun v => 0 < N.deg (fun _ => 1) v) hs
      (fun u hu => N.reachable_sub_of_forall hall (hN.pole.2 s u hs hu))
  · exact fun h => hN.ne (congrArg Subtype.val h)
  · rw [hdeg]
    exact hN.port_s
  · rw [hdeg]
    exact hN.port_t
  · intro v hvs hvt
    rw [hdeg]
    have h1 : v.1 ≠ s := fun h => hvs (Subtype.ext h)
    have h2 : v.1 ≠ t := fun h => hvt (Subtype.ext h)
    rcases hN.deg_other h1 h2 with h | h
    · have := v.2
      omega
    · exact h
  · intro g
    obtain ⟨Z, hZ, hZg⟩ := hbl g.1
    have hw : Within Z (N.induceEmbed fun v => 0 < N.deg (fun _ => 1) v).image :=
      fun g' _ => (N.induceEmbed_image _ g').2 (hall g')
    have hpush := (N.induceEmbed fun v => 0 < N.deg (fun _ => 1) v).push_pull hw
    refine ⟨(N.induceEmbed fun v => 0 < N.deg (fun _ => 1) v).pull Z, ?_, hZg⟩
    rw [← (N.induceEmbed fun v => 0 < N.deg (fun _ => 1) v).isCycleWord_push_iff, hpush]
    exact hZ
  · rw [N.numCycles_induce, N.numCycles_sub_of_forall _ hall]
  · rw [N.networkRank_induce, N.networkRank_sub_of_forall _ hall]
  · rw [N.numPaths_induce, N.numPaths_sub_of_forall _ hall]

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleBridgesDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Arithmetic -/

/-- The inequality `(c + 2κ)² ≤ 4κ² X` can be added over the two sides of a bridge. -/
theorem invariant_add {c₁ c₂ κ X Y : ℕ} (hκ : 0 < κ) (h1 : (c₁ + 2 * κ) ^ 2 ≤ 4 * κ ^ 2 * X)
    (h2 : (c₂ + 2 * κ) ^ 2 ≤ 4 * κ ^ 2 * Y) :
    (c₁ + c₂ + 2 * κ) ^ 2 ≤ 4 * κ ^ 2 * (X * Y) := by
  have h3 : 2 * κ * (c₁ + c₂ + 2 * κ) ≤ (c₁ + 2 * κ) * (c₂ + 2 * κ) := by
    have e : (c₁ + 2 * κ) * (c₂ + 2 * κ) = c₁ * c₂ + 2 * κ * (c₁ + c₂ + 2 * κ) := by ring
    rw [e]
    exact Nat.le_add_left _ _
  have h4 : (2 * κ * (c₁ + c₂ + 2 * κ)) ^ 2 ≤ ((c₁ + 2 * κ) * (c₂ + 2 * κ)) ^ 2 :=
    Nat.pow_le_pow_left h3 2
  have h5 : ((c₁ + 2 * κ) * (c₂ + 2 * κ)) ^ 2 ≤ (4 * κ ^ 2 * X) * (4 * κ ^ 2 * Y) := by
    rw [mul_pow]
    exact Nat.mul_le_mul h1 h2
  have h6 : 4 * κ ^ 2 * (c₁ + c₂ + 2 * κ) ^ 2 ≤ 4 * κ ^ 2 * (4 * κ ^ 2 * (X * Y)) := by
    calc 4 * κ ^ 2 * (c₁ + c₂ + 2 * κ) ^ 2 = (2 * κ * (c₁ + c₂ + 2 * κ)) ^ 2 := by ring
      _ ≤ (4 * κ ^ 2 * X) * (4 * κ ^ 2 * Y) := le_trans h4 h5
      _ = 4 * κ ^ 2 * (4 * κ ^ 2 * (X * Y)) := by ring
  have hpos : 0 < 4 * κ ^ 2 := by
    have := pow_pos hκ 2
    omega
  exact Nat.le_of_mul_le_mul_left h6 hpos

/-- The inequality `(c + 2κ)² ≤ 4κ² 2^b` for `κ = K₁ + 2`, from `c < 2^b` and, for `b ≥ 2`, from
`c² ≤ K₁ 2^b`. -/
theorem invariant_base {c b K₁ : ℕ} (hc : c < 2 ^ b) (hK : 2 ≤ b → c ^ 2 ≤ K₁ * 2 ^ b) :
    (c + 2 * (K₁ + 2)) ^ 2 ≤ 4 * (K₁ + 2) ^ 2 * 2 ^ b := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = K₁ + 2 := ⟨_, rfl⟩
  rw [← hκ]
  have hκ2 : 2 ≤ κ := by omega
  have hκsq : 2 * κ ≤ κ ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right κ hκ2
  by_cases hb : 2 ≤ b
  · have h1 := hK hb
    have h4 : 4 ≤ 2 ^ b := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have h2 : (c + 2 * κ) ^ 2 ≤ 2 * c ^ 2 + 8 * κ ^ 2 := by
      zify
      nlinarith [sq_nonneg ((c : ℤ) - 2 * (κ : ℤ))]
    have hKκ : K₁ ≤ κ ^ 2 := by omega
    have h5 : K₁ * 2 ^ b ≤ κ ^ 2 * 2 ^ b := Nat.mul_le_mul_right _ hKκ
    have h6 : κ ^ 2 * 4 ≤ κ ^ 2 * 2 ^ b := Nat.mul_le_mul_left _ h4
    have e : 4 * κ ^ 2 * 2 ^ b = 4 * (κ ^ 2 * 2 ^ b) := by ring
    rw [e]
    omega
  · have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with hb0 | hb1
    · rw [hb0, pow_zero] at hc
      have hc0 : c = 0 := by omega
      rw [hc0, hb0, pow_zero, zero_add, mul_one]
      have e : (2 * κ) ^ 2 = 4 * κ ^ 2 := by ring
      omega
    · rw [hb1, pow_one] at hc
      have h1 : (c + 2 * κ) ^ 2 ≤ (1 + 2 * κ) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e1 : (1 + 2 * κ) ^ 2 = 1 + 4 * κ + 4 * κ ^ 2 := by ring
      have e2 : 4 * κ ^ 2 * 2 ^ b = 8 * κ ^ 2 := by
        rw [hb1]
        ring
      rw [e2]
      omega

/-! ### The induction -/

/-- The conclusion of Theorem 5.4 of the paper for `ε = 1/1000`, with the constant `K`, for
connected bridgeless poles with two ports. -/
def BridgelessFewCyclesWith (K : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t → 501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
    N.numCycles ^ 2 ≤ K * 2 ^ networkRank N

/-- **Theorem 5.4 of the paper for `ε = 1/1000`, for connected bridgeless poles with two
ports.** Not proved in this file. -/
def BridgelessFewCyclesStatement : Prop := ∃ K : ℕ, BridgelessFewCyclesWith K

/-- **Lemma 5.2 (b) of the paper, as an induction.** If connected bridgeless poles with two
ports have at most `(K₁ 2^b)^(1/2)` cycles, then every pole `N` with the two ports `s`, `t` and
at least `0.501 · 2^b` paths from `s` to `t` satisfies `(c + 2κ)² ≤ 4κ² 2^b` with
`κ = K₁ + 2`. -/
theorem pole_invariant {K₁ : ℕ} (h : BridgelessFewCyclesWith K₁) (V : Type) [Fintype V] :
    ∀ n : ℕ, ∀ (E : Type) [Fintype E] (N : Network V E) (s t : V), Fintype.card E = n →
      N.IsWeakTwoPole s t → 501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      (N.numCycles + 2 * (K₁ + 2)) ^ 2 ≤ 4 * (K₁ + 2) ^ 2 * 2 ^ networkRank N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ N s t hcard hN hmany
    by_cases hbl : N.IsBridgeless
    · -- no bridge: the connected pole on the vertices of positive degree
      obtain ⟨hs, ht, hpole, hc, hr, hp⟩ := N.isBridgelessTwoPole_induce hN hbl
      have hcore := h _ _ _ _ _ hpole (by rw [hr, hp]; exact hmany)
      rw [hc, hr] at hcore
      exact invariant_base N.numCycles_lt_two_pow (fun _ => hcore)
    · -- a bridge
      obtain ⟨e, he⟩ : ∃ e, ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0 := by
        unfold IsBridgeless at hbl
        obtain ⟨e, he⟩ := not_forall.1 hbl
        refine ⟨e, fun Z hZ => Classical.not_not.1 fun hne => he ⟨Z, hZ, hne⟩⟩
      obtain ⟨S, x, y, hj, hx, hy, hC, hSs, hSt, hT₁, hT₂⟩ := N.exists_bridge_split hN hmany he
      have hce : N.crosses S e := N.crosses_of_joins hj hx hy
      have hrank := N.networkRank_of_one_crossing S hC hce
      have hcyc := N.numCycles_of_one_crossing S hC
      have hpaths := N.numPaths_of_one_crossing S hj hx hy hC hSs hSt hT₁.ne hT₂.ne
      -- both sides have many paths
      have hP₁ := (N.sub (N.inside S)).numPaths_le_two_pow s x
      have hP₂ := (N.sub (N.outside S)).numPaths_le_two_pow y t
      rw [hrank, pow_add, hpaths] at hmany
      have hmany₁ : 501 * 2 ^ networkRank (N.sub (N.inside S)) ≤
          1000 * (N.sub (N.inside S)).numPaths s x := by
        have h1 : (501 * 2 ^ networkRank (N.sub (N.inside S))) *
            2 ^ networkRank (N.sub (N.outside S)) ≤
            (1000 * (N.sub (N.inside S)).numPaths s x) *
              2 ^ networkRank (N.sub (N.outside S)) := by
          calc (501 * 2 ^ networkRank (N.sub (N.inside S))) *
                2 ^ networkRank (N.sub (N.outside S))
              = 501 * (2 ^ networkRank (N.sub (N.inside S)) *
                  2 ^ networkRank (N.sub (N.outside S))) := by ring
            _ ≤ 1000 * ((N.sub (N.inside S)).numPaths s x *
                  (N.sub (N.outside S)).numPaths y t) := hmany
            _ = (1000 * (N.sub (N.inside S)).numPaths s x) *
                  (N.sub (N.outside S)).numPaths y t := by ring
            _ ≤ (1000 * (N.sub (N.inside S)).numPaths s x) *
                  2 ^ networkRank (N.sub (N.outside S)) := Nat.mul_le_mul_left _ hP₂
        exact Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos _)
      have hmany₂ : 501 * 2 ^ networkRank (N.sub (N.outside S)) ≤
          1000 * (N.sub (N.outside S)).numPaths y t := by
        have h1 : 2 ^ networkRank (N.sub (N.inside S)) *
            (501 * 2 ^ networkRank (N.sub (N.outside S))) ≤
            2 ^ networkRank (N.sub (N.inside S)) *
              (1000 * (N.sub (N.outside S)).numPaths y t) := by
          calc 2 ^ networkRank (N.sub (N.inside S)) *
                (501 * 2 ^ networkRank (N.sub (N.outside S)))
              = 501 * (2 ^ networkRank (N.sub (N.inside S)) *
                  2 ^ networkRank (N.sub (N.outside S))) := by ring
            _ ≤ 1000 * ((N.sub (N.inside S)).numPaths s x *
                  (N.sub (N.outside S)).numPaths y t) := hmany
            _ = (N.sub (N.inside S)).numPaths s x *
                  (1000 * (N.sub (N.outside S)).numPaths y t) := by ring
            _ ≤ 2 ^ networkRank (N.sub (N.inside S)) *
                  (1000 * (N.sub (N.outside S)).numPaths y t) := Nat.mul_le_mul_right _ hP₁
        exact Nat.le_of_mul_le_mul_left h1 (Nat.two_pow_pos _)
      -- both sides have fewer edges
      have hlt₁ : Fintype.card {g : E // N.inside S g} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (N.not_inside_of_crosses hce)
      have hlt₂ : Fintype.card {g : E // N.outside S g} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (N.not_outside_of_crosses hce)
      have h1 := ih _ hlt₁ {g : E // N.inside S g} (N.sub (N.inside S)) s x rfl hT₁ hmany₁
      have h2 := ih _ hlt₂ {g : E // N.outside S g} (N.sub (N.outside S)) y t rfl hT₂ hmany₂
      have h3 := invariant_add (by omega : 0 < K₁ + 2) h1 h2
      rw [hcyc, hrank, pow_add]
      exact h3

/-- **Lemma 5.2 (b) of the paper, as a reduction.** Theorem 5.4 for connected bridgeless poles
with two ports implies Theorem 5.4 for poles with two ports. -/
theorem twoPoleFewCyclesWith_of_bridgeless {K₁ : ℕ} (h : BridgelessFewCyclesWith K₁) :
    TwoPoleFewCyclesWith (4 * (K₁ + 2) ^ 2) := by
  intro V E _ _ N hN s t hs ht hst hall hmany
  have hinv := pole_invariant h V _ E N s t rfl ⟨hN, hs, ht, hst, hall⟩ hmany
  exact le_trans (Nat.pow_le_pow_left (Nat.le_add_right _ _) 2) hinv

/-- Theorem 5.4 for connected bridgeless poles with two ports implies Theorem 5.4 for poles with
two ports. -/
theorem twoPoleFewCyclesStatement_of_bridgeless (h : BridgelessFewCyclesStatement) :
    TwoPoleFewCyclesStatement := by
  obtain ⟨K₁, h1⟩ := h
  refine ⟨4 * (K₁ + 2) ^ 2, ?_, twoPoleFewCyclesWith_of_bridgeless h1⟩
  have := pow_pos (show 0 < K₁ + 2 by omega) 2
  omega

end Erdos1016.ExactMaximum

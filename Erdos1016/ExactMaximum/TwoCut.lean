import Erdos1016.ExactMaximum.Poles

set_option autoImplicit false

/-!
# A cyclic cut of size two

This file proves the case `d = 2` of Proposition 6.3 of the paper "The maximum number of cycles
in a graph of large rank": a connected cubic network of large rank `r` whose smallest cyclic cut
has two edges has at most `2^(r-1) + 2 K 2^(r/2)` cycles (`numCycles_le_of_two_cut`).

The proof uses two statements about poles that are not proved here. They are hypotheses of the
theorem, and `FewCyclesStatement` and `PoleCycleBoundStatement` state them once:

* Theorem 5.4 of the paper for `ε = 1/1000`: a pole of rank `b` with two ports that are joined
  by at least `0.501 · 2^b` paths has at most `K 2^(b/2)` cycles;
* Corollary 3.11 of the paper for poles: a pole of large rank `b` has at most `(9/16) 2^b`
  cycles.

The other ingredients are proved: the count `c(G) = c(T₁) + c(T₂) + P(T₁) P(T₂)`, the rank
`r = b₁ + b₂ + 1`, and the structure of a smallest cyclic cut.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance twoCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### The two statements about poles -/

/-- The conclusion of Theorem 5.4 of the paper for `ε = 1/1000`, with the constant `K`: in every
pole, two ports that are joined by at least `0.501 · 2^b` paths force `c² ≤ K 2^b`. -/
def FewCyclesWith (K : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.IsWeakPole →
    ∀ s t : V, N.IsPort s → N.IsPort t → s ≠ t →
      501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      N.numCycles ^ 2 ≤ K * 2 ^ networkRank N

/-- **Theorem 5.4 of the paper for `ε = 1/1000`.** Not proved in this file. -/
def FewCyclesStatement : Prop := ∃ K : ℕ, 1 ≤ K ∧ FewCyclesWith K

/-- The conclusion of Corollary 3.11 of the paper for poles of rank at least `B`. -/
def PoleCycleBoundWith (B : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.IsWeakPole →
    B ≤ networkRank N → 16 * N.numCycles ≤ 9 * 2 ^ networkRank N

/-- **Corollary 3.11 of the paper for poles.** Not proved in this file. -/
def PoleCycleBoundStatement : Prop := ∃ B : ℕ, PoleCycleBoundWith B

/-! ### Arithmetic -/

/-- From `c² ≤ K 2^b`: `c ≤ K 2^⌈b/2⌉`. -/
theorem le_of_sq_le {c K b : ℕ} (h : c ^ 2 ≤ K * 2 ^ b) :
    c ≤ K * 2 ^ ((b + 1) / 2) := by
  have h1 : K * 2 ^ b ≤ (K * 2 ^ ((b + 1) / 2)) ^ 2 := by
    have e1 : (K * 2 ^ ((b + 1) / 2)) ^ 2 = K * K * 2 ^ (2 * ((b + 1) / 2)) := by ring
    rw [e1]
    have h2 : 2 ^ b ≤ 2 ^ (2 * ((b + 1) / 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_le_mul (Nat.le_mul_self K) h2
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 (le_trans h h1)

/-- From `c² ≤ K D` and `16 K ≤ D`: `4 c ≤ D`. -/
theorem four_mul_le {c K D : ℕ} (h : c ^ 2 ≤ K * D) (hD : 16 * K ≤ D) : 4 * c ≤ D := by
  have h1 : (4 * c) * (4 * c) ≤ D * D := by
    have e1 : (4 * c) * (4 * c) = 16 * c ^ 2 := by ring
    rw [e1]
    calc 16 * c ^ 2 ≤ 16 * (K * D) := Nat.mul_le_mul_left 16 h
      _ = (16 * K) * D := by ring
      _ ≤ D * D := Nat.mul_le_mul_right D hD
  exact Nat.mul_self_le_mul_self_iff.1 h1

/-- The count for a cut of size two, when the first side has the smaller rank. -/
theorem two_cut_arith_aux {K B c₁ c₂ P₁ P₂ b₁ b₂ : ℕ} (hK : 1 ≤ K) (hb₁ : 1 ≤ b₁)
    (hle : b₁ ≤ b₂) (hc₁ : c₁ < 2 ^ b₁) (hP₁ : P₁ ≤ 2 ^ b₁) (hP₂ : P₂ ≤ 2 ^ b₂)
    (hF₁ : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂ : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hG₂ : B ≤ b₂ → 16 * c₂ ≤ 9 * 2 ^ b₂) (hlarge : 2 * max B (16 * K) + 8 ≤ b₁ + b₂) :
    c₁ + c₂ + P₁ * P₂ ≤ 2 ^ (b₁ + b₂) + 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) := by
  have hmax : max B (16 * K) + 4 ≤ b₂ := by omega
  have hB : B ≤ b₂ := by
    have := le_max_left B (16 * K)
    omega
  have h16K : 16 * K ≤ b₂ := by
    have := le_max_right B (16 * K)
    omega
  have hA2 : 2 ≤ 2 ^ b₁ := Nat.le_self_pow (by omega) 2
  have h16D : 16 ≤ 2 ^ b₂ := by
    have h : 2 ^ 4 ≤ 2 ^ b₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h
    exact h
  have h16KD : 16 * K ≤ 2 ^ b₂ := le_trans h16K (le_of_lt Nat.lt_two_pow_self)
  have hAD : 2 ^ (b₁ + b₂) = 2 ^ b₁ * 2 ^ b₂ := pow_add 2 b₁ b₂
  have m1 : K * 2 ^ ((b₁ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 2) / 2) :=
    Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
  have m2 : K * 2 ^ ((b₂ + 1) / 2) ≤ K * 2 ^ ((b₁ + b₂ + 2) / 2) :=
    Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e2 : 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) = 2 * (K * 2 ^ ((b₁ + b₂ + 2) / 2)) := by ring
  have k1' : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ≤ K * 2 ^ ((b₁ + 1) / 2) :=
    fun h => le_of_sq_le (hF₁ h)
  have k2' : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ≤ K * 2 ^ ((b₂ + 1) / 2) :=
    fun h => le_of_sq_le (hF₂ h)
  rw [hAD, e2]
  -- abbreviations for the powers
  generalize 2 ^ b₁ = A at *
  generalize 2 ^ b₂ = D at *
  generalize K * 2 ^ ((b₁ + b₂ + 2) / 2) = M at *
  have t3 : 16 * A ≤ A * D := by
    calc 16 * A = A * 16 := by ring
      _ ≤ A * D := Nat.mul_le_mul_left A h16D
  have t4 : 2 * D ≤ A * D := Nat.mul_le_mul_right D hA2
  by_cases hcase₂ : 501 * D ≤ 1000 * P₂
  · have hc₂ := hF₂ hcase₂
    by_cases hcase₁ : 501 * A ≤ 1000 * P₁
    · -- both sides have many paths
      have k1 := k1' hcase₁
      have k2 := k2' hcase₂
      have m3 : P₁ * P₂ ≤ A * D := Nat.mul_le_mul hP₁ hP₂
      omega
    · -- the second side has many paths, the first side does not
      have k2 : 4 * c₂ ≤ D := four_mul_le hc₂ h16KD
      have t1 : P₁ * P₂ ≤ P₁ * D := Nat.mul_le_mul_left P₁ hP₂
      have t2 : 1000 * (P₁ * D) ≤ 501 * (A * D) := by
        calc 1000 * (P₁ * D) = (1000 * P₁) * D := by ring
          _ ≤ (501 * A) * D := Nat.mul_le_mul_right D (le_of_lt (not_le.1 hcase₁))
          _ = 501 * (A * D) := by ring
      generalize P₁ * P₂ = Z at *
      generalize P₁ * D = Y at *
      generalize A * D = X at *
      omega
  · -- the second side has few paths
    have k2 := hG₂ hB
    have t1 : P₁ * P₂ ≤ A * P₂ := Nat.mul_le_mul_right P₂ hP₁
    have t2 : 1000 * (A * P₂) ≤ 501 * (A * D) := by
      calc 1000 * (A * P₂) = A * (1000 * P₂) := by ring
        _ ≤ A * (501 * D) := Nat.mul_le_mul_left A (le_of_lt (not_le.1 hcase₂))
        _ = 501 * (A * D) := by ring
    generalize P₁ * P₂ = Z at *
    generalize A * P₂ = Y at *
    generalize A * D = X at *
    omega

/-- The count for a cut of size two. -/
theorem two_cut_arith {K B c₁ c₂ P₁ P₂ b₁ b₂ : ℕ} (hK : 1 ≤ K) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hc₁ : c₁ < 2 ^ b₁) (hc₂ : c₂ < 2 ^ b₂) (hP₁ : P₁ ≤ 2 ^ b₁) (hP₂ : P₂ ≤ 2 ^ b₂)
    (hF₁ : 501 * 2 ^ b₁ ≤ 1000 * P₁ → c₁ ^ 2 ≤ K * 2 ^ b₁)
    (hF₂ : 501 * 2 ^ b₂ ≤ 1000 * P₂ → c₂ ^ 2 ≤ K * 2 ^ b₂)
    (hG₁ : B ≤ b₁ → 16 * c₁ ≤ 9 * 2 ^ b₁) (hG₂ : B ≤ b₂ → 16 * c₂ ≤ 9 * 2 ^ b₂)
    (hlarge : 2 * max B (16 * K) + 8 ≤ b₁ + b₂) :
    c₁ + c₂ + P₁ * P₂ ≤ 2 ^ (b₁ + b₂) + 2 * K * 2 ^ ((b₁ + b₂ + 2) / 2) := by
  rcases le_total b₁ b₂ with h | h
  · exact two_cut_arith_aux hK hb₁ h hc₁ hP₁ hP₂ hF₁ hF₂ hG₂ hlarge
  · have h1 := two_cut_arith_aux hK hb₂ h hc₂ hP₂ hP₁ hF₂ hF₁ hG₁
      (by omega : 2 * max B (16 * K) + 8 ≤ b₂ + b₁)
    rw [add_comm b₂ b₁, Nat.mul_comm P₂ P₁] at h1
    omega

/-! ### The theorem -/

/-- A crossing edge joins a vertex of `S` and a vertex outside `S`. -/
theorem exists_joins_of_crosses {V E : Type*} (N : Network V E) {S : V → Prop} {e : E}
    (h : N.crosses S e) : ∃ s t, N.Joins e s t ∧ S s ∧ ¬ S t := by
  by_cases h1 : S (N.src e)
  · exact ⟨N.src e, N.dst e, Or.inl ⟨rfl, rfl⟩, h1, fun h2 => h ⟨fun _ => h2, fun _ => h1⟩⟩
  · have h2 : S (N.dst e) := Classical.not_not.1 fun h2 =>
      h ⟨fun k => absurd k h1, fun k => absurd k h2⟩
    exact ⟨N.dst e, N.src e, Or.inr ⟨rfl, rfl⟩, h2, h1⟩

/-- **Proposition 6.3 of the paper, the case of a cut of size two.** Let `N` be a connected cubic
network of rank `r`, without a cyclic cut of size one, and let `S` be a cyclic cut of size two.
If `r` is large, then `N` has at most `2^(r-1) + 2 K 2^⌈r/2⌉` cycles. The constants `K` and `B`
are those of the two statements about poles. -/
theorem numCycles_le_of_two_cut {K B : ℕ} (hK : 1 ≤ K) (hF : FewCyclesWith K)
    (hG : PoleCycleBoundWith B) {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 2 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 2) (hcyc : N.IsCyclicCut S)
    (hR : 2 * max B (16 * K) + 9 ≤ networkRank N) :
    N.numCycles ≤ 2 ^ (networkRank N - 1) + 2 * K * 2 ^ ((networkRank N + 1) / 2) := by
  -- the two crossing edges
  have hcard : (Finset.univ.filter fun g : E => N.crosses S g).card = 2 := by
    rw [← natCard_subtype_eq_card_filter]
    exact hS
  obtain ⟨e, f, hef, hCef⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ g, N.crosses S g ↔ g = e ∨ g = f := by
    intro g
    have h1 : g ∈ (Finset.univ.filter fun g : E => N.crosses S g) ↔ N.crosses S g :=
      ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ g, h⟩⟩
    rw [← h1, hCef, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨s₁, t₁, he, hs₁, ht₁⟩ := exists_joins_of_crosses N ((hmem e).2 (Or.inl rfl))
  obtain ⟨s₂, t₂, hf, hs₂, ht₂⟩ := exists_joins_of_crosses N ((hmem f).2 (Or.inr rfl))
  -- the complement of `S` is a cut of the same kind
  have hS' : N.cutSize (fun v => ¬ S v) = 2 := by
    rw [N.cutSize_not S]
    exact hS
  have hcyc' : 0 < (N.sub (N.inside fun v => ¬ S v)).numCycles := hcyc.2
  have hnn : ∀ v, S v → ¬ ¬ S v := fun v h h' => h' h
  -- the ends of the two edges are different
  have hs : s₁ ≠ s₂ := by
    intro h
    rw [← h] at hf
    exact N.false_of_two_crossing_at hcubic (by norm_num) hmin S hS hcyc.1 hef he hf hs₁ ht₁ ht₂
  have ht : t₁ ≠ t₂ := by
    intro h
    rw [← h] at hf
    exact N.false_of_two_crossing_at hcubic (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' hef
      he.symm hf.symm ht₁ (hnn s₁ hs₁) (hnn s₂ hs₂)
  -- both sides are connected
  have hin := N.reachable_inside_of_minimal hcubic (by norm_num) (by norm_num) hmin S hS hs₁ ht₁
  have hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable t₁ u :=
    N.reachable_inside_of_minimal hcubic (by norm_num) (by norm_num) hmin (fun v => ¬ S v) hS'
      ht₁ (hnn s₁ hs₁)
  -- the rank and the count
  have hrank := N.networkRank_add_one_of_cut S hs₁ ht₁ hN hin hout
  have hS2 : Nat.card {g : E // N.crosses S g} = 2 := hS
  rw [hS2] at hrank
  have hcount := N.numCycles_of_two_crossing S (fun g hg => (hmem g).1 hg) he hs₁ ht₁ hf hs₂ ht₂
    hs ht
  -- the two sides are poles, and the ends of the edges are ports
  have hpole₁ : (N.sub (N.inside S)).IsWeakPole :=
    N.isWeakPole_inside hcubic (by norm_num) (by norm_num) hmin S hS hcyc.1 hs₁ ht₁
  have hpole₂ : (N.sub (N.outside S)).IsWeakPole :=
    N.isWeakPole_inside hcubic (by norm_num) (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' ht₁
      (hnn s₁ hs₁)
  have hport₁ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.inside S)).IsPort s := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (by norm_num) hmin S hS hcyc.1 hg hs' ht'
  have hport₂ : ∀ (g : E) (s t : V), N.Joins g s t → S s → ¬ S t →
      (N.sub (N.outside S)).IsPort t := fun g s t hg hs' ht' =>
    N.isPort_inside hcubic (by norm_num) hmin (fun v => ¬ S v) hS' hcyc' hg.symm ht'
      (hnn s hs')
  -- the hypotheses of the arithmetic
  have hb₁ := networkRank_pos_of_numCycles_pos _ hcyc.1
  have hb₂ := networkRank_pos_of_numCycles_pos _ hcyc.2
  have hc₁ := (N.sub (N.inside S)).numCycles_lt_two_pow
  have hc₂ := (N.sub (N.outside S)).numCycles_lt_two_pow
  have hP₁ := (N.sub (N.inside S)).numPaths_le_two_pow s₁ s₂
  have hP₂ := (N.sub (N.outside S)).numPaths_le_two_pow t₁ t₂
  have hF₁ := hF V {g : E // N.inside S g} (N.sub (N.inside S)) hpole₁ s₁ s₂
    (hport₁ e s₁ t₁ he hs₁ ht₁) (hport₁ f s₂ t₂ hf hs₂ ht₂) hs
  have hF₂ := hF V {g : E // N.outside S g} (N.sub (N.outside S)) hpole₂ t₁ t₂
    (hport₂ e s₁ t₁ he hs₁ ht₁) (hport₂ f s₂ t₂ hf hs₂ ht₂) ht
  have hG₁ := hG V {g : E // N.inside S g} (N.sub (N.inside S)) hpole₁
  have hG₂ := hG V {g : E // N.outside S g} (N.sub (N.outside S)) hpole₂
  have harith := two_cut_arith hK hb₁ hb₂ hc₁ hc₂ hP₁ hP₂ hF₁ hF₂ hG₁ hG₂ (by omega)
  have e1 : networkRank N - 1 =
      networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) := by omega
  have e2 : (networkRank N + 1) / 2 =
      (networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) + 2) / 2 := by
    omega
  rw [e1, e2, hcount]
  exact harith

end Erdos1016.ExactMaximum

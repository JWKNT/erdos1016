import Erdos1016.ExactMaximumSupport.Shortening.BoundedPortExit

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The path recursion using the direct bounded-port exit estimate. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryTrace.Network
open BoundaryDecay
local instance (priority := 100) boundedPortCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type} [Fintype V] [Fintype E]

theorem ShortState.count_of_girth {m G B₁ : ℕ}
    (hpair : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      (∀ z : K.Word, K.IsCycleWord z → 5 ≤ size z) →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        2 ^ (m + 1) * K.numPaths s t < (2 ^ m + 2) * 2 ^ networkRank K)
    {N : Network V E} {C : N.Word} {e : E} (H : N.ShortSetting C e)
    (hG : 12 * size C ≤ G)
    (hgr : size C ≤ networkRank N) {t : V} (het : N.src e = t ∨ N.dst e = t) :
    ∀ (n : ℕ) (D : V → Prop) (R : N.Word) (s : V), N.ShortState C e t D R s → size R = n →
      2 ^ (m + 1) * N.numPathsIn (N.keep e D) s t +
          (2 ^ m + 2) * 2 ^ (networkRank N - size C) ≤
        2 ^ (m + 1) + n * (2 ^ (m + 1) * 2 ^ B₁) +
          (2 ^ m + 2) * 2 ^ (networkRank N - size C + n) := by
  intro n
  induction n with
  | zero =>
    intro D R s St hn
    exfalso
    obtain ⟨g, hg, -⟩ := N.exists_edge_of_deg_pos St.path.deg_left_pos
    unfold size at hn
    rw [Finset.card_eq_zero] at hn
    have hmem : g ∈ (Finset.univ.filter fun k : E => R k ≠ 0) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ g, hg⟩
    rw [hn] at hmem
    exact Finset.not_mem_empty g hmem
  | succ n ih =>
    intro D R s St hn
    obtain ⟨f, hRf, hfs⟩ := N.exists_edge_of_deg_pos St.path.deg_left_pos
    obtain ⟨s', hf⟩ := N.exists_joins hfs
    obtain ⟨fX, w, hX, hCX, hCw, hkX, huniq⟩ := St.exit H St.path.deg_left_pos
    have hCs : 0 < N.deg C s := St.deg_pos_of_deg_pos St.path.deg_left_pos
    have hCt : 0 < N.deg C t := St.deg_pos_of_deg_pos St.path.deg_right_pos
    have hwt : w ≠ t := fun h => by
      rw [h] at hCw
      omega
    have hsize := St.size_lt H
    have hF := N.numPathsIn_le_of_two_edges (N.keep e D) t hf hX (St.edges_at hRf hfs huniq)
    rw [if_neg hwt] at hF
    have hcongr : ∀ u, N.numPathsIn (fun g => N.keep e D g ∧ ¬ (N.src g = s ∨ N.dst g = s)) u t =
        N.numPathsIn (N.keep e (fun v => D v ∨ v = s)) u t := fun u =>
      N.numPathsIn_congr (fun g => (N.keep_insert_iff e D s g).symm) u t
    rw [hcongr w] at hF
    -- the exit edge of `s` does not remain
    have hnkX : ∀ D' : V → Prop, D' s → ¬ N.keep e D' fX := by
      intro D' hs hk
      rcases hX.at_left with h | h
      · exact hk.2.1 (by rw [h]; exact hs)
      · exact hk.2.2 (by rw [h]; exact hs)
    have hnke : ∀ D' : V → Prop, ¬ N.keep e D' e := fun D' hk => hk.1 rfl
    by_cases hs't : s' = t
    · -- the last step: the path leaves the cycle at `s` and ends with the exit edge of `t`
      rw [if_pos hs't] at hF
      rw [hs't] at hf
      have hn0 : n = 0 := by
        have h1 := St.path.eq_unitWord_of_first hf hRf
        rw [h1, size_unitWord] at hn
        omega
      obtain ⟨fT, wT, hT, hCT, hCwT, hkT, huniqT⟩ := St.exit H St.path.deg_right_pos
      -- the only edge at `t` that remains
      have hallT : ∀ g, N.keep e (fun v => D v ∨ v = s) g → (N.src g = t ∨ N.dst g = t) →
          g = fT := by
        intro g hk hgt
        by_cases hC : C g = 0
        · exact huniqT g hgt hC
        · exfalso
          rcases St.cover g hC with h | h
          · have hgf : f = g := N.eq_of_deg_eq_one St.path.2.2.1 hRf hf.at_right h hgt
            rw [← hgf] at hk
            exact ((N.keep_insert_iff e D s f).1 hk).2 hf.at_left
          · exact h ((N.keep_insert_iff e D s g).1 hk).1
      have hwne : wT ≠ w := by
        intro h
        rw [h] at hT
        have hne : fX ≠ fT := by
          intro h'
          rw [← h'] at hT
          rcases hT.eq_or_eq hX.at_left with k | k
          · exact St.path.1 k
          · rw [k] at hCs
            omega
        exact H.cyc.no_two_feet H.short H.five hne hX.symm hT.symm hCw hCs hCt
      have hF1 := N.numPathsIn_le_of_one_edge (N.keep e (fun v => D v ∨ v = s)) w hT hallT
      rw [if_neg hwne, N.numPathsIn_congr
        (fun g => (N.keep_insert_iff e (fun v => D v ∨ v = s) t g).symm) wT w] at hF1
      -- every vertex of the cycle is deleted now
      have hD'' : ∀ v, ((D v ∨ v = s) ∨ v = t) → 0 < N.deg C v := by
        intro v hv
        rcases hv with (hv | hv) | hv
        · exact St.onC v hv
        · rw [hv]
          exact hCs
        · rw [hv]
          exact hCt
      have hoff : ∀ v, ¬ ((D v ∨ v = s) ∨ v = t) → N.deg C v = 0 := by
        intro v hv
        refine Classical.not_not.1 fun hC => ?_
        have hR := St.onR v (Nat.pos_of_ne_zero hC) (fun h => hv (Or.inl (Or.inl h)))
        obtain ⟨g, hg, hgv⟩ := N.exists_edge_of_deg_pos hR
        have hgf : f = g := N.eq_of_deg_eq_one St.path.2.1 hRf hf.at_left hg (by
          refine Classical.not_not.1 fun hgs => ?_
          have h1 := St.path.eq_unitWord_of_first hf hRf
          rw [h1] at hg
          have h2 : f = g := Classical.not_not.1 fun h => hg (unitWord_apply_of_ne h)
          rw [← h2] at hgs
          exact hgs hf.at_left)
        rw [← hgf] at hgv
        rcases hf.eq_or_eq hgv with h | h
        · exact hv (Or.inl (Or.inr h))
        · exact hv (Or.inr h)
      have hpot : size C - 1 ≤
          Nat.card {g : E // N.arcEdges C e (fun v => (D v ∨ v = s) ∨ v = t) g} := by
        have h1 := St.natCard_arcEdges_insert hRf hf.at_left
          (fun v => (D v ∨ v = s) ∨ v = t) (fun v h => Or.inl (Or.inl h)) (Or.inl (Or.inr rfl))
        have h2 := St.pot
        omega
      have hexit := H.exit_bound_of_girth hpair hG (fun v => (D v ∨ v = s) ∨ v = t) hD''
        (fun v hv => H.two_le_deg_keep_of_off _ hD'' (hoff v hv)) hwne
        (by
          have h1 := N.deg_restrict_lt (N.keep e (fun v => (D v ∨ v = s) ∨ v = t)) hT.at_right
            (fun hk => by
              rcases hT.at_left with h | h
              · exact hk.2.1 (by rw [h]; exact Or.inr rfl)
              · exact hk.2.2 (by rw [h]; exact Or.inr rfl))
          have h2 := H.cubic wT
          omega)
        (by
          have h1 := N.deg_restrict_lt (N.keep e (fun v => (D v ∨ v = s) ∨ v = t)) hX.at_right
            (hnkX _ (Or.inl (Or.inr rfl)))
          have h2 := H.cubic w
          omega)
        (size C - 1) hpot
      rw [N.numPathsIn_symm (N.keep e (fun v => D v ∨ v = s)) w t] at hF
      have e1 : networkRank N - 1 - (size C - 1) = networkRank N - size C := by omega
      rw [e1] at hexit
      have e2 : 2 ^ (networkRank N - size C + (n + 1)) = 2 * 2 ^ (networkRank N - size C) := by
        rw [hn0, zero_add, pow_succ, mul_comm]
      have h1 : 2 ^ (m + 1) * N.numPathsIn (N.keep e D) s t ≤
          2 ^ (m + 1) * 1 + 2 ^ (m + 1) * N.numPathsIn (N.keep e (fun v => D v ∨ v = s)) t w := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ hF
      have h2 : 2 ^ (m + 1) * N.numPathsIn (N.keep e (fun v => D v ∨ v = s)) t w ≤
          2 ^ (m + 1) * N.numPathsIn (N.keep e (fun v => (D v ∨ v = s) ∨ v = t)) wT w :=
        Nat.mul_le_mul_left _ hF1
      have e3 : (n + 1) * (2 ^ (m + 1) * 2 ^ B₁) = 2 ^ (m + 1) * 2 ^ B₁ := by
        rw [hn0, zero_add, one_mul]
      have e4 : (2 ^ m + 2) * (2 * 2 ^ (networkRank N - size C)) =
          (2 ^ m + 2) * 2 ^ (networkRank N - size C) +
            (2 ^ m + 2) * 2 ^ (networkRank N - size C) := by ring
      rw [e2, e3, e4]
      omega
    · -- the next state
      rw [if_neg hs't, hcongr s'] at hF
      have St' := St.step hf hRf hs't
      have hsz : size (R + unitWord f) = n := by
        have h1 := size_add_of_subword (N.isSubword_unitWord hRf)
        rw [size_unitWord] at h1
        omega
      have hih := ih _ _ _ St' hsz
      have hpot : size C - (n + 1) ≤
          Nat.card {g : E // N.arcEdges C e (fun v => D v ∨ v = s) g} := by
        have h1 := St'.pot
        omega
      have hexit := H.exit_bound_of_girth hpair hG (fun v => D v ∨ v = s) St'.onC
        (St'.two_le_deg_keep H) hwt
        (by
          have h1 := N.deg_restrict_lt (N.keep e (fun v => D v ∨ v = s)) hX.at_right
            (hnkX _ (Or.inr rfl))
          have h2 := H.cubic w
          omega)
        (by
          have h1 := N.deg_restrict_lt (N.keep e (fun v => D v ∨ v = s)) het (hnke _)
          have h2 := H.cubic t
          omega)
        (size C - (n + 1)) hpot
      have e1 : networkRank N - 1 - (size C - (n + 1)) = networkRank N - size C + n := by omega
      rw [e1] at hexit
      have e2 : 2 ^ (networkRank N - size C + (n + 1)) =
          2 * 2 ^ (networkRank N - size C + n) := by
        rw [← add_assoc, pow_succ, mul_comm]
      have h1 : 2 ^ (m + 1) * N.numPathsIn (N.keep e D) s t ≤
          2 ^ (m + 1) * N.numPathsIn (N.keep e (fun v => D v ∨ v = s)) s' t +
            2 ^ (m + 1) * N.numPathsIn (N.keep e (fun v => D v ∨ v = s)) w t := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ hF
      have e3 : (n + 1) * (2 ^ (m + 1) * 2 ^ B₁) =
          n * (2 ^ (m + 1) * 2 ^ B₁) + 2 ^ (m + 1) * 2 ^ B₁ := by ring
      have e4 : (2 ^ m + 2) * (2 * 2 ^ (networkRank N - size C + n)) =
          (2 ^ m + 2) * 2 ^ (networkRank N - size C + n) +
            (2 ^ m + 2) * 2 ^ (networkRank N - size C + n) := by ring
      rw [e2, e3, e4]
      omega


end Erdos1016.BoundaryTrace.Network

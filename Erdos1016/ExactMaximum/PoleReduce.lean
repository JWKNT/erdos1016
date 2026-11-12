import Erdos1016.ExactMaximum.NetSuppress
import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximum.NetPairs
import Erdos1016.ExactMaximum.TwoCut

set_option autoImplicit false

/-!
# Lemma 5.2 (a): a pole with many paths between two ports has no other port

Lemma 5.2 (a) of the paper "The maximum number of cycles in a graph of large rank" replaces each
port other than `s`, `t`, with its two edges, by one edge. The rank, the number of paths from `s`
to `t` and the number of cycles do not change.

In this file a pole can have isolated vertices (`Network.IsWeakPole`), so the removed port stays
as an isolated vertex (`NetSuppress.lean`). The two neighbours of the port are different: if both
edges at the port end in the same vertex, they form a cycle that meets no path from `s` to `t`,
and then at most half of the possible paths exist (`two_mul_numPaths_le_of_digon`, from
Lemma 5.1).

The result is `fewCyclesWith_of_twoPole`: Theorem 5.4 for poles whose only ports are `s` and `t`
(`TwoPoleFewCyclesWith`) implies Theorem 5.4 for all poles (`FewCyclesWith`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleReduceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- The two edges at a vertex of degree two. -/
theorem exists_two_edges_of_deg_two (N : Network V E) {z : V} (hz : N.deg (fun _ => 1) z = 2) :
    ∃ (e f : E) (u w : V), e ≠ f ∧ N.Joins e u z ∧ N.Joins f z w ∧
      ∀ g, N.src g = z ∨ N.dst g = z → g = e ∨ g = f := by
  unfold deg at hz
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.1 hz
  have hmem : ∀ g, (N.src g = z ∨ N.dst g = z) ↔ g = e ∨ g = f := by
    intro g
    have h1 := Finset.ext_iff.1 hset g
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h1
    exact ⟨fun h => h1.1 ⟨Finset.mem_univ g, one_ne_zero, h⟩, fun h => (h1.2 h).2.2⟩
  obtain ⟨u, hu⟩ := N.exists_joins ((hmem e).2 (Or.inl rfl))
  obtain ⟨w, hw⟩ := N.exists_joins ((hmem f).2 (Or.inr rfl))
  exact ⟨e, f, u, w, hef, hu.symm, hw, fun g hg => (hmem g).1 hg⟩

/-- **Two parallel edges at a vertex of degree two.** Let all degrees be at most three, and let
`s` and `t` have degree two. Let the vertex `z`, other than `s` and `t`, be on exactly two edges,
and let both join `z` and `u`. Then at most half of the possible paths from `s` to `t` exist. -/
theorem two_mul_numPaths_le_of_digon (N : Network V E) {s t z u : V} {e f : E}
    (hdeg : ∀ x, N.deg (fun _ => 1) x ≤ 3) (hs : N.deg (fun _ => 1) s = 2)
    (ht : N.deg (fun _ => 1) t = 2) (hzs : z ≠ s) (hzt : z ≠ t) (hef : e ≠ f)
    (he : N.Joins e u z) (hf : N.Joins f z u)
    (honly : ∀ g, N.src g = z ∨ N.dst g = z → g = e ∨ g = f) :
    2 * N.numPaths s t ≤ 2 ^ networkRank N := by
  -- the cycle of the two parallel edges
  have hfe : (unitWord e : E → Bit) f = 0 := by rw [unitWord_apply, if_neg hef]
  have hef' : (unitWord f : E → Bit) e = 0 := by
    rw [unitWord_apply, if_neg (fun h : f = e => hef h.symm)]
  have hZ : N.IsCycleWord (unitWord e + unitWord f) :=
    (N.isPathWord_unitWord he).add_closing hf.symm hfe
  have hZe : (unitWord e + unitWord f : E → Bit) e ≠ 0 := by
    rw [Pi.add_apply, unitWord_apply, unitWord_apply, if_pos rfl,
      if_neg (fun h : f = e => hef h.symm), add_zero]
    exact one_ne_zero
  have hZu : N.deg (unitWord e + unitWord f) u = 2 := by
    have hpos : 0 < N.deg (unitWord e + unitWord f) u := by
      rcases he.at_left with h | h
      · rw [← h]
        exact N.deg_src_pos hZe
      · rw [← h]
        exact N.deg_dst_pos hZe
    rcases hZ.2.1 u with h | h
    · omega
    · exact h
  -- the edges other than `e` and `f`
  obtain ⟨rest, hrest⟩ : ∃ rest : E → Bit, ∀ g, rest g = if g = e ∨ g = f then 0 else 1 :=
    ⟨_, fun _ => rfl⟩
  have hones : (fun _ => (1 : Bit)) = (unitWord e + unitWord f : E → Bit) + rest := by
    funext g
    rw [Pi.add_apply, Pi.add_apply, hrest, unitWord_apply, unitWord_apply]
    by_cases hge : g = e
    · rw [if_pos (Or.inl hge), if_pos hge.symm, if_neg (fun h : f = g => hef (hge.symm.trans h.symm)),
        add_zero, add_zero]
    · by_cases hgf : g = f
      · rw [if_pos (Or.inr hgf), if_neg (fun h : e = g => hge h.symm), if_pos hgf.symm, zero_add,
          add_zero]
      · rw [if_neg (fun h : g = e ∨ g = f => h.elim hge hgf),
          if_neg (fun h : e = g => hge h.symm), if_neg (fun h : f = g => hgf h.symm), zero_add,
          zero_add]
  have hdisj : ∀ g, (unitWord e + unitWord f : E → Bit) g ≠ 0 → rest g = 0 := by
    intro g hg
    rw [hrest]
    by_cases hge : g = e
    · rw [if_pos (Or.inl hge)]
    · by_cases hgf : g = f
      · rw [if_pos (Or.inr hgf)]
      · exfalso
        apply hg
        rw [Pi.add_apply, unitWord_apply, unitWord_apply, if_neg (fun h : e = g => hge h.symm),
          if_neg (fun h : f = g => hgf h.symm), add_zero]
  have hrestu : N.deg rest u ≤ 1 := by
    have h1 := N.deg_add_of_disjoint hdisj u
    rw [← hones, hZu] at h1
    have h2 := hdeg u
    omega
  apply N.two_mul_numPaths_le_of_disjoint_cycle s t hZ
  intro p hp
  -- the path does not use the vertex `z`
  have hpz : N.deg p z = 0 := by
    rcases hp.2.2.2.1 z hzs hzt with h | h
    · exact h
    · exfalso
      have hpe : p e ≠ 0 := by
        intro h0
        by_cases hpf : p f = 0
        · have h1 : N.deg p z = 0 := by
            apply N.deg_eq_zero_of_forall
            intro g hg
            rcases honly g hg with k | k
            · rw [k]
              exact h0
            · rw [k]
              exact hpf
          omega
        · have h1 : N.deg p z = N.deg (unitWord f) z := by
            apply N.deg_congr
            intro g hg
            rcases honly g hg with k | k
            · rw [k, hef']
              exact ⟨fun h => absurd h0 h, fun h => absurd rfl h⟩
            · rw [k, unitWord_apply, if_pos rfl]
              exact ⟨fun _ => one_ne_zero, fun _ => hpf⟩
          rw [N.deg_unitWord_eq_one hf.at_left] at h1
          omega
      have hpf : p f ≠ 0 := by
        intro h0
        have h1 : N.deg p z = N.deg (unitWord e) z := by
          apply N.deg_congr
          intro g hg
          rcases honly g hg with k | k
          · rw [k, unitWord_apply, if_pos rfl]
            exact ⟨fun _ => one_ne_zero, fun _ => hpe⟩
          · rw [k, hfe]
            exact ⟨fun h => absurd h0 h, fun h => absurd rfl h⟩
        rw [N.deg_unitWord_eq_one he.at_right] at h1
        omega
      have hsub : N.IsSubword (unitWord e + unitWord f) p :=
        (N.isSubword_unitWord hpe).add (N.isSubword_unitWord hpf)
      exact hZ.1 (hp.eq_zero_of_even_subword hsub hZ.boundary_eq_zero)
  have hpe : p e = 0 := N.eq_zero_of_deg_eq_zero hpz he.at_right
  have hpf : p f = 0 := N.eq_zero_of_deg_eq_zero hpz hf.at_left
  -- the path does not use the vertex `u`
  have hpu : N.deg p u = 0 := by
    have hsub : N.IsSubword p rest := by
      intro g hg
      rw [hrest, if_neg]
      · exact one_ne_zero
      · rintro (k | k)
        · exact hg (by rw [k]; exact hpe)
        · exact hg (by rw [k]; exact hpf)
    have hle := hsub.deg_le u
    by_cases hus : u = s
    · exfalso
      have h1 := N.deg_add_of_disjoint hdisj u
      rw [← hones, hZu, hus, hs] at h1
      have h2 := hp.2.1
      rw [hus] at hle
      omega
    · by_cases hut : u = t
      · exfalso
        have h1 := N.deg_add_of_disjoint hdisj u
        rw [← hones, hZu, hut, ht] at h1
        have h2 := hp.2.2.1
        rw [hut] at hle
        omega
      · rcases hp.2.2.2.1 u hus hut with h | h
        · exact h
        · omega
  -- the cycle has the two vertices `z` and `u`
  intro x
  by_cases hxz : x = z
  · left
    rw [hxz]
    exact hpz
  · by_cases hxu : x = u
    · left
      rw [hxu]
      exact hpu
    · right
      apply N.deg_eq_zero_of_forall
      intro g hg
      have hge : g ≠ e := by
        intro k
        rw [k] at hg
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hg with h | h
          · exact hxu (h.symm.trans h1)
          · exact hxz (h.symm.trans h2)
        · rcases hg with h | h
          · exact hxz (h.symm.trans h1)
          · exact hxu (h.symm.trans h2)
      have hgf : g ≠ f := by
        intro k
        rw [k] at hg
        rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hg with h | h
          · exact hxz (h.symm.trans h1)
          · exact hxu (h.symm.trans h2)
        · rcases hg with h | h
          · exact hxu (h.symm.trans h1)
          · exact hxz (h.symm.trans h2)
      rw [Pi.add_apply, unitWord_apply, unitWord_apply, if_neg (fun h : e = g => hge h.symm),
        if_neg (fun h : f = g => hgf h.symm), add_zero]

/-! ### A pole without one of its ports -/

namespace Thread

variable {N : Network V E} {e f : E} {u v w : V} (T : Thread N e f u v w)
include T

omit [Fintype V] in
/-- The new network is a pole if `N` is a pole. -/
theorem isWeakPole_suppress (hN : N.IsWeakPole) : (N.suppress e f u w T.huw).IsWeakPole := by
  constructor
  · intro x
    by_cases hx : x = v
    · left
      rw [hx]
      exact T.deg_suppress_v _
    · rw [T.deg_suppress hx]
      exact hN.1 x
  · intro a b ha hb
    have hav : a ≠ v := by
      intro h
      rw [h, T.deg_suppress_v] at ha
      exact lt_irrefl 0 ha
    have hbv : b ≠ v := by
      intro h
      rw [h, T.deg_suppress_v] at hb
      exact lt_irrefl 0 hb
    rw [T.deg_suppress hav] at ha
    rw [T.deg_suppress hbv] at hb
    exact T.reachable_suppress hav hbv (hN.2 a b ha hb)

omit [Fintype V] in
/-- A vertex other than `v` is a port of the new network if and only if it is a port of `N`. -/
theorem isPort_suppress {x : V} (hx : x ≠ v) :
    (N.suppress e f u w T.huw).IsPort x ↔ N.IsPort x := by
  unfold IsPort
  rw [T.deg_suppress hx]

end Thread

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleReduceDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- The conclusion of Theorem 5.4 of the paper for `ε = 1/1000`, with the constant `K`, for poles
whose only ports are `s` and `t`. -/
def TwoPoleFewCyclesWith (K : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.IsWeakPole →
    ∀ s t : V, N.IsPort s → N.IsPort t → s ≠ t → (∀ z, N.IsPort z → z = s ∨ z = t) →
      501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      N.numCycles ^ 2 ≤ K * 2 ^ networkRank N

/-- **Lemma 5.2 (a) of the paper, as a reduction.** Theorem 5.4 for poles with exactly two ports
implies Theorem 5.4 for all poles. -/
theorem fewCyclesWith_of_twoPole {K : ℕ} (h2 : TwoPoleFewCyclesWith K) : FewCyclesWith K := by
  intro V E _ _ N hN s t hs ht hst hmany
  -- induction on the number of edges
  have key : ∀ n : ℕ, ∀ (E : Type) [Fintype E] (N : Network V E), Fintype.card E = n →
      N.IsWeakPole → N.IsPort s → N.IsPort t →
      501 * 2 ^ networkRank N ≤ 1000 * N.numPaths s t →
      N.numCycles ^ 2 ≤ K * 2 ^ networkRank N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E _ N hcard hN hs ht hmany
      by_cases hall : ∀ z, N.IsPort z → z = s ∨ z = t
      · exact h2 V E N hN s t hs ht hst hall hmany
      · -- a port other than `s` and `t`
        obtain ⟨z, hz⟩ := not_forall.1 hall
        obtain ⟨hzport, hzst⟩ := Classical.not_imp.1 hz
        have hzs : z ≠ s := fun h => hzst (Or.inl h)
        have hzt : z ≠ t := fun h => hzst (Or.inr h)
        obtain ⟨e, f, u, w, hef, he, hf, honly⟩ := N.exists_two_edges_of_deg_two hzport
        -- the two neighbours of the port are different
        have huw : u ≠ w := by
          intro huw
          subst huw
          have hdeg : ∀ x, N.deg (fun _ => 1) x ≤ 3 := by
            intro x
            rcases hN.1 x with h | h | h <;> omega
          have h1 := N.two_mul_numPaths_le_of_digon hdeg hs ht hzs hzt hef he hf honly
          have hpos : 0 < 2 ^ networkRank N := Nat.two_pow_pos _
          omega
        have T : Thread N e f u z w := ⟨he, hf, hef, huw, honly⟩
        have hlt : Fintype.card {g : E // g ≠ f} < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (fun h : f ≠ f => h rfl)
        have hc := ih _ hlt {g : E // g ≠ f} (N.suppress e f u w huw) rfl
          (T.isWeakPole_suppress hN) ((T.isPort_suppress (Ne.symm hzs)).2 hs)
          ((T.isPort_suppress (Ne.symm hzt)).2 ht)
          (by rw [T.networkRank_suppress, T.numPaths_suppress (Ne.symm hzs) (Ne.symm hzt)]
              exact hmany)
        rw [T.networkRank_suppress, T.numCycles_suppress] at hc
        exact hc
  exact key _ E N rfl hN hs ht hmany

/-- **Theorem 5.4 of the paper for `ε = 1/1000`, for poles with exactly two ports.** Not proved
in this file. -/
def TwoPoleFewCyclesStatement : Prop := ∃ K : ℕ, 1 ≤ K ∧ TwoPoleFewCyclesWith K

/-- Theorem 5.4 for poles with exactly two ports implies Theorem 5.4. -/
theorem fewCyclesStatement_of_twoPole (h : TwoPoleFewCyclesStatement) : FewCyclesStatement := by
  obtain ⟨K, hK, h2⟩ := h
  exact ⟨K, hK, fewCyclesWith_of_twoPole h2⟩

end Erdos1016.ExactMaximum

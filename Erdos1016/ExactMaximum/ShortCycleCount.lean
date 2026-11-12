import Erdos1016.ExactMaximum.ShortCycleExit

set_option autoImplicit false

/-!
# The paths along a shortest cycle

Let `C` be a shortest cycle of a connected cubic network `N`, with at least five edges, and let
`e` be an edge of `C` with the end `t` (`ShortSetting`). The proof of Theorem 7.1 of the paper
"The maximum number of cycles in a graph of large rank" sorts the paths between the ends of `e`
that do not use `e` by the vertex where they leave `C`. This file does that as a recursion.

A state (`ShortState`) has a set `D` of deleted vertices of `C`, the remaining part `R` of `C`,
which is a path from the present vertex `s` to `t`, and these invariants: `R` uses only edges
that remain; every edge of `C` is in `R` or deleted; the vertices of `C` that are not deleted are
on `R`; and at least `|C| - 1 - |R|` edges of `C` other than `e` have an end in `D`.

In a state, the present vertex `s` has two edges that remain: the first edge of `R` and its exit
edge. So a path from `s` to `t` continues along `R`, or it leaves `C` at `s`
(`numPathsIn_le_of_two_edges`). The first kind is counted by the next state (`ShortState.step`),
and the second kind by `exit_bound`. At the last vertex before `t`, the path that leaves `C`
ends with the exit edge of `t`, so it is a path between two vertices outside `C`.

The result is `ShortState.count`: for a state with `|R| = n`,

`2^(m+1) P + (2^m + 2) 2^(r-g) ≤ 2^(m+1) + n 2^(m+1) 2^B + (2^m + 2) 2^(r-g+n)`,

where `g = |C|` and `P` is the number of paths from `s` to `t` in what remains.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance shortCycleCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type} [Fintype V] [Fintype E]

/-! ### Tools -/

omit [Fintype V] in
/-- Equivalent sets of edges have the same paths. -/
theorem numPathsIn_congr (N : Network V E) {q q' : E → Prop} (h : ∀ g, q g ↔ q' g) (s t : V) :
    N.numPathsIn q s t = N.numPathsIn q' s t :=
  le_antisymm (N.numPathsIn_mono (fun g hg => (h g).1 hg) s t)
    (N.numPathsIn_mono (fun g hg => (h g).2 hg) s t)

omit [Fintype V] [Fintype E] in
/-- The edges that remain when one more vertex is deleted. -/
theorem keep_insert_iff (N : Network V E) (e : E) (D : V → Prop) (s : V) (g : E) :
    N.keep e (fun v => D v ∨ v = s) g ↔
      (N.keep e D g ∧ ¬ (N.src g = s ∨ N.dst g = s)) := by
  unfold keep
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun h => h2 (Or.inl h), fun h => h3 (Or.inl h)⟩,
      fun h => h.elim (fun h' => h2 (Or.inr h')) (fun h' => h3 (Or.inr h'))⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, fun h => h.elim h2 (fun h' => h4 (Or.inl h')),
      fun h => h.elim h3 (fun h' => h4 (Or.inr h'))⟩

omit [Fintype V] in
/-- A selected edge at a vertex gives a positive selected degree. -/
theorem deg_pos_of_edge (N : Network V E) {x : N.Word} {g : E} {v : V} (hx : x g ≠ 0)
    (hg : N.src g = v ∨ N.dst g = v) : 0 < N.deg x v := by
  rcases hg with h | h
  · rw [← h]
    exact N.deg_src_pos hx
  · rw [← h]
    exact N.deg_dst_pos hx

omit [Fintype V] [Fintype E] in
/-- An end of an edge that joins `a` and `b` is `a` or `b`. -/
theorem Joins.eq_or_eq {N : Network V E} {g : E} {a b v : V} (h : N.Joins g a b)
    (hv : N.src g = v ∨ N.dst g = v) : v = a ∨ v = b := by
  rcases h with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rcases hv with hv | hv
    · exact Or.inl (by rw [← hv, k1])
    · exact Or.inr (by rw [← hv, k2])
  · rcases hv with hv | hv
    · exact Or.inr (by rw [← hv, k1])
    · exact Or.inl (by rw [← hv, k2])

/-! ### States -/

/-- **A state of the recursion along the cycle `C`.** `D` is the set of the deleted vertices,
`R` is the remaining part of `C`, a path from `s` to `t`. -/
structure ShortState (N : Network V E) (C : N.Word) (e : E) (t : V) (D : V → Prop)
    (R : N.Word) (s : V) : Prop where
  path : N.IsPathWord s t R
  sub : N.IsSubword R C
  within : Within R (N.keep e D)
  cover : ∀ g, C g ≠ 0 → R g ≠ 0 ∨ ¬ N.keep e D g
  onC : ∀ v, D v → 0 < N.deg C v
  onR : ∀ v, 0 < N.deg C v → ¬ D v → 0 < N.deg R v
  pot : size C ≤ size R + 1 + Nat.card {g : E // N.arcEdges C e D g}

namespace ShortState

variable {N : Network V E} {C : N.Word} {e : E} {t : V} {D : V → Prop} {R : N.Word} {s : V}

omit [Fintype V] in
/-- A vertex of `R` is not deleted. -/
theorem not_mem_of_deg_pos (St : N.ShortState C e t D R s) {v : V} (hv : 0 < N.deg R v) :
    ¬ D v := by
  obtain ⟨g, hg, hgv⟩ := N.exists_edge_of_deg_pos hv
  have hk := St.within g hg
  rcases hgv with h | h
  · rw [← h]
    exact hk.2.1
  · rw [← h]
    exact hk.2.2

omit [Fintype V] in
/-- A vertex of `R` is a vertex of `C`. -/
theorem deg_pos_of_deg_pos (St : N.ShortState C e t D R s) {v : V} (hv : 0 < N.deg R v) :
    0 < N.deg C v :=
  lt_of_lt_of_le hv (St.sub.deg_le v)

omit [Fintype V] in
/-- `R` has fewer edges than `C`. -/
theorem size_lt (H : N.ShortSetting C e) (St : N.ShortState C e t D R s) : size R < size C := by
  apply St.sub.size_lt
  intro h
  have h1 : R e ≠ 0 := by
    rw [h]
    exact H.mem
  exact (St.within e h1).1 rfl

/-- **The exit edge of a vertex of `R`.** It is an edge that remains, and its other end is
outside `C`. -/
theorem exit (H : N.ShortSetting C e) (St : N.ShortState C e t D R s) {v : V}
    (hv : 0 < N.deg R v) :
    ∃ (f : E) (w : V), N.Joins f v w ∧ C f = 0 ∧ N.deg C w = 0 ∧ N.keep e D f ∧
      ∀ g, (N.src g = v ∨ N.dst g = v) → C g = 0 → g = f := by
  have hCv := St.deg_pos_of_deg_pos hv
  obtain ⟨f, w, hfw, hCf, huniq⟩ := H.cyc.exists_exit H.cubic hCv
  have hw := H.cyc.deg_exit_eq_zero H.short (by have := H.five; omega) hfw hCf hCv
  have hDv := St.not_mem_of_deg_pos hv
  have hDw : ¬ D w := fun h => by
    have := St.onC w h
    omega
  refine ⟨f, w, hfw, hCf, hw, ⟨fun h => H.mem (by rw [← h]; exact hCf), ?_, ?_⟩, huniq⟩
  · rcases hfw with ⟨k1, _⟩ | ⟨k1, _⟩
    · rw [k1]
      exact hDv
    · rw [k1]
      exact hDw
  · rcases hfw with ⟨_, k2⟩ | ⟨_, k2⟩
    · rw [k2]
      exact hDw
    · rw [k2]
      exact hDv

/-- **Every vertex that is not deleted keeps at least two edges.** -/
theorem two_le_deg_keep (H : N.ShortSetting C e) (St : N.ShortState C e t D R s) (v : V)
    (hv : ¬ D v) : 2 ≤ (N.sub (N.keep e D)).deg (fun _ => 1) v := by
  by_cases hC : N.deg C v = 0
  · exact H.two_le_deg_keep_of_off D St.onC hC
  · have hR := St.onR v (Nat.pos_of_ne_zero hC) hv
    obtain ⟨g, hg, hgv⟩ := N.exists_edge_of_deg_pos hR
    obtain ⟨f, w, hfw, hCf, -, hkf, -⟩ := St.exit H hR
    refine N.two_le_deg_restrict (N.keep e D) (fun h => St.sub g hg (by rw [h]; exact hCf)) hgv
      (St.within g hg) hfw.at_left hkf

omit [Fintype V] in
/-- **The edges at the present vertex that remain** are the first edge of `R` and the exit
edge. -/
theorem edges_at (St : N.ShortState C e t D R s) {f : E} (hRf : R f ≠ 0)
    (hfs : N.src f = s ∨ N.dst f = s) {fX : E}
    (hX : ∀ g, (N.src g = s ∨ N.dst g = s) → C g = 0 → g = fX) :
    ∀ g, N.keep e D g → (N.src g = s ∨ N.dst g = s) → g = f ∨ g = fX := by
  intro g hk hgs
  by_cases hC : C g = 0
  · exact Or.inr (hX g hgs hC)
  · rcases St.cover g hC with h | h
    · exact Or.inl (N.eq_of_deg_eq_one St.path.2.1 h hgs hRf hfs)
    · exact absurd hk h

omit [Fintype V] in
/-- One more edge of `C` has an end in the set of deleted vertices, when the present vertex is
deleted. -/
theorem natCard_arcEdges_insert (St : N.ShortState C e t D R s) {f : E} (hRf : R f ≠ 0)
    (hfs : N.src f = s ∨ N.dst f = s) (D' : V → Prop) (hD' : ∀ v, D v → D' v) (hs : D' s) :
    Nat.card {g : E // N.arcEdges C e D g} + 1 ≤ Nat.card {g : E // N.arcEdges C e D' g} := by
  have hk := St.within f hRf
  have h1 : Nat.card {g : E // N.arcEdges C e D g} + Nat.card {g : E // g = f} ≤
      Nat.card {g : E // N.arcEdges C e D' g} :=
    natCard_add_le_of_imp (fun g : E => N.arcEdges C e D g) (fun g => g = f)
      (fun g => N.arcEdges C e D' g)
      (fun g h => ⟨h.1, h.2.1, h.2.2.elim (fun k => Or.inl (hD' _ k)) (fun k => Or.inr (hD' _ k))⟩)
      (by
        intro g h
        rw [h]
        refine ⟨hk.1, St.sub f hRf, ?_⟩
        rcases hfs with k | k
        · exact Or.inl (by rw [k]; exact hs)
        · exact Or.inr (by rw [k]; exact hs))
      (by
        intro g h h'
        rw [h'] at h
        exact h.2.2.elim hk.2.1 hk.2.2)
  have h2 : Nat.card {g : E // g = f} = 1 := Nat.card_unique
  omega

/-- **The next state.** Delete the present vertex `s`, and remove the first edge `f` of `R`.
If the other end `s'` of `f` is not `t`, this is a state with the present vertex `s'`. -/
theorem step (St : N.ShortState C e t D R s) {f : E} {s' : V} (hf : N.Joins f s s')
    (hRf : R f ≠ 0) (hs't : s' ≠ t) :
    N.ShortState C e t (fun v => D v ∨ v = s) (R + unitWord f) s' := by
  have hpath := St.path.erase_first hf hRf hs't
  refine ⟨hpath, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun g hg => St.sub g ((add_unitWord_ne_zero_iff hRf g).1 hg).1
  · intro g hg
    exact (N.keep_insert_iff e D s g).2 ⟨St.within g ((add_unitWord_ne_zero_iff hRf g).1 hg).1,
      St.path.erase_first_not_at hf hRf hg⟩
  · intro g hg
    rcases St.cover g hg with h | h
    · by_cases hgf : g = f
      · right
        intro hk
        exact ((N.keep_insert_iff e D s g).1 hk).2 (by rw [hgf]; exact hf.at_left)
      · exact Or.inl ((add_unitWord_ne_zero_iff hRf g).2 ⟨h, hgf⟩)
    · exact Or.inr (fun hk => h ((N.keep_insert_iff e D s g).1 hk).1)
  · intro v hv
    rcases hv with hv | hv
    · exact St.onC v hv
    · rw [hv]
      exact St.deg_pos_of_deg_pos St.path.deg_left_pos
  · intro v hCv hv
    have hDv : ¬ D v := fun h => hv (Or.inl h)
    have hvs : v ≠ s := fun h => hv (Or.inr h)
    obtain ⟨g, hg, hgv⟩ := N.exists_edge_of_deg_pos (St.onR v hCv hDv)
    by_cases hgf : g = f
    · rw [hgf] at hgv
      rcases hf.eq_or_eq hgv with h | h
      · exact absurd h hvs
      · rw [h]
        exact hpath.deg_left_pos
    · exact N.deg_pos_of_edge ((add_unitWord_ne_zero_iff hRf g).2 ⟨hg, hgf⟩) hgv
  · have h1 := size_add_of_subword (N.isSubword_unitWord hRf)
    rw [size_unitWord] at h1
    have h2 := St.natCard_arcEdges_insert hRf hf.at_left (fun v => D v ∨ v = s)
      (fun v h => Or.inl h) (Or.inr rfl)
    have h3 := St.pot
    omega

end ShortState

/-! ### The count -/

/-- **The paths along the cycle.** In the setting of the count, let `N` have no cyclic cut with
at most four crossing edges, let the statement of `CyclicShore.lean` hold for the numbers `m`,
`G`, `B`, where `12 |C| ≤ G`, and let `|C| ≤ r`. Then in a state with `|R| = n` the number `P`
of paths from the present vertex to `t` in what remains satisfies
`2^(m+1) P + (2^m + 2) 2^(r-g) ≤ 2^(m+1) + n 2^(m+1) 2^B + (2^m + 2) 2^(r-g+n)`. -/
theorem ShortState.count {m G B₁ : ℕ}
    (hshore : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        (2 ^ m + 2) * 2 ^ networkRank K ≤ 2 ^ (m + 1) * K.numPaths s t →
        ∃ S : V → Prop, K.IsCyclicCut S ∧ K.cutSize S ≤ 4 ∧
          ∀ v, S v → K.deg (fun _ => 1) v = 3)
    {N : Network V E} {C : N.Word} {e : E} (H : N.ShortSetting C e)
    (hcut : ∀ S : V → Prop, N.IsCyclicCut S → 5 ≤ N.cutSize S) (hG : 12 * size C ≤ G)
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
      have hexit := H.exit_bound hshore hcut hG (fun v => (D v ∨ v = s) ∨ v = t) hD''
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
      have hexit := H.exit_bound hshore hcut hG (fun v => D v ∨ v = s) St'.onC
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

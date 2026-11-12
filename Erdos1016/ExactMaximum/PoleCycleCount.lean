import Erdos1016.ExactMaximum.CountTools
import Erdos1016.ExactMaximum.PoleMatchings
import Erdos1016.ExactMaximum.PoleBridges

set_option autoImplicit false

/-!
# The count of Theorem 5.4

Let `N` be a connected bridgeless pole with the two ports `s`, `t` and at least `0.501 · 2^b`
paths from `s` to `t`. Theorem 5.4 of the paper "The maximum number of cycles in a graph of large
rank" says that `N` has at most `K 2^(b/2)` cycles. This file proves it
(`bridgelessFewCyclesStatement_of_layers`) from three statements:

* `ThinLayersStatement` (Proposition 5.3): every distance from `s` is at most `b + C`, and at
  most `C` vertices lie outside the ordinary layers;
* `TwoStrandsStatement`: a cycle passes a thin layer in two strands;
* `LayerMatchingStatement`: two consecutive ordinary layers have at most two perfect matchings,
  and of two neighbouring pairs at most one has two.

The proof is the last paragraph of the proof in the paper. For a cycle `Z` let `i` and `j` be
the smallest and the largest distance from `s` of a vertex of `Z` (`lo`, `hi`). The cycle is
determined by its values on the code set `codeSet i j` (`eq_of_restrict_codeSet`): the edges at
the layers `i`, `j` and at the vertices outside ordinary layers, and one separating edge for each
pair of consecutive ordinary layers with two perfect matchings. The code set has at most
`3 (C + 4) + (j - i)/2` edges (`natCard_codeSet_le`). The sum over `i ≤ j ≤ b + C` gives the
bound.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance poleCycleCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### The first and the last layer of a word -/

/-- The word has a vertex at distance `l` from `s`. -/
def meets (N : Network V E) (s : V) (x : N.Word) (l : ℕ) : Prop :=
  ∃ v, 0 < N.deg x v ∧ N.graph.dist s v = l

/-- The smallest distance from `s` of a vertex of the word. -/
def lo (N : Network V E) (s : V) (x : N.Word) : ℕ := sInf {l | N.meets s x l}

/-- The largest distance from `s` of a vertex of the word. -/
def hi (N : Network V E) (s : V) (x : N.Word) : ℕ := sSup {l | N.meets s x l}

theorem bddAbove_meets (N : Network V E) (s : V) (x : N.Word) :
    BddAbove {l | N.meets s x l} := by
  refine ⟨Finset.univ.sup (fun v => N.graph.dist s v), ?_⟩
  rintro l ⟨v, _, hv⟩
  rw [← hv]
  exact Finset.le_sup (f := fun v => N.graph.dist s v) (Finset.mem_univ v)

omit [Fintype V] in
theorem lo_le_dist (N : Network V E) (s : V) {x : N.Word} {v : V} (hv : 0 < N.deg x v) :
    N.lo s x ≤ N.graph.dist s v :=
  Nat.sInf_le ⟨v, hv, rfl⟩

theorem dist_le_hi (N : Network V E) (s : V) {x : N.Word} {v : V} (hv : 0 < N.deg x v) :
    N.graph.dist s v ≤ N.hi s x :=
  le_csSup (N.bddAbove_meets s x) ⟨v, hv, rfl⟩

omit [Fintype V] in
theorem meets_lo (N : Network V E) (s : V) {x : N.Word} {v : V} (hv : 0 < N.deg x v) :
    N.meets s x (N.lo s x) := by
  have hne : ({l | N.meets s x l} : Set ℕ).Nonempty := ⟨N.graph.dist s v, v, hv, rfl⟩
  exact Nat.sInf_mem hne

theorem meets_hi (N : Network V E) (s : V) {x : N.Word} {v : V} (hv : 0 < N.deg x v) :
    N.meets s x (N.hi s x) := by
  have hne : ({l | N.meets s x l} : Set ℕ).Nonempty := ⟨N.graph.dist s v, v, hv, rfl⟩
  exact Nat.sSup_mem hne (N.bddAbove_meets s x)

omit [Fintype V] in
/-- A cycle has a vertex. -/
theorem IsCycleWord.exists_vertex {N : Network V E} {Z : N.Word} (hZ : N.IsCycleWord Z) :
    ∃ v, 0 < N.deg Z v := by
  obtain ⟨e, he⟩ := hZ.exists_edge
  exact ⟨N.src e, N.deg_src_pos he⟩

/-- A word does not take an edge with an end before its first layer or after its last layer. -/
theorem apply_eq_zero_of_outside (N : Network V E) (s : V) {x : N.Word} {g : E}
    (h : N.graph.dist s (N.src g) < N.lo s x ∨ N.graph.dist s (N.dst g) < N.lo s x ∨
      N.hi s x < N.graph.dist s (N.src g) ∨ N.hi s x < N.graph.dist s (N.dst g)) :
    x g = 0 := by
  refine Classical.not_not.1 fun hne => ?_
  have h1 := N.lo_le_dist s (N.deg_src_pos hne)
  have h2 := N.lo_le_dist s (N.deg_dst_pos hne)
  have h3 := N.dist_le_hi s (N.deg_src_pos hne)
  have h4 := N.dist_le_hi s (N.deg_dst_pos hne)
  omega

omit [Fintype V] [Fintype E] in
/-- The two ends of an edge have distances from `s` that differ by at most one. -/
theorem dist_dst_le (N : Network V E) (hN : N.graph.Connected) (s : V) (g : E) :
    N.graph.dist s (N.dst g) ≤ N.graph.dist s (N.src g) + 1 := by
  have hadj : N.graph.Adj (N.src g) (N.dst g) := ⟨g, Or.inl ⟨rfl, rfl⟩⟩
  have h := hN.dist_triangle (u := s) (v := N.src g) (w := N.dst g)
  rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at h
  exact h

omit [Fintype V] [Fintype E] in
theorem dist_src_le (N : Network V E) (hN : N.graph.Connected) (s : V) (g : E) :
    N.graph.dist s (N.src g) ≤ N.graph.dist s (N.dst g) + 1 := by
  have hadj : N.graph.Adj (N.dst g) (N.src g) := ⟨g, Or.inr ⟨rfl, rfl⟩⟩
  have h := hN.dist_triangle (u := s) (v := N.dst g) (w := N.src g)
  rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at h
  exact h

/-! ### The two local statements for one network -/

/-- The statement `TwoStrandsStatement` for the network `N`. -/
def TwoStrandsAt (N : Network V E) (s t : V) : Prop :=
  ∀ (Z : N.Word) (l : ℕ), N.IsCycleWord Z → N.IsThinLayer s t l →
    (∃ u, 0 < N.deg Z u ∧ N.graph.dist s u < l) →
    (∃ w, 0 < N.deg Z w ∧ l < N.graph.dist s w) →
    (∀ g, N.graph.dist s (N.src g) = l → N.graph.dist s (N.dst g) = l → Z g = 0) ∧
      ∀ v, N.graph.dist s v = l →
        N.deg (restrict Z (N.IsLayerEdge s (l - 1))) v = 1 ∧
          N.deg (restrict Z (N.IsLayerEdge s l)) v = 1

/-- The statement `LayerMatchingStatement` for the network `N`. -/
def MatchingsAt (N : Network V E) (s t : V) : Prop :=
  ∀ l : ℕ, N.IsOrdinaryLayer s t l → N.IsOrdinaryLayer s t (l + 1) →
    Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 ∧
      (N.IsOrdinaryLayer s t (l + 2) →
        Nat.card {m : N.Word // N.IsLayerMatching s l m} +
          Nat.card {m : N.Word // N.IsLayerMatching s (l + 1) m} ≤ 3)

/-- **The matching of a cycle.** Let the layers `l` and `l + 1` be thin, and let the cycle `Z`
have a vertex before the layer `l` and a vertex after the layer `l + 1`. Then the edges of `Z`
between the two layers form a perfect matching. -/
theorem isLayerMatching_restrict (N : Network V E) {s t : V} (h2 : N.TwoStrandsAt s t)
    {Z : N.Word} (hZ : N.IsCycleWord Z) {l : ℕ} (hl : N.IsThinLayer s t l)
    (hl' : N.IsThinLayer s t (l + 1)) (hlo : N.lo s Z < l) (hhi : l + 1 < N.hi s Z) :
    N.IsLayerMatching s l (restrict Z (N.IsLayerEdge s l)) := by
  obtain ⟨v₀, hv₀⟩ := hZ.exists_vertex
  obtain ⟨u, hu, hud⟩ := N.meets_lo s hv₀
  obtain ⟨w, hw, hwd⟩ := N.meets_hi s hv₀
  have hA := (h2 Z l hZ hl ⟨u, hu, by omega⟩ ⟨w, hw, by omega⟩).2
  have hB := (h2 Z (l + 1) hZ hl' ⟨u, hu, by omega⟩ ⟨w, hw, by omega⟩).2
  refine ⟨within_restrict _ _, fun v hv => ?_⟩
  rcases hv with hv | hv
  · exact (hA v hv).2
  · have h := (hB v hv).1
    rwa [Nat.add_sub_cancel] at h

/-! ### The code set -/

/-- The vertices of the layers `i` and `j`, and the vertices outside the ordinary layers. -/
def markSet (N : Network V E) (s t : V) (i j : ℕ) (v : V) : Prop :=
  N.graph.dist s v = i ∨ N.graph.dist s v = j ∨ ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)

/-- The ordinary layers `l` and `l + 1` have exactly two perfect matchings. -/
def IsDoubleLayer (N : Network V E) (s t : V) (l : ℕ) : Prop :=
  N.IsOrdinaryLayer s t l ∧ N.IsOrdinaryLayer s t (l + 1) ∧
    Nat.card {m : N.Word // N.IsLayerMatching s l m} = 2

/-- The edges that determine a cycle with first layer `i` and last layer `j`: the edges at the
marked vertices, and the edge `ε l` for each pair of layers strictly between `i` and `j` with two
perfect matchings. -/
def codeSet (N : Network V E) (s t : V) (ε : ℕ → E) (i j : ℕ) (g : E) : Prop :=
  N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g) ∨
    ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l

/-- Two cycles have the same edges between two consecutive ordinary layers strictly inside their
range, if they agree at the separating edge when there are two perfect matchings. -/
theorem restrict_layerEdge_eq (N : Network V E) {s t : V} (h2 : N.TwoStrandsAt s t)
    (hM : N.MatchingsAt s t) (ε : ℕ → E)
    (hε : ∀ l, Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 → ∀ m m' : N.Word,
      N.IsLayerMatching s l m → N.IsLayerMatching s l m' → m (ε l) = m' (ε l) → m = m')
    {Z Z' : N.Word} (hZ : N.IsCycleWord Z) (hZ' : N.IsCycleWord Z') {l : ℕ}
    (hO : N.IsOrdinaryLayer s t l) (hO' : N.IsOrdinaryLayer s t (l + 1))
    (hlo : N.lo s Z < l) (hhi : l + 1 < N.hi s Z) (hlo' : N.lo s Z' < l)
    (hhi' : l + 1 < N.hi s Z') (hval : N.IsDoubleLayer s t l → Z (ε l) = Z' (ε l)) :
    restrict Z (N.IsLayerEdge s l) = restrict Z' (N.IsLayerEdge s l) := by
  have hm := N.isLayerMatching_restrict h2 hZ hO.1 hO'.1 hlo hhi
  have hm' := N.isLayerMatching_restrict h2 hZ' hO.1 hO'.1 hlo' hhi'
  have hcard := (hM l hO hO').1
  by_cases hD : N.IsDoubleLayer s t l
  · apply hε l hcard _ _ hm hm'
    by_cases hLE : N.IsLayerEdge s l (ε l)
    · rw [restrict_apply_of_pos _ hLE, restrict_apply_of_pos _ hLE]
      exact hval hD
    · rw [restrict_apply_of_neg _ hLE, restrict_apply_of_neg _ hLE]
  · have hle1 : Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 1 := by
      have hne : Nat.card {m : N.Word // N.IsLayerMatching s l m} ≠ 2 :=
        fun k => hD ⟨hO, hO', k⟩
      omega
    haveI : Subsingleton {m : N.Word // N.IsLayerMatching s l m} :=
      Finite.card_le_one_iff_subsingleton.1 hle1
    have h := Subsingleton.elim (⟨_, hm⟩ : {m : N.Word // N.IsLayerMatching s l m}) ⟨_, hm'⟩
    exact Subtype.mk.inj h

/-- **A cycle is determined by its values on the code set.** -/
theorem eq_of_restrict_codeSet (N : Network V E) {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (h2 : N.TwoStrandsAt s t) (hM : N.MatchingsAt s t) (ε : ℕ → E)
    (hε : ∀ l, Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 → ∀ m m' : N.Word,
      N.IsLayerMatching s l m → N.IsLayerMatching s l m' → m (ε l) = m' (ε l) → m = m')
    {Z Z' : N.Word} (hZ : N.IsCycleWord Z) (hZ' : N.IsCycleWord Z') {i j : ℕ}
    (hi : N.lo s Z = i) (hj : N.hi s Z = j) (hi' : N.lo s Z' = i) (hj' : N.hi s Z' = j)
    (h : restrict Z (N.codeSet s t ε i j) = restrict Z' (N.codeSet s t ε i j)) : Z = Z' := by
  have hval : ∀ g, N.codeSet s t ε i j g → Z g = Z' g := by
    intro g hg
    have h0 := congrFun h g
    rwa [restrict_apply_of_pos _ hg, restrict_apply_of_pos _ hg] at h0
  funext g
  by_cases hF : N.codeSet s t ε i j g
  · exact hval g hF
  · -- both ends of `g` are in ordinary layers other than `i` and `j`
    have hsrc : ¬ N.markSet s t i j (N.src g) := fun k => hF (Or.inl k)
    have hdst : ¬ N.markSet s t i j (N.dst g) := fun k => hF (Or.inr (Or.inl k))
    obtain ⟨a, ha⟩ : ∃ a, a = N.graph.dist s (N.src g) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = N.graph.dist s (N.dst g) := ⟨_, rfl⟩
    have hai : a ≠ i := fun k => hsrc (Or.inl (by rw [← ha, k]))
    have haj : a ≠ j := fun k => hsrc (Or.inr (Or.inl (by rw [← ha, k])))
    have hOa : N.IsOrdinaryLayer s t a := by
      rw [ha]
      exact Classical.not_not.1 fun k => hsrc (Or.inr (Or.inr k))
    have hci : c ≠ i := fun k => hdst (Or.inl (by rw [← hc, k]))
    have hcj : c ≠ j := fun k => hdst (Or.inr (Or.inl (by rw [← hc, k])))
    have hOc : N.IsOrdinaryLayer s t c := by
      rw [hc]
      exact Classical.not_not.1 fun k => hdst (Or.inr (Or.inr k))
    by_cases hout : a < i ∨ c < i ∨ j < a ∨ j < c
    · have h1 : Z g = 0 := N.apply_eq_zero_of_outside s (by rw [hi, hj, ← ha, ← hc]; exact hout)
      have h1' : Z' g = 0 :=
        N.apply_eq_zero_of_outside s (by rw [hi', hj', ← ha, ← hc]; exact hout)
      rw [h1, h1']
    · have hrange : i < a ∧ a < j ∧ i < c ∧ c < j := by omega
      have hd1 := N.dist_dst_le hN.connected s g
      have hd2 := N.dist_src_le hN.connected s g
      rw [← ha, ← hc] at hd1 hd2
      -- vertices of the two cycles at the layers `i` and `j`
      obtain ⟨v₀, hv₀⟩ := hZ.exists_vertex
      obtain ⟨u, hu, hud⟩ := N.meets_lo s hv₀
      obtain ⟨w, hw, hwd⟩ := N.meets_hi s hv₀
      obtain ⟨v₀', hv₀'⟩ := hZ'.exists_vertex
      obtain ⟨u', hu', hud'⟩ := N.meets_lo s hv₀'
      obtain ⟨w', hw', hwd'⟩ := N.meets_hi s hv₀'
      have hcases : a = c ∨ c = a + 1 ∨ a = c + 1 := by omega
      rcases hcases with hac | hac | hac
      · -- an edge inside an ordinary layer
        have h1 := (h2 Z a hZ hOa.1 ⟨u, hu, by omega⟩ ⟨w, hw, by omega⟩).1 g ha.symm
          (by rw [hac]; exact hc.symm)
        have h1' := (h2 Z' a hZ' hOa.1 ⟨u', hu', by omega⟩ ⟨w', hw', by omega⟩).1 g ha.symm
          (by rw [hac]; exact hc.symm)
        rw [h1, h1']
      · -- an edge from the layer `a` to the layer `a + 1`
        have hLE : N.IsLayerEdge s a g := Or.inl ⟨ha.symm, by rw [← hc, hac]⟩
        have hO' : N.IsOrdinaryLayer s t (a + 1) := by
          rw [← hac]
          exact hOc
        have heq := N.restrict_layerEdge_eq h2 hM ε hε hZ hZ' hOa hO' (by omega) (by omega)
          (by omega) (by omega)
          (fun hD => hval _ (Or.inr (Or.inr ⟨a, hrange.1, by omega, hD, rfl⟩)))
        have h0 := congrFun heq g
        rwa [restrict_apply_of_pos _ hLE, restrict_apply_of_pos _ hLE] at h0
      · -- an edge from the layer `c + 1` to the layer `c`
        have hLE : N.IsLayerEdge s c g := Or.inr ⟨by rw [← ha, hac], hc.symm⟩
        have hO' : N.IsOrdinaryLayer s t (c + 1) := by
          rw [← hac]
          exact hOa
        have heq := N.restrict_layerEdge_eq h2 hM ε hε hZ hZ' hOc hO' (by omega) (by omega)
          (by omega) (by omega)
          (fun hD => hval _ (Or.inr (Or.inr ⟨c, hrange.2.2.1, by omega, hD, rfl⟩)))
        have h0 := congrFun heq g
        rwa [restrict_apply_of_pos _ hLE, restrict_apply_of_pos _ hLE] at h0

/-! ### The size of the code set -/

omit [Fintype E] in
/-- There are at most `C + 4` marked vertices. -/
theorem natCard_markSet_le (N : Network V E) {s t : V} {C : ℕ}
    (hC : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C) (i j : ℕ) :
    Nat.card {v : V // N.markSet s t i j v} ≤ C + 4 := by
  have hlayer : ∀ l : ℕ,
      Nat.card {v : V // N.graph.dist s v = l ∧ N.IsOrdinaryLayer s t l} ≤ 2 := by
    intro l
    by_cases hO : N.IsOrdinaryLayer s t l
    · have h1 : Nat.card {v : V // N.graph.dist s v = l ∧ N.IsOrdinaryLayer s t l} ≤
          Nat.card {v : V // N.graph.dist s v = l} := natCard_le_of_imp (fun v h => h.1)
      rw [hO.1.2.2] at h1
      exact h1
    · haveI : IsEmpty {v : V // N.graph.dist s v = l ∧ N.IsOrdinaryLayer s t l} :=
        ⟨fun v => hO v.2.2⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have h1 : Nat.card {v : V // N.markSet s t i j v} ≤
      Nat.card {v : V // (¬ N.IsOrdinaryLayer s t (N.graph.dist s v) ∨
        (N.graph.dist s v = i ∧ N.IsOrdinaryLayer s t i)) ∨
        (N.graph.dist s v = j ∧ N.IsOrdinaryLayer s t j)} := by
    apply natCard_le_of_imp
    intro v hv
    rcases hv with hv | hv | hv
    · by_cases hO : N.IsOrdinaryLayer s t i
      · exact Or.inl (Or.inr ⟨hv, hO⟩)
      · exact Or.inl (Or.inl (by rw [hv]; exact hO))
    · by_cases hO : N.IsOrdinaryLayer s t j
      · exact Or.inr ⟨hv, hO⟩
      · exact Or.inl (Or.inl (by rw [hv]; exact hO))
    · exact Or.inl (Or.inl hv)
  have h2 : Nat.card {v : V // (¬ N.IsOrdinaryLayer s t (N.graph.dist s v) ∨
        (N.graph.dist s v = i ∧ N.IsOrdinaryLayer s t i)) ∨
        (N.graph.dist s v = j ∧ N.IsOrdinaryLayer s t j)} ≤
      Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v) ∨
        (N.graph.dist s v = i ∧ N.IsOrdinaryLayer s t i)} +
      Nat.card {v : V // N.graph.dist s v = j ∧ N.IsOrdinaryLayer s t j} := natCard_or_le _ _
  have h3 : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v) ∨
        (N.graph.dist s v = i ∧ N.IsOrdinaryLayer s t i)} ≤
      Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} +
      Nat.card {v : V // N.graph.dist s v = i ∧ N.IsOrdinaryLayer s t i} := natCard_or_le _ _
  have h4 := hlayer i
  have h5 := hlayer j
  omega

/-- **The size of the code set.** It has at most `3 (C + 4) + (j - i) / 2` edges. -/
theorem natCard_codeSet_le (N : Network V E) {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hM : N.MatchingsAt s t) (ε : ℕ → E) {C : ℕ}
    (hC : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C) (i j : ℕ) :
    Nat.card {g : E // N.codeSet s t ε i j g} ≤ 3 * (C + 4) + (j - i) / 2 := by
  -- the edges at the marked vertices
  have hdeg : ∀ v, N.deg (fun _ => 1) v ≤ 3 := by
    intro v
    by_cases hvs : v = s
    · rw [hvs, hN.deg_s]
      norm_num
    · by_cases hvt : v = t
      · rw [hvt, hN.deg_t]
        norm_num
      · rw [hN.deg_other v hvs hvt]
  have hF₁ : Nat.card {g : E // N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)} ≤
      3 * Nat.card {v : V // N.markSet s t i j v} := by
    have hsum1 : Nat.card {g : E // N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)} =
        ∑ g, if N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g) then 1 else 0 := by
      rw [natCard_subtype_eq_card_filter, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)
      · rw [if_pos hg, if_pos hg]
      · rw [if_neg hg, if_neg hg]
    have hsumM : 3 * Nat.card {v : V // N.markSet s t i j v} =
        ∑ v, if N.markSet s t i j v then 3 else 0 := by
      rw [natCard_subtype_eq_card_filter, Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : N.markSet s t i j v
      · rw [if_pos hv, if_pos hv, mul_one]
      · rw [if_neg hv, if_neg hv, mul_zero]
    have h1 : (∑ g, if N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g) then 1 else 0)
        ≤ ∑ g, ((if N.markSet s t i j (N.src g) then 1 else 0) +
          (if N.markSet s t i j (N.dst g) then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro g _
      by_cases k1 : N.markSet s t i j (N.src g)
      · rw [if_pos (Or.inl k1), if_pos k1]
        exact Nat.le_add_right _ _
      · by_cases k2 : N.markSet s t i j (N.dst g)
        · rw [if_pos (Or.inr k2), if_pos k2]
          exact Nat.le_add_left _ _
        · rw [if_neg (fun k => k.elim k1 k2)]
          exact Nat.zero_le _
    have h2 : (∑ v, if N.markSet s t i j v then N.deg (fun _ => 1) v else 0) ≤
        ∑ v, if N.markSet s t i j v then 3 else 0 := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : N.markSet s t i j v
      · rw [if_pos hv, if_pos hv]
        exact hdeg v
      · rw [if_neg hv, if_neg hv]
    rw [hsum1, hsumM]
    exact le_trans h1 (le_trans (le_of_eq (N.sum_deg_eq (N.markSet s t i j)).symm) h2)
  -- the separating edges
  have hF₂ : Nat.card {g : E // ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l} ≤
      (j - i) / 2 := by
    obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, ∀ l, l ∈ A ↔ (i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l) :=
      ⟨(Finset.range j).filter (fun l => i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l), fun l => by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩⟩
    have hAcard : A.card ≤ (j - 1 - i) / 2 := by
      apply card_le_half_of_no_consecutive A i (j - 1)
      · intro l hl
        have := (hA l).1 hl
        omega
      · intro l hl hl'
        have h1 := (hA l).1 hl
        have h2 := (hA (l + 1)).1 hl'
        have h3 := (hM l h1.2.2.1 h1.2.2.2.1).2
          (show N.IsOrdinaryLayer s t (l + 2) from h2.2.2.2.1)
        have h4 := h1.2.2.2.2
        have h5 := h2.2.2.2.2
        omega
    have hsub : Nat.card {g : E // ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l} ≤
        (A.image ε).card := by
      rw [natCard_subtype_eq_card_filter]
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨l, h1, h2, h3, h4⟩ := hg.2
      rw [Finset.mem_image]
      exact ⟨l, (hA l).2 ⟨h1, h2, h3⟩, h4.symm⟩
    have himg := Finset.card_image_le (s := A) (f := ε)
    omega
  have h1 : Nat.card {g : E // N.codeSet s t ε i j g} ≤
      Nat.card {g : E // (N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)) ∨
        ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l} := by
    apply natCard_le_of_imp
    intro g hg
    rcases hg with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h2 : Nat.card {g : E // (N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)) ∨
        ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l} ≤
      Nat.card {g : E // N.markSet s t i j (N.src g) ∨ N.markSet s t i j (N.dst g)} +
      Nat.card {g : E // ∃ l, i < l ∧ l + 1 < j ∧ N.IsDoubleLayer s t l ∧ g = ε l} :=
    natCard_or_le _ _
  have h3 := N.natCard_markSet_le hC i j
  omega

end Erdos1016.BoundaryTrace.Network

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleCycleCountDecidable' (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Theorem 5.4 of the paper for `ε = 1/1000`, for connected bridgeless poles with two ports**,
from Proposition 5.3 and the two local statements about cycles. -/
theorem bridgelessFewCyclesStatement_of_layers (hT : ThinLayersStatement)
    (h2 : TwoStrandsStatement) (hM : LayerMatchingStatement) : BridgelessFewCyclesStatement := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨2 ^ (2 * (3 * (C + 4)) + 8 + C), ?_⟩
  intro V E _ _ N s t hN hmany
  obtain ⟨hdist, hbad⟩ := hC V E N s t hN hmany
  have h2' : N.TwoStrandsAt s t := h2 V E N s t hN
  have hM' : N.MatchingsAt s t := hM V E N s t hN
  haveI : Nonempty E := by
    have h : 0 < N.deg (fun _ => 1) s := by
      rw [hN.deg_s]
      norm_num
    obtain ⟨e, _⟩ := N.exists_edge_of_deg_pos h
    exact ⟨e⟩
  -- a separating edge for each pair of layers
  have hsep : ∀ l : ℕ, ∃ ε : E, Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2 →
      ∀ m m' : N.Word, N.IsLayerMatching s l m → N.IsLayerMatching s l m' → m ε = m' ε →
        m = m' := by
    intro l
    by_cases h : Nat.card {m : N.Word // N.IsLayerMatching s l m} ≤ 2
    · obtain ⟨ε, hε⟩ := exists_separating_edge (fun m : N.Word => N.IsLayerMatching s l m) h
      exact ⟨ε, fun _ => hε⟩
    · exact ⟨Classical.arbitrary E, fun h' => absurd h' h⟩
  choose ε hε using hsep
  obtain ⟨n, hn⟩ : ∃ n, n = networkRank N + C := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = 3 * (C + 4) := ⟨_, rfl⟩
  -- the cycles with a given first and last layer
  have hfiber : ∀ i j : ℕ,
      Nat.card {Z : N.Word // (N.IsCycleWord Z ∧ N.hi s Z = j) ∧ N.lo s Z = i} ≤
        2 ^ (K₀ + (j - i) / 2) := by
    intro i j
    refine le_trans (natCard_le_of_determined _ (N.codeSet s t ε i j) ?_)
      (Nat.pow_le_pow_right (by norm_num) ?_)
    · rintro Z Z' ⟨⟨hZ, hj⟩, hi⟩ ⟨⟨hZ', hj'⟩, hi'⟩ hres
      exact N.eq_of_restrict_codeSet hN h2' hM' ε hε hZ hZ' hi hj hi' hj' hres
    · rw [hK₀]
      exact N.natCard_codeSet_le hN hM' ε hbad i j
  -- the cycles with a given last layer
  have hlast : ∀ j : ℕ, Nat.card {Z : N.Word // N.IsCycleWord Z ∧ N.hi s Z = j} ≤
      2 ^ K₀ * halfPowSum j := by
    intro j
    rw [natCard_eq_sum_fibers (fun Z : N.Word => N.IsCycleWord Z ∧ N.hi s Z = j)
      (fun Z => N.lo s Z) (Finset.range (j + 1)) ?_]
    · calc (∑ i ∈ Finset.range (j + 1),
            Nat.card {Z : N.Word // (N.IsCycleWord Z ∧ N.hi s Z = j) ∧ N.lo s Z = i})
          ≤ ∑ i ∈ Finset.range (j + 1), 2 ^ K₀ * 2 ^ ((j - i) / 2) :=
            Finset.sum_le_sum (fun i _ => by
              rw [← pow_add]
              exact hfiber i j)
        _ = 2 ^ K₀ * halfPowSum j := by rw [← Finset.mul_sum, sum_range_half_pow_sub]
    · rintro Z ⟨hZ, hj⟩
      rw [Finset.mem_range]
      show N.lo s Z < j + 1
      obtain ⟨v, hv⟩ := hZ.exists_vertex
      have h1 := N.lo_le_dist s hv
      have h3 := N.dist_le_hi s hv
      omega
  -- all cycles
  have hall : N.numCycles ≤ 2 ^ K₀ * (16 * 2 ^ (n / 2)) := by
    unfold numCycles
    rw [natCard_eq_sum_fibers (fun Z : N.Word => N.IsCycleWord Z) (fun Z => N.hi s Z)
      (Finset.range (n + 1)) ?_]
    · calc (∑ j ∈ Finset.range (n + 1),
            Nat.card {Z : N.Word // N.IsCycleWord Z ∧ N.hi s Z = j})
          ≤ ∑ j ∈ Finset.range (n + 1), 2 ^ K₀ * halfPowSum j :=
            Finset.sum_le_sum (fun j _ => hlast j)
        _ = 2 ^ K₀ * ∑ j ∈ Finset.range (n + 1), halfPowSum j := by rw [Finset.mul_sum]
        _ ≤ 2 ^ K₀ * (16 * 2 ^ (n / 2)) := Nat.mul_le_mul_left _ (sum_halfPowSum_le n)
    · intro Z hZ
      rw [Finset.mem_range]
      show N.hi s Z < n + 1
      obtain ⟨v, hv⟩ := hZ.exists_vertex
      obtain ⟨w, _, hw⟩ := N.meets_hi s hv
      have h1 := hdist w
      omega
  -- the square
  have hsq : N.numCycles ^ 2 ≤ (2 ^ K₀ * (16 * 2 ^ (n / 2))) ^ 2 := Nat.pow_le_pow_left hall 2
  have e1 : (2 ^ K₀ * (16 * 2 ^ (n / 2))) ^ 2 = 2 ^ (2 * K₀ + 8 + 2 * (n / 2)) := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16, ← pow_add, ← pow_add, ← pow_mul]
    congr 1
    ring
  have e2 : 2 ^ (2 * K₀ + 8 + 2 * (n / 2)) ≤
      2 ^ (2 * (3 * (C + 4)) + 8 + C) * 2 ^ networkRank N := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  rw [e1] at hsq
  exact le_trans hsq e2

end Erdos1016.ExactMaximum

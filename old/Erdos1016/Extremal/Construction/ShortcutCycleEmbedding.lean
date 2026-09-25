import Erdos1016.Extremal.Construction.ShortcutBounds
import Mathlib.Combinatorics.SimpleGraph.Circulant

set_option autoImplicit false

/-!
# Embedding the binary shortcut chain into a labeled n-vertex graph

This module realizes the already verified chain-cycle witnesses on `Fin n`.
The ambient graph contains the ordinary `n`-cycle and the embedded shortcut
construction.  This is a reusable graph-level bridge; edge-count optimization
and the recursive chords for the short lengths are handled separately.
-/

namespace Erdos1016.Extremal

open SimpleGraph

/-- Two simple paths with the same pair of distinct endpoints form a simple
cycle when their interiors and edge lists are disjoint. -/
theorem append_cycle_of_disjoint_paths {V : Type*} (G : SimpleGraph V)
    {u v : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hedges : List.Disjoint p.edges q.edges)
    (hsupport : List.Disjoint p.support.tail q.support.tail) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_append]
    exact List.nodup_append.mpr ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, hedges⟩
  · intro hnil
    have hlen := congrArg Walk.length hnil
    rw [Walk.length_append, Walk.length_nil] at hlen
    have hpzero : p.length = 0 := by omega
    have hpnil : p.Nil := (Walk.nil_iff_length_eq).2 hpzero
    exact huv hpnil.eq
  · rw [Walk.tail_support_append]
    exact List.nodup_append.mpr
      ⟨hp.support_nodup.tail, hq.support_nodup.tail, hsupport⟩

def shortcutEmbedding (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) :
    ShortcutVertex j → Fin n := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hn⟩

theorem shortcutEmbedding_injective (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) :
  Function.Injective (shortcutEmbedding n j hn) := by
  intro x y h
  have hv := congrArg Fin.val h
  exact Fin.ext (by simpa [shortcutEmbedding] using hv)

/-- The ordinary `n`-cycle together with an embedded copy of the closed
binary shortcut chain. -/
def shortcutCycleGraph (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) : SimpleGraph (Fin n) where
  Adj v w := (cycleGraph n).Adj v w ∨
    (v.val + 1 = w.val ∨ w.val + 1 = v.val ∨
      (2 ≤ n ∧ v.val + 1 = n ∧ w.val = 0) ∨
      (2 ≤ n ∧ w.val + 1 = n ∧ v.val = 0)) ∨
    (∃ x y : ShortcutVertex j,
      shortcutEmbedding n j hn x = v ∧ shortcutEmbedding n j hn y = w ∧
        (closedShortcutGraph j).Adj x y)
  loopless := by
    intro v h
    rcases h with h | h
    · exact (cycleGraph n).loopless v h
    · rcases h with h | ⟨x, y, hv, hw, hxy⟩
      · rcases h with h | h | h | h
        · omega
        · omega
        · omega
        · omega
      · have hxy' : x = y := shortcutEmbedding_injective n j hn (hv.trans hw.symm)
        subst y
        exact (closedShortcutGraph j).loopless x hxy
  symm := by
    intro v w h
    rcases h with h | h
    · exact Or.inl ((cycleGraph n).symm h)
    · rcases h with h | ⟨x, y, hv, hw, hxy⟩
      · rcases h with h | h | h | h
        · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2⟩))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2⟩))))
      · exact Or.inr (Or.inr ⟨y, x, hw, hv, (closedShortcutGraph j).symm hxy⟩)

private theorem shortcutCycleGraph_step_adj (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) (b : ℕ) (hb : b + 1 < n) :
    (shortcutCycleGraph n j hn hn2).Adj ⟨b, by omega⟩ ⟨b + 1, hb⟩ :=
  Or.inr (Or.inl (Or.inl rfl))

private theorem shortcutCycleGraph_wrap_adj (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) (b : ℕ) (hb : b < n) (heq : b + 1 = n) :
    (shortcutCycleGraph n j hn hn2).Adj ⟨b, hb⟩ ⟨0, by omega⟩ := by
  apply Or.inr
  apply Or.inl
  apply Or.inr
  apply Or.inr
  exact Or.inl ⟨hn2, heq, rfl⟩

private def longReturnAux (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) :
    (b t : ℕ) → (h : b + t + 1 = n) →
      (shortcutCycleGraph n j hn hn2).Walk ⟨b, by omega⟩ ⟨0, by omega⟩
  | b, 0, h => Walk.cons (shortcutCycleGraph_wrap_adj n j hn hn2 b (by omega) (by omega)) Walk.nil
  | b, t + 1, h => Walk.cons (shortcutCycleGraph_step_adj n j hn hn2 b (by omega))
      (longReturnAux n j hn hn2 (b + 1) t (by omega))
termination_by b t h => t
decreasing_by exact Nat.lt_succ_self _

/-- The long arc of the n-cycle from a chain boundary `b` forward to zero. -/
def longReturnArc (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n)
    (b : ℕ) (hb : b < n) :
    (shortcutCycleGraph n j hn hn2).Walk ⟨b, hb⟩ ⟨0, by omega⟩ := by
  let t := n - b - 1
  have heq : b + t + 1 = n := by dsimp [t]; omega
  exact (longReturnAux n j hn hn2 b t heq).copy
    (Fin.ext (by simp [t, Nat.sub_sub])) rfl

private theorem longReturnAux_length (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) :
    ∀ b t h, (longReturnAux n j hn hn2 b t h).length = t + 1 := by
  intro b t
  induction t generalizing b with
  | zero => intro h; simp [longReturnAux, Walk.length_cons]
  | succ t ih =>
      intro h
      simp only [longReturnAux, Walk.length_cons]
      rw [ih (b + 1) (by omega)]

theorem longReturnArc_length (n j : ℕ) (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n)
    (b : ℕ) (hb : b < n) :
    (longReturnArc n j hn hn2 b hb).length = n - b := by
  simp [longReturnArc, longReturnAux_length]
  omega

private theorem longReturnAux_support_lower (n j : ℕ)
    (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) :
    ∀ b t h {x : Fin n}, x ∈ (longReturnAux n j hn hn2 b t h).support →
      x.val = 0 ∨ b ≤ x.val := by
  intro b t
  induction t generalizing b with
  | zero =>
      intro h x hx
      simp only [longReturnAux, Walk.support_cons, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        exact Or.inr (Nat.le_refl _)
      · have hx' : x = (⟨0, by omega⟩ : Fin n) := by simpa using hx
        exact Or.inl (congrArg Fin.val hx')
  | succ t ih =>
      intro h x hx
      simp only [longReturnAux, Walk.support_cons, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        exact Or.inr (Nat.le_refl _)
      · have hlow := ih (b + 1) (by omega) hx
        rcases hlow with hz | hle
        · exact Or.inl hz
        · exact Or.inr (by omega)

theorem longReturnArc_support_lower (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) (b : ℕ) (hb : b < n) {x : Fin n}
    (hx : x ∈ (longReturnArc n j hn hn2 b hb).support) : x.val = 0 ∨ b ≤ x.val := by
  have h := longReturnAux_support_lower n j hn hn2 b (n - b - 1) (by omega) hx
  simpa [longReturnArc] using h

private theorem longReturnAux_isPath (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) : ∀ b t h, 0 < b →
      (longReturnAux n j hn hn2 b t h).IsPath := by
  intro b t
  induction t generalizing b with
  | zero =>
      intro h hb
      simp [longReturnAux, Walk.isPath_def, Fin.ext_iff]
      omega
  | succ t ih =>
      intro h hb
      rw [longReturnAux]
      apply (Walk.cons_isPath_iff _ _).2
      constructor
      · exact ih (b + 1) (by omega) (by omega)
      · intro hx
        have hx' : (⟨b, by omega⟩ : Fin n) ∈
            (longReturnAux n j hn hn2 (b + 1) t (by omega)).support := hx
        have hlow := longReturnAux_support_lower n j hn hn2 (b + 1) t (by omega)
          (x := ⟨b, by omega⟩) hx'
        rcases hlow with hzero | hge
        · have : b = 0 := by simpa using hzero
          omega
        · have : b + 1 ≤ b := by simpa using hge
          omega

theorem longReturnArc_isPath (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) (b : ℕ) (hb : b < n) (hb0 : 0 < b) :
    (longReturnArc n j hn hn2 b hb).IsPath := by
  unfold longReturnArc
  have hp := longReturnAux_isPath n j hn hn2 b (n - b - 1) (by omega) hb0
  exact (Walk.isPath_copy _ _ _).2 hp

theorem longReturnArc_tail_lower (n j : ℕ) (hn : shortcutSize j + 1 ≤ n)
    (hn2 : 2 ≤ n) (b : ℕ) (hb : b < n) (hb0 : 0 < b)
    {x : Fin n} (hx : x ∈ (longReturnArc n j hn hn2 b hb).support.tail) :
    x.val = 0 ∨ b < x.val := by
  have hpath := longReturnArc_isPath n j hn hn2 b hb hb0
  have hstart : (⟨b, hb⟩ : Fin n) ∉ (longReturnArc n j hn hn2 b hb).support.tail := by
    have hnodd := hpath.support_nodup
    rw [Walk.support_eq_cons] at hnodd
    exact (List.nodup_cons.mp hnodd).1
  have hlow := longReturnArc_support_lower n j hn hn2 b hb (List.mem_of_mem_tail hx)
  rcases hlow with hz | hle
  · exact Or.inl hz
  · by_cases heq : x.val = b
    · have hxstart : x = ⟨b, hb⟩ := Fin.ext heq
      exact False.elim (hstart (hxstart ▸ hx))
    · exact Or.inr (lt_of_le_of_ne hle (Ne.symm heq))

private theorem longReturnAux_edge_escape (n j : ℕ)
    (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) (B : ℕ) (hBn : B + 1 < n) :
    ∀ b t h, B ≤ b → ∀ {e : Sym2 (Fin n)},
      e ∈ (longReturnAux n j hn hn2 b t h).edges →
        ∃ a c : Fin n, e = s(a, c) ∧ (B < a.val ∨ B < c.val) := by
  intro b t
  induction t generalizing b with
  | zero =>
      intro h hb e he
      simp only [longReturnAux, Walk.edges_cons, List.mem_cons, Walk.edges_nil] at he
      rcases he with he | he
      · subst e
        refine ⟨⟨b, by omega⟩, ⟨0, by omega⟩, rfl, ?_⟩
        left
        have hbn : b + 1 = n := by omega
        change B < b
        omega
      · simp at he
  | succ t ih =>
      intro h hb e he
      simp only [longReturnAux, Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        refine ⟨⟨b, by omega⟩, ⟨b + 1, by omega⟩, rfl, ?_⟩
        right
        change B < b + 1
        omega
      · exact ih (b + 1) (by omega) (by omega) he

theorem longReturnArc_edge_escape (n j : ℕ)
    (hn : shortcutSize j + 1 ≤ n) (hn2 : 2 ≤ n) (B : ℕ)
    (hBn : B + 1 < n) : ∀ {e : Sym2 (Fin n)},
      e ∈ (longReturnArc n j hn hn2 B (by omega)).edges →
        ∃ a c : Fin n, e = s(a, c) ∧ (B < a.val ∨ B < c.val) := by
  intro e he
  have h := longReturnAux_edge_escape n j hn hn2 B hBn B (n - B - 1) (by omega)
    (by omega) (e := e) (by simpa [longReturnArc, Walk.edges_copy] using he)
  exact h

/-- The complementary long-arc cycles in the embedded n-cycle construction.
The one-vertex-slack case is handled by the short interval theorem, so this
statement assumes the return arc has at least two edges. -/
theorem longShortcut_cycle_interval_on_fin (n j c : ℕ)
    (hn : shortcutSize j + 2 ≤ n) (hj : 2 ≤ j)
    (hlo : n - 2 ^ j + 1 ≤ c) (hhi : c ≤ n) :
    Erdos1016.Problem1016.HasCycleLength
      (shortcutCycleGraph n j (by omega) (by omega)) c := by
  let B := shortcutSize j
  let ell := c - (n - B)
  have hBformula : B = 2 ^ j + j - 1 := by
    dsimp [B]
    exact shortcutSize_eq j
  have hBpos : 0 < B := by
    have h := shortcutBoundary_strictMono (show 0 < j by omega)
    simpa [B, shortcutSize, shortcutBoundary_zero] using h
  have hellow : j ≤ ell := by dsimp [ell]; omega
  have helhi : ell < j + 2 ^ j := by dsimp [ell]; omega
  obtain ⟨pSrc, hpSrc, hlenSrc, _havoid⟩ :=
    selectedChainPath_family j ell hj hellow helhi
  let hom : binaryShortcutGraph j →g shortcutCycleGraph n j (by omega) (by omega) :=
    { toFun := shortcutEmbedding n j (by omega)
      map_rel' := by
        intro a b hab
        exact Or.inr (Or.inr ⟨a, b, rfl, rfl, Or.inl hab⟩) }
  have hzero : hom (shortcutVertex j 0 (by omega)) = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    change shortcutBoundary 0 = 0
    exact shortcutBoundary_zero
  have hboundary : hom (shortcutVertex j j (by omega)) = (⟨B, by omega⟩ : Fin n) := by
    apply Fin.ext
    change shortcutBoundary j = B
    rfl
  let pMap := pSrc.map hom
  let p := pMap.copy hzero hboundary
  let q := longReturnArc n j (by omega) (by omega) B (by omega)
  have hp : p.IsPath := by
    exact (Walk.isPath_copy pMap hzero hboundary).2
      (Walk.map_isPath_of_injective
        (shortcutEmbedding_injective n j (by omega)) hpSrc)
  have hq : q.IsPath := by
    exact longReturnArc_isPath n j (by omega) (by omega) B (by omega) hBpos
  have hpBound : ∀ x ∈ p.support, x.val ≤ B := by
    intro x hx
    have hx' : x ∈ pMap.support := by simpa [p] using hx
    simp only [pMap, Walk.support_map, List.mem_map] at hx'
    rcases hx' with ⟨y, hy, hxy⟩
    have hv : x.val = y.val := congrArg Fin.val hxy.symm
    have hylt : y.val < shortcutSize j + 1 := y.isLt
    omega
  have hstart : (⟨0, by omega⟩ : Fin n) ∉ p.support.tail := by
    have hnodup := hp.support_nodup
    rw [Walk.support_eq_cons] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hsupport : List.Disjoint p.support.tail q.support.tail := by
    intro x hx hy
    have hxle := hpBound x (List.mem_of_mem_tail hx)
    have hqtail := longReturnArc_tail_lower n j (by omega) (by omega) B (by omega)
      (by omega) hy
    rcases hqtail with hzero' | hlarge
    · have hxzero : x = (⟨0, by omega⟩ : Fin n) := Fin.ext hzero'
      rw [hxzero] at hx
      exact hstart hx
    · omega
  have hescape : ∀ {e : Sym2 (Fin n)}, e ∈ q.edges →
      ∃ a c : Fin n, e = s(a, c) ∧ (B < a.val ∨ B < c.val) := by
    intro e he
    exact longReturnArc_edge_escape n j (by omega) (by omega) B (by omega) he
  have hedges : List.Disjoint p.edges q.edges := by
    intro e heP heQ
    obtain ⟨a, b, rfl, hab⟩ := hescape heQ
    rcases hab with ha | hb
    · have haP := Walk.fst_mem_support_of_mem_edges p heP
      have hbound := hpBound a haP
      omega
    · have hbP := Walk.snd_mem_support_of_mem_edges p heP
      have hbound := hpBound b hbP
      omega
  have hdistinct : (⟨0, by omega⟩ : Fin n) ≠ (⟨B, by omega⟩ : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hlenp : p.length = ell := by
    simp [p, pMap, Walk.length_copy, hlenSrc]
  have hlen : (p.append q).length = c := by
    rw [Walk.length_append, hlenp, longReturnArc_length]
    dsimp [ell]
    omega
  refine ⟨⟨0, by omega⟩, p.append q, ?_, hlen⟩
  exact append_cycle_of_disjoint_paths _ p q hp hq hdistinct hedges hsupport



end Erdos1016.Extremal

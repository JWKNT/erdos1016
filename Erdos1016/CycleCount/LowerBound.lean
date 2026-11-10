import Erdos1016.CycleCount.Statement
import Erdos1016.Extremal.Construction.ShortcutChain

set_option autoImplicit false

/-!
# A graph with many cycles

The closed binary shortcut chain with `j` shortcuts has cyclomatic number
`j + 1` and at least `2^j` cycles. Its cycles through the closing edge have
`2^j` different lengths. This is the elementary lower bound that matches the
cycle-count bound.
-/

noncomputable section

namespace Erdos1016.CycleCount
open Erdos1016.Extremal

/-- A cycle walk has as many edges as its length. -/
theorem cycle_edgeSet_ncard {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    ({a | a ∈ p.edges} : Set (Sym2 V)).ncard = p.length := by
  classical
  have h1 : ({a | a ∈ p.edges} : Set (Sym2 V)) = ↑p.edges.toFinset := by
    ext a
    simp
  rw [h1, Set.ncard_coe_Finset, List.toFinset_card_of_nodup hp.1.1.edges_nodup,
    SimpleGraph.Walk.length_edges]

/-- Cycles of all lengths in an interval give at least that many cycles. -/
theorem numCycles_ge_of_cycle_lengths {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a b : ℕ) (h : ∀ c, a ≤ c → c ≤ b → Problem1016.HasCycleLength G c) :
    b + 1 - a ≤ numCycles G := by
  classical
  have hex : ∀ c : ℕ, ∃ s : Set (Sym2 V),
      a ≤ c → c ≤ b → s ∈ cycleEdgeSets G ∧ s.ncard = c := by
    intro c
    by_cases hc : a ≤ c ∧ c ≤ b
    · obtain ⟨v, p, hp, hlen⟩ := h c hc.1 hc.2
      exact ⟨{x | x ∈ p.edges},
        fun _ _ => ⟨⟨v, p, hp, rfl⟩, (cycle_edgeSet_ncard p hp).trans hlen⟩⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose s hs using hex
  have hsub : s '' (↑(Finset.Icc a b) : Set ℕ) ⊆ cycleEdgeSets G := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := Finset.mem_Icc.mp hc
    exact (hs c hc'.1 hc'.2).1
  have hinj : Set.InjOn s (↑(Finset.Icc a b) : Set ℕ) := by
    intro c hc c' hc' heq
    have h1 := Finset.mem_Icc.mp hc
    have h2 := Finset.mem_Icc.mp hc'
    have e1 := (hs c h1.1 h1.2).2
    have e2 := (hs c' h2.1 h2.2).2
    rw [heq] at e1
    exact e1.symm.trans e2
  have hfin : (cycleEdgeSets G).Finite := Set.toFinite _
  calc b + 1 - a = (Finset.Icc a b).card := by simp
    _ = (s '' (↑(Finset.Icc a b) : Set ℕ)).ncard := by
      rw [Set.ncard_image_of_injOn hinj, Set.ncard_coe_Finset]
    _ ≤ (cycleEdgeSets G).ncard := Set.ncard_le_ncard hsub hfin

/-- The closed shortcut chain is connected. -/
theorem closedShortcutGraph_connected (j : ℕ) : (closedShortcutGraph j).Connected := by
  have hreach : ∀ (a : ℕ) (ha : a < shortcutSize j + 1),
      (closedShortcutGraph j).Reachable ⟨0, by omega⟩ ⟨a, ha⟩ := by
    intro a
    induction a with
    | zero =>
      intro ha
      exact SimpleGraph.Reachable.refl _
    | succ a ih =>
      intro ha
      have hadj : (closedShortcutGraph j).Adj ⟨a, by omega⟩ ⟨a + 1, ha⟩ :=
        Or.inl (Or.inl rfl)
      exact (ih (by omega)).trans hadj.reachable
  exact
    { preconnected := fun u v => (hreach u.1 u.2).symm.trans (hreach v.1 v.2)
      nonempty := ⟨⟨0, by omega⟩⟩ }

/-- The closed shortcut chain has at most `shortcutSize j + j + 1` edges. -/
theorem closedShortcutGraph_edge_card_le (j : ℕ) :
    Nat.card (closedShortcutGraph j).edgeSet ≤ shortcutSize j + j + 1 := by
  classical
  let S1 : Finset (Sym2 (ShortcutVertex j)) :=
    (Finset.univ : Finset (Fin (shortcutSize j))).image
      fun a => s((⟨a.1, by omega⟩ : ShortcutVertex j), ⟨a.1 + 1, by omega⟩)
  let S2 : Finset (Sym2 (ShortcutVertex j)) :=
    (Finset.univ : Finset (Fin j)).image
      fun i => s(shortcutVertex j i.1 (Nat.le_of_lt i.2),
        shortcutVertex j (i.1 + 1) (Nat.succ_le_of_lt i.2))
  let S3 : Finset (Sym2 (ShortcutVertex j)) :=
    {s(shortcutVertex j 0 (Nat.zero_le j), shortcutVertex j j le_rfl)}
  have hcons : ∀ v w : ShortcutVertex j, v.val + 1 = w.val → s(v, w) ∈ S1 := by
    intro v w h
    refine Finset.mem_image.mpr ⟨⟨v.val, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    exact Prod.ext (Fin.ext rfl) (Fin.ext h)
  have hshort : ∀ (v w : ShortcutVertex j) (i : ℕ), i < j →
      v.val = shortcutBoundary i → w.val = shortcutBoundary (i + 1) → s(v, w) ∈ S2 := by
    intro v w i hi hv hw
    refine Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    congr 1
    exact Prod.ext (Fin.ext hv.symm) (Fin.ext hw.symm)
  have hends : ∀ v w : ShortcutVertex j, v.val = 0 → w.val = shortcutBoundary j →
      s(v, w) ∈ S3 := by
    intro v w hv hw
    refine Finset.mem_singleton.mpr ?_
    congr 1
    refine Prod.ext (Fin.ext ?_) (Fin.ext hw)
    simp [shortcutVertex, shortcutBoundary_zero, hv]
  have hsub : (closedShortcutGraph j).edgeSet ⊆ (↑(S1 ∪ S2 ∪ S3) : Set _) := by
    intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro v w hvw
    have hadj : (closedShortcutGraph j).Adj v w := hvw
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    rcases hadj with (h | h | ⟨i, hi, h | h⟩) | ⟨_, h | h⟩
    · exact Or.inl (Or.inl (hcons v w h))
    · exact Or.inl (Or.inl (Sym2.eq_swap ▸ hcons w v h))
    · exact Or.inl (Or.inr (hshort v w i hi h.1 h.2))
    · exact Or.inl (Or.inr (Sym2.eq_swap ▸ hshort w v i hi h.1 h.2))
    · exact Or.inr (hends v w h.1 h.2)
    · exact Or.inr (Sym2.eq_swap ▸ hends w v h.1 h.2)
  have hcard : (S1 ∪ S2 ∪ S3).card ≤ shortcutSize j + j + 1 := by
    have h1 : S1.card ≤ shortcutSize j := by
      refine (Finset.card_image_le).trans ?_
      simp
    have h2 : S2.card ≤ j := by
      refine (Finset.card_image_le).trans ?_
      simp
    have h3 : S3.card = 1 := Finset.card_singleton _
    have hu1 := Finset.card_union_le (S1 ∪ S2) S3
    have hu2 := Finset.card_union_le S1 S2
    omega
  rw [Set.Nat.card_coe_set_eq]
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
    (by rw [Set.ncard_coe_Finset]; exact hcard)

/-- For `j ≥ 2`, the closed shortcut chain has cyclomatic number `j + 1` and
at least `2^j` cycles. -/
theorem exists_graph_many_cycles (j : ℕ) (hj : 2 ≤ j) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (j + 1) + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent ∧
      2 ^ j ≤ numCycles G := by
  refine ⟨shortcutSize j + 1, closedShortcutGraph j, ?_, ?_⟩
  · have hE := physical_euler (closedShortcutGraph j)
    have hconn := closedShortcutGraph_connected j
    have hcomp : Nat.card (closedShortcutGraph j).ConnectedComponent = 1 := by
      haveI : Subsingleton (closedShortcutGraph j).ConnectedComponent :=
        hconn.preconnected.subsingleton_connectedComponent
      haveI : Nonempty (closedShortcutGraph j).ConnectedComponent :=
        ⟨(closedShortcutGraph j).connectedComponentMk ⟨0, by omega⟩⟩
      exact Nat.card_of_subsingleton
        ((closedShortcutGraph j).connectedComponentMk ⟨0, by omega⟩)
    have hedges := closedShortcutGraph_edge_card_le j
    have hmany : 2 ^ j ≤ numCycles (closedShortcutGraph j) := by
      have h := numCycles_ge_of_cycle_lengths (closedShortcutGraph j) (j + 1) (2 ^ j + j)
        (fun c h1 h2 => closedShortcut_cycle_interval j c hj h1 h2)
      omega
    have hlt := numCycles_lt_two_pow (closedShortcutGraph j) _ hE
    have hpow : 2 ^ j < 2 ^ (Problem1016.physicalOfSimpleGraph (closedShortcutGraph j)).cycleRank :=
      lt_of_le_of_lt hmany hlt
    have hjr : j < (Problem1016.physicalOfSimpleGraph (closedShortcutGraph j)).cycleRank :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow
    omega
  · have h := numCycles_ge_of_cycle_lengths (closedShortcutGraph j) (j + 1) (2 ^ j + j)
      (fun c h1 h2 => closedShortcut_cycle_interval j c hj h1 h2)
    omega

end Erdos1016.CycleCount

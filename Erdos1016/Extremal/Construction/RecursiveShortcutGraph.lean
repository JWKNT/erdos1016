import Erdos1016.Extremal.Construction.RecursiveCycleIntervals
import Erdos1016.Extremal.Construction.ShortcutCycleEmbedding
import Erdos1016.Extremal.LogarithmComparison
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

/-!
# One merged graph for the recursive closure construction

The additional edges are stored as a single finite set: the `k` segment
shortcuts and one closing chord at the main level and each recursive level.
The ambient n-cycle supplies all ordinary chain edges.
-/

namespace Erdos1016.Extremal

open SimpleGraph

/-- The residue representative of an integer on the labeled cycle. -/
def cyclePosition (n a : ℕ) (hn : 0 < n) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩



/-- Segment shortcut chords on the n-cycle, together with the main and
recursive closing chords. -/
def recursiveShortcutExtraEdges (n k : ℕ) (hn : shortcutSize k + 1 ≤ n) :
    Finset (Sym2 (Fin n)) := by
  let hnp : 0 < n := by omega
  let seg := (Finset.range k).image fun i =>
    s(cyclePosition n (shortcutBoundary i) hnp,
      cyclePosition n (shortcutBoundary (i + 1)) hnp)
  let lev := (k :: recursiveClosureLevels k).toFinset
  let close := lev.image fun m =>
    s(cyclePosition n 0 hnp, cyclePosition n (shortcutBoundary m) hnp)
  exact seg ∪ close

/-- The n-cycle augmented by precisely the chords in
`recursiveShortcutExtraEdges`. -/
def recursiveShortcutGraph (n k : ℕ) (hn : shortcutSize k + 1 ≤ n) : SimpleGraph (Fin n) :=
  SimpleGraph.cycleGraph n ⊔ SimpleGraph.fromEdgeSet
    (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n)))

theorem recursiveShortcutExtraEdges_card_le (n k : ℕ)
    (hn : shortcutSize k + 1 ≤ n) :
    (recursiveShortcutExtraEdges n k hn).card ≤
      k + (recursiveClosureLevels k).length + 1 := by
  classical
  let hnp : 0 < n := by omega
  let seg := (Finset.range k).image fun i =>
    s(cyclePosition n (shortcutBoundary i) hnp,
      cyclePosition n (shortcutBoundary (i + 1)) hnp)
  let lev := (k :: recursiveClosureLevels k).toFinset
  let close := lev.image fun m =>
    s(cyclePosition n 0 hnp, cyclePosition n (shortcutBoundary m) hnp)
  change (seg ∪ close).card ≤ k + (recursiveClosureLevels k).length + 1
  calc
    _ ≤ seg.card + close.card := Finset.card_union_le _ _
    _ ≤ k + (k :: recursiveClosureLevels k).length := by
      apply Nat.add_le_add
      · dsimp [seg]
        exact Finset.card_image_le.trans_eq (Finset.card_range k)
      · dsimp [close, lev]
        exact Finset.card_image_le.trans (List.toFinset_card_le _)
    _ = k + (recursiveClosureLevels k).length + 1 := by simp [Nat.add_assoc]

private theorem recursiveSegmentChord_mem (n k i : ℕ) (hn : shortcutSize k + 1 ≤ n)
    (hi : i < k) :
    s(cyclePosition n (shortcutBoundary i) (by omega),
      cyclePosition n (shortcutBoundary (i + 1)) (by omega)) ∈
        recursiveShortcutExtraEdges n k hn := by
  classical
  unfold recursiveShortcutExtraEdges
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
  rfl

private theorem recursiveCloseChord_mem (n k m : ℕ) (hn : shortcutSize k + 1 ≤ n)
    (hm : m ∈ k :: recursiveClosureLevels k) :
    s(cyclePosition n 0 (by omega),
      cyclePosition n (shortcutBoundary m) (by omega)) ∈
        recursiveShortcutExtraEdges n k hn := by
  classical
  unfold recursiveShortcutExtraEdges
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  refine ⟨m, List.mem_toFinset.mpr hm, ?_⟩
  rfl


lemma two_mem_recursiveClosureLevels_cons {k : ℕ} (hk : 2 ≤ k) :
    2 ∈ k :: recursiveClosureLevels k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hsmall : k ≤ 2
      · have hk2 : k = 2 := by omega
        subst k
        simp [recursiveClosureLevels]
      · have hbig : 2 < k := by omega
        let m := Nat.clog 2 k
        have hmLt : m < k := by dsimp [m]; exact clog_two_lt_self hbig
        have hmTwo : 2 ≤ m := by dsimp [m]; exact two_le_clog_two hbig
        have hrec := ih m hmLt hmTwo
        have hdef : recursiveClosureLevels k = recursiveClosureLevels m ++ [m] := by
          dsimp [m]
          rw [recursiveClosureLevels.eq_1, if_neg (by omega)]
        apply List.mem_cons.mpr
        right
        rw [hdef]
        rcases List.mem_cons.mp hrec with heq | hmem
        · exact List.mem_append.mpr (Or.inr (by simpa using heq) )
        · exact List.mem_append.mpr (Or.inl hmem)

/-- Every closed shortcut chain at one of the selected levels embeds into the
single graph carrying all recursive chords. -/
def closedShortcutGraphToRecursive (n k m : ℕ)
    (hn : shortcutSize k + 1 ≤ n) (hmk : m ≤ k)
    (hmMem : m ∈ k :: recursiveClosureLevels k) :
    closedShortcutGraph m →g recursiveShortcutGraph n k hn := by
  let hnm : shortcutSize m + 1 ≤ n := by
    have hsize : shortcutSize m ≤ shortcutSize k := shortcutBoundary_mono hmk
    omega
  let f := shortcutEmbedding n m hnm
  refine ⟨f, ?_⟩
  intro v w hadj
  have hne : v ≠ w := by
    intro hvw
    subst w
    exact (closedShortcutGraph m).loopless v hadj
  rcases hadj with hadj | ⟨hm2, hclose⟩
  · rcases hadj with hstep | hstep | ⟨i, hi, hshortcut⟩
    · have hpath : (SimpleGraph.pathGraph n).Adj (f v) (f w) := by
        rw [SimpleGraph.pathGraph_adj]
        left
        simpa [f, shortcutEmbedding] using hstep
      exact Or.inl (SimpleGraph.pathGraph_le_cycleGraph hpath)
    · have hpath : (SimpleGraph.pathGraph n).Adj (f v) (f w) := by
        rw [SimpleGraph.pathGraph_adj]
        right
        simpa [f, shortcutEmbedding] using hstep
      exact Or.inl (SimpleGraph.pathGraph_le_cycleGraph hpath)
    · have hiK : i < k := lt_of_lt_of_le hi hmk
      have hboundi : shortcutBoundary i < n := by
        have hb : shortcutBoundary i ≤ shortcutSize k := by
          unfold shortcutSize
          exact shortcutBoundary_mono (Nat.le_of_lt (lt_of_lt_of_le hi hmk))
        omega
      have hboundis : shortcutBoundary (i + 1) < n := by
        have hb : shortcutBoundary (i + 1) ≤ shortcutSize k := by
          unfold shortcutSize
          exact shortcutBoundary_mono (Nat.succ_le_of_lt hiK)
        omega
      have hmemBase := recursiveSegmentChord_mem n k i hn hiK
      have hmem : s(f v, f w) ∈ recursiveShortcutExtraEdges n k hn := by
        rcases hshortcut with ⟨hv, hw⟩ | ⟨hw, hv⟩
        · have hvi : f v = cyclePosition n (shortcutBoundary i) (by omega) := by
            apply Fin.ext
            simp [f, shortcutEmbedding, cyclePosition, hv, Nat.mod_eq_of_lt hboundi]
          have hwi : f w = cyclePosition n (shortcutBoundary (i + 1)) (by omega) := by
            apply Fin.ext
            simp [f, shortcutEmbedding, cyclePosition, hw, Nat.mod_eq_of_lt hboundis]
          simpa [hvi, hwi] using hmemBase
        · have hwi : f w = cyclePosition n (shortcutBoundary i) (by omega) := by
            apply Fin.ext
            simp [f, shortcutEmbedding, cyclePosition, hw, Nat.mod_eq_of_lt hboundi]
          have hvi : f v = cyclePosition n (shortcutBoundary (i + 1)) (by omega) := by
            apply Fin.ext
            simp [f, shortcutEmbedding, cyclePosition, hv, Nat.mod_eq_of_lt hboundis]
          rw [hvi, hwi, Sym2.eq_swap]
          exact hmemBase
      exact Or.inr ((SimpleGraph.fromEdgeSet_adj (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n)))).mpr ⟨by
        exact hmem, by
        intro heq
        apply hne
        exact (shortcutEmbedding_injective n m hnm) (by simpa [f] using heq)⟩)
  · have hboundm : shortcutBoundary m < n := by
      have hb : shortcutBoundary m ≤ shortcutSize k := by
        unfold shortcutSize
        exact shortcutBoundary_mono hmk
      omega
    have hmemBase := recursiveCloseChord_mem n k m hn hmMem
    have hmem : s(f v, f w) ∈ recursiveShortcutExtraEdges n k hn := by
      rcases hclose with ⟨hv, hw⟩ | ⟨hw, hv⟩
      · have hvi : f v = cyclePosition n 0 (by omega) := by
          apply Fin.ext
          simp [f, shortcutEmbedding, cyclePosition, hv]
        have hwi : f w = cyclePosition n (shortcutBoundary m) (by omega) := by
          apply Fin.ext
          simp [f, shortcutEmbedding, cyclePosition, hw, Nat.mod_eq_of_lt hboundm]
        simpa [hvi, hwi] using hmemBase
      · have hwi : f w = cyclePosition n 0 (by omega) := by
          apply Fin.ext
          simp [f, shortcutEmbedding, cyclePosition, hw]
        have hvi : f v = cyclePosition n (shortcutBoundary m) (by omega) := by
          apply Fin.ext
          simp [f, shortcutEmbedding, cyclePosition, hv, Nat.mod_eq_of_lt hboundm]
        rw [hvi, hwi, Sym2.eq_swap]
        exact hmemBase
    exact Or.inr ((SimpleGraph.fromEdgeSet_adj (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n)))).mpr ⟨by
      exact hmem, by
      intro heq
      apply hne
      exact (shortcutEmbedding_injective n m hnm) (by simpa [f] using heq)⟩)

private theorem cycleGraph_wrap_adj {n : ℕ} (hn : 2 ≤ n) {v w : Fin n}
    (hv : v.val + 1 = n) (hw : w.val = 0) : (SimpleGraph.cycleGraph n).Adj v w := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  have hInt : ((w - v).val : ℤ) = 1 := by
    rw [Fin.intCast_val_sub_eq_sub_add_ite]
    have hv' : (v.val : ℤ) + 1 = n := by exact_mod_cast hv
    have hw' : (w.val : ℤ) = 0 := by exact_mod_cast hw
    have hnot : ¬ v ≤ w := by
      intro hle
      have hle' := Fin.le_iff_val_le_val.mp hle
      omega
    simp only [hnot, if_false]
    omega
  exact_mod_cast hInt

/-- The long-arc ambient shortcut graph is a subgraph of the merged graph. -/
def shortcutCycleGraphToRecursive (n k : ℕ) (hn : shortcutSize k + 1 ≤ n)
    (hn2 : 2 ≤ n) :
    shortcutCycleGraph n k hn hn2 →g recursiveShortcutGraph n k hn := by
  let hmem : k ∈ k :: recursiveClosureLevels k := by simp
  let chainHom := closedShortcutGraphToRecursive n k k hn le_rfl hmem
  refine ⟨id, ?_⟩
  intro v w hadj
  rcases hadj with hc | hrest
  · exact Or.inl hc
  · rcases hrest with hline | ⟨x, y, hx, hy, hxy⟩
    · rcases hline with h | h | h | h
      · have hp : (SimpleGraph.pathGraph n).Adj v w := by
          rw [SimpleGraph.pathGraph_adj]
          exact Or.inl h
        exact Or.inl (SimpleGraph.pathGraph_le_cycleGraph hp)
      · have hp : (SimpleGraph.pathGraph n).Adj v w := by
          rw [SimpleGraph.pathGraph_adj]
          exact Or.inr h
        exact Or.inl (SimpleGraph.pathGraph_le_cycleGraph hp)
      · exact Or.inl (cycleGraph_wrap_adj hn2 h.2.1 h.2.2)
      · exact Or.inl ((SimpleGraph.cycleGraph n).symm
          (cycleGraph_wrap_adj hn2 h.2.1 h.2.2))
    · have hmapped := chainHom.map_rel hxy
      change (recursiveShortcutGraph n k hn).Adj
        (shortcutEmbedding n k (by omega) x) (shortcutEmbedding n k (by omega) y) at hmapped
      rw [hx, hy] at hmapped
      exact hmapped


theorem recursiveShortcutGraph_gap_cycle (n k : ℕ)
    (hn : shortcutSize k + 2 ≤ n) (hk : 2 ≤ k) :
    Erdos1016.Problem1016.HasCycleLength (recursiveShortcutGraph n k (by omega))
      (n - 2 ^ k) := by
  let hnk : shortcutSize k + 1 ≤ n := by omega
  let hn2 : 2 ≤ n := by omega
  let B := shortcutSize k
  let b2 : Fin n := ⟨shortcutBoundary 2, by
    have hb : shortcutBoundary 2 ≤ shortcutSize k := by
      unfold shortcutSize
      exact shortcutBoundary_mono (by omega)
    omega⟩
  let z : Fin n := ⟨0, by omega⟩
  let hmem2 : 2 ∈ k :: recursiveClosureLevels k := two_mem_recursiveClosureLevels_cons hk
  have hgapmem := recursiveCloseChord_mem n k 2 hnk hmem2
  have hBformula : B = 2 ^ k + k - 1 := by
    dsimp [B]
    exact shortcutSize_eq k
  have hBpos : 0 < B := by
    have h := shortcutBoundary_strictMono (show 0 < k by omega)
    simpa [B, shortcutSize, shortcutBoundary_zero] using h
  have hb2pos : 0 < shortcutBoundary 2 := by
    have h := shortcutBoundary_strictMono (show 0 < 2 by omega)
    simpa [shortcutBoundary_zero] using h
  have hgap : (recursiveShortcutGraph n k hnk).Adj z b2 := by
    apply Or.inr
    apply (SimpleGraph.fromEdgeSet_adj
      (recursiveShortcutExtraEdges n k hnk : Set (Sym2 (Fin n)))).2
    constructor
    · have hg : s(cyclePosition n 0 (by omega),
          cyclePosition n (shortcutBoundary 2) (by omega)) ∈
          (recursiveShortcutExtraEdges n k hnk : Set (Sym2 (Fin n))) := by
        exact Finset.mem_coe.mpr hgapmem
      have hz : cyclePosition n 0 (by omega) = z := by
        apply Fin.ext
        simp [z, cyclePosition]
      have hb2 : cyclePosition n (shortcutBoundary 2) (by omega) = b2 := by
        apply Fin.ext
        have hb2lt : shortcutBoundary 2 < n := b2.isLt
        simp [b2, cyclePosition, Nat.mod_eq_of_lt hb2lt]
      simpa [hz, hb2] using hg
    · intro heq
      have hv := congrArg Fin.val heq
      simp [z, b2] at hv
      omega
  let chainHom : binaryShortcutGraph k →g recursiveShortcutGraph n k hnk :=
    { toFun := shortcutEmbedding n k hnk
      map_rel' := by
        intro v w hadj
        exact (closedShortcutGraphToRecursive n k k hnk le_rfl (by simp)).map_rel
          (Or.inl hadj) }
  let hsrc : 2 + (k - 2) ≤ k := by omega
  let pSrc := selectedChainWalk k (k - 2) 2 hsrc (fun _ => false)
  have hpSrc : pSrc.IsPath := selectedChainWalk_isPath k 2 (k - 2) hsrc (fun _ => false)
  have hlenSrc : pSrc.length = k - 2 := by
    simp [pSrc, selectedChainWalk_length, chosenPowerSum]
  have hstart : chainHom (shortcutVertex k 2 (by omega)) = b2 := by
    change shortcutEmbedding n k hnk (shortcutVertex k 2 (by omega)) = b2
    apply Fin.ext
    simp [shortcutEmbedding, b2, shortcutVertex]
  have hend : chainHom (shortcutVertex k (2 + (k - 2)) (by omega)) =
      ⟨B, by omega⟩ := by
    change shortcutEmbedding n k hnk (shortcutVertex k (2 + (k - 2)) (by omega)) = _
    apply Fin.ext
    have hidx : 2 + (k - 2) = k := by omega
    change shortcutBoundary (2 + (k - 2)) = shortcutSize k
    rw [hidx]
    rfl
  let pMap := pSrc.map chainHom
  let p0 := pMap.copy hstart hend
  have hp0 : p0.IsPath := by
    exact (Walk.isPath_copy pMap hstart hend).2
      (Walk.map_isPath_of_injective (shortcutEmbedding_injective n k hnk) hpSrc)
  have hp0len : p0.length = k - 2 := by
    simp [p0, pMap, hlenSrc]
  have hzeroNot : z ∉ p0.support := by
    intro hz
    have hz' : z ∈ pMap.support := by simpa [p0] using hz
    simp only [pMap, Walk.support_map, List.mem_map] at hz'
    rcases hz' with ⟨x, hx, hxeq⟩
    have hxlow := selectedChainWalk_support_lower k 2 (k - 2) hsrc (fun _ => false) hx
    have hval' := congrArg Fin.val hxeq
    change (shortcutEmbedding n k hnk x).val = z.val at hval'
    change x.val = 0 at hval'
    have hval : x.val = 0 := hval'
    have hbound : shortcutBoundary 2 ≤ x.val := by simpa [shortcutVertex] using hxlow
    omega
  let p := Walk.cons hgap p0
  have hp : p.IsPath := (Walk.cons_isPath_iff hgap p0).2 ⟨hp0, hzeroNot⟩
  have hplen : p.length = k - 1 := by simp [p, hp0len]; omega
  let qSrc := longReturnArc n k hnk hn2 B (by omega)
  let hom := shortcutCycleGraphToRecursive n k hnk hn2
  let q := qSrc.map hom
  have hq : q.IsPath := by
    exact Walk.map_isPath_of_injective Function.injective_id
      (longReturnArc_isPath n k hnk hn2 B (by omega) hBpos)
  have hfun : (hom : Fin n → Fin n) = id := rfl
  have hqLen : q.length = n - B := by simp [q, qSrc, Walk.length_map, longReturnArc_length]
  have hPbound : ∀ x ∈ p.support, x.val ≤ B := by
    intro x hx
    simp only [p, Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · subst x
      simp [z, B]
    · have hx' : x ∈ pMap.support := by simpa [p0] using hx
      simp only [pMap, Walk.support_map, List.mem_map] at hx'
      rcases hx' with ⟨y, hy, hxy⟩
      have hyupper := selectedChainWalk_support_upper k 2 (k - 2) hsrc (fun _ => false) hy
      have hval : y.val = x.val := congrArg Fin.val hxy
      have hboundary : shortcutBoundary (2 + (k - 2)) ≤ B := by
        unfold B shortcutSize
        exact shortcutBoundary_mono (by omega)
      have hyupper' : y.val ≤ shortcutBoundary (2 + (k - 2)) := by simpa [shortcutVertex] using hyupper
      omega
  have hstartNot : z ∉ p.support.tail := by
    have hnodup := hp.support_nodup
    rw [Walk.support_eq_cons] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hsupport : List.Disjoint p.support.tail q.support.tail := by
    intro x hx hy
    have hxle := hPbound x (List.mem_of_mem_tail hx)
    have hySrc : x ∈ qSrc.support.tail := by
      simpa only [q, Walk.support_map, hfun, List.map_id] using hy
    have hqtail := longReturnArc_tail_lower n k hnk hn2 B (by omega) hBpos hySrc
    rcases hqtail with hzero | hlarge
    · have hxzero : x = z := Fin.ext (by simpa [z] using hzero)
      rw [hxzero] at hx
      exact hstartNot hx
    · omega
  have hescape : ∀ {e : Sym2 (Fin n)}, e ∈ q.edges →
      ∃ a c : Fin n, e = s(a, c) ∧ (B < a.val ∨ B < c.val) := by
    intro e he
    have heSrc : e ∈ qSrc.edges := by
      simpa only [q, Walk.edges_map, hfun, Sym2.map_id, List.map_id] using he
    exact longReturnArc_edge_escape n k hnk hn2 B (by omega) heSrc
  have hedges : List.Disjoint p.edges q.edges := by
    intro e heP heQ
    obtain ⟨a, b, rfl, hab⟩ := hescape heQ
    rcases hab with ha | hb
    · have haP := Walk.fst_mem_support_of_mem_edges p heP
      have hbound := hPbound a haP
      omega
    · have hbP := Walk.snd_mem_support_of_mem_edges p heP
      have hbound := hPbound b hbP
      omega
  have hdistinct : z ≠ (⟨B, by omega⟩ : Fin n) := by
    intro h
    have hv := congrArg Fin.val h
    simp [z] at hv
    omega
  let c := n - 2 ^ k
  have hlen : (p.append q).length = c := by
    rw [Walk.length_append, hplen, hqLen]
    dsimp [c, B]
    rw [shortcutSize_eq]
    omega
  refine ⟨z, p.append q, ?_, hlen⟩
  exact append_cycle_of_disjoint_paths _ p q hp hq hdistinct hedges hsupport


theorem cycleGraph_edgeSet_ncard (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).edgeSet.ncard = n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ m =>
        classical
        have hdeg : ∀ v : Fin (m + 3),
            (SimpleGraph.cycleGraph (m + 3)).degree v = 2 := by
          intro v
          exact SimpleGraph.cycleGraph_degree_three_le
        have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges
          (SimpleGraph.cycleGraph (m + 3))
        have hsum' : (∑ v : Fin (m + 3),
            (SimpleGraph.cycleGraph (m + 3)).degree v) = 2 * (m + 3) := by
          calc
            _ = ∑ _v : Fin (m + 3), 2 := Finset.sum_congr rfl (fun v _ => hdeg v)
            _ = 2 * (m + 3) := by simp [Nat.mul_comm]
        rw [hsum'] at hsum
        have hcard : (SimpleGraph.cycleGraph (m + 3)).edgeSet.ncard =
            (SimpleGraph.cycleGraph (m + 3)).edgeFinset.card := by
          rw [SimpleGraph.edgeFinset]
          exact Set.ncard_eq_toFinset_card' _
        rw [← hcard] at hsum
        have hfinal : (SimpleGraph.cycleGraph (m + 3)).edgeSet.ncard = m + 3 := by omega
        simpa [Nat.add_assoc] using hfinal

/-- The merged edge set is contained in the union of the n-cycle and the
explicit finite chord set. -/
theorem recursiveShortcutGraph_edgeSet_ncard_le (n k : ℕ)
    (hn : shortcutSize k + 1 ≤ n) (hn3 : 3 ≤ n) :
    (recursiveShortcutGraph n k hn).edgeSet.ncard ≤
      n + (recursiveShortcutExtraEdges n k hn).card := by
  classical
  have hsub : (recursiveShortcutGraph n k hn).edgeSet ⊆
      (SimpleGraph.cycleGraph n).edgeSet ∪
        (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n))) := by
    change (SimpleGraph.cycleGraph n ⊔ SimpleGraph.fromEdgeSet
      (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n)))).edgeSet ⊆ _
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.union_subset_union_right (SimpleGraph.cycleGraph n).edgeSet
      Set.diff_subset
  calc
    _ ≤ ((SimpleGraph.cycleGraph n).edgeSet ∪
        (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n)))).ncard :=
      Set.ncard_le_ncard hsub
    _ ≤ (SimpleGraph.cycleGraph n).edgeSet.ncard +
        (recursiveShortcutExtraEdges n k hn : Set (Sym2 (Fin n))).ncard :=
      Set.ncard_union_le _ _
    _ = n + (recursiveShortcutExtraEdges n k hn).card := by
      rw [cycleGraph_edgeSet_ncard n hn3]
      simp


theorem recursiveShortcutGraph_excess_le (n k : ℕ)
    (hn : shortcutSize k + 1 ≤ n) (hn3 : 3 ≤ n) :
    Erdos1016.Problem1016.excess n (recursiveShortcutGraph n k hn) ≤
      (recursiveShortcutExtraEdges n k hn).card := by
  classical
  let G := recursiveShortcutGraph n k hn
  have hcard := recursiveShortcutGraph_edgeSet_ncard_le n k hn hn3
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  unfold Erdos1016.Problem1016.excess
  have hcardEq : Fintype.card G.edgeSet = G.edgeSet.ncard := by
    rw [← SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset]
    exact (Set.ncard_eq_toFinset_card' _).symm
  change Fintype.card G.edgeSet - n ≤ (recursiveShortcutExtraEdges n k hn).card
  rw [hcardEq]
  exact Nat.sub_le_iff_le_add.mpr (by simpa [G, Nat.add_comm] using hcard)


theorem recursiveShortcutGraph_pancyclic (k : ℕ) (hk : 2 ≤ k) :
    Erdos1016.Problem1016.IsPancyclic
      (recursiveShortcutGraph (shortcutSize k + 1) k (by omega)) := by
  intro ℓ hlo hhi
  have htop : ℓ ≤ 2 ^ k + k := by
    calc
      ℓ ≤ Fintype.card (Fin (shortcutSize k + 1)) := hhi
      _ = shortcutSize k + 1 := by simp
      _ = 2 ^ k + k := by
        rw [shortcutSize_eq]
        have hpow : 0 < 2 ^ k := Nat.pow_pos (by omega)
        have hpos : 1 ≤ 2 ^ k + k := by omega
        exact Nat.sub_add_cancel hpos
  by_cases hmain : k + 1 ≤ ℓ
  · have hn2 : 2 ≤ shortcutSize k + 1 := by
      have hsize : 2 ≤ shortcutSize k := by
        rw [shortcutSize_eq]
        have hpow : 0 < 2 ^ k := Nat.pow_pos (by omega)
        omega
      omega
    obtain ⟨v, p, hp, hlen⟩ := closedShortcut_cycle_interval k ℓ hk hmain htop
    let hom := closedShortcutGraphToRecursive (shortcutSize k + 1) k k
      (by omega) (by omega) (by simp)
    refine ⟨hom v, p.map hom, ?_, ?_⟩
    · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (shortcutEmbedding_injective (shortcutSize k + 1) k (by omega))).2 hp
    · simpa using hlen
  · obtain ⟨m, hmMem, hmlo, hmhi⟩ := recursiveClosureIntervals_cover k ℓ hk hlo htop
    have hmk : m ≤ k := by
      rcases List.mem_cons.mp hmMem with h | h
      · omega
      · exact Nat.le_of_lt (recursiveClosureLevels_mem_bounds hk h).2
    have hm2 : 2 ≤ m := by
      rcases List.mem_cons.mp hmMem with h | h
      · omega
      · exact (recursiveClosureLevels_mem_bounds hk h).1
    have hnm : shortcutSize m + 1 ≤ shortcutSize k + 1 := by
      have hsize : shortcutSize m ≤ shortcutSize k := shortcutBoundary_mono hmk
      omega
    obtain ⟨v, p, hp, hlen⟩ := closedShortcut_cycle_interval m ℓ hm2 hmlo hmhi
    let hom := closedShortcutGraphToRecursive (shortcutSize k + 1) k m
      (by omega) hmk hmMem
    refine ⟨hom v, p.map hom, ?_, ?_⟩
    · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (shortcutEmbedding_injective (shortcutSize k + 1) m hnm)).2 hp
    · simpa using hlen



theorem recursiveShortcutGraph_pancyclic_of_maximal_fit (n k : ℕ)
    (hk : 2 ≤ k) (hfit : shortcutFits n k) (hmax : ¬ shortcutFits n (k + 1)) :
    Erdos1016.Problem1016.IsPancyclic
      (recursiveShortcutGraph n k (by
        have hf : 2 ^ k + k + 1 ≤ n := by simpa [shortcutFits] using hfit
        rw [shortcutSize_eq]
        have hpowpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
        have hp : 1 ≤ 2 ^ k + k := by omega
        omega)) := by
  have hf : 2 ^ k + k + 1 ≤ n := by simpa [shortcutFits] using hfit
  let hn : shortcutSize k + 1 ≤ n := by
    rw [shortcutSize_eq]
    have hpowpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hp : 1 ≤ 2 ^ k + k := by omega
    omega
  let hnLong : shortcutSize k + 2 ≤ n := by
    rw [shortcutSize_eq]
    have hpowpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hp : 1 ≤ 2 ^ k + k := by omega
    omega
  have hn2 : 2 ≤ n := by omega
  have htop : 2 ^ k + k ≤ n := by omega
  have hmaxBound : n ≤ 2 ^ (k + 1) + k + 1 := shortcut_maximal_rounding hmax
  intro ℓ hlo hhi
  have hlen : ℓ ≤ n := by simpa using hhi
  by_cases hshort : ℓ ≤ 2 ^ k + k
  · obtain ⟨m, hmMem, hmlo, hmhi⟩ := recursiveClosureIntervals_cover k ℓ hk hlo hshort
    have hmk : m ≤ k := by
      rcases List.mem_cons.mp hmMem with h | h
      · omega
      · exact Nat.le_of_lt (recursiveClosureLevels_mem_bounds hk h).2
    have hm2 : 2 ≤ m := by
      rcases List.mem_cons.mp hmMem with h | h
      · omega
      · exact (recursiveClosureLevels_mem_bounds hk h).1
    have hnm : shortcutSize m + 1 ≤ n := by
      have hsize : shortcutSize m ≤ shortcutSize k := shortcutBoundary_mono hmk
      omega
    obtain ⟨v, p, hp, hcyclelen⟩ := closedShortcut_cycle_interval m ℓ hm2 hmlo hmhi
    let hom := closedShortcutGraphToRecursive n k m hn hmk hmMem
    refine ⟨hom v, p.map hom, ?_, ?_⟩
    · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (shortcutEmbedding_injective n m hnm)).2 hp
    · simpa using hcyclelen
  · by_cases hhigh : n - 2 ^ k + 1 ≤ ℓ
    · obtain ⟨v, p, hp, hcyclelen⟩ := longShortcut_cycle_interval_on_fin
        n k ℓ hnLong hk hhigh hlen
      let hom := shortcutCycleGraphToRecursive n k hn hn2
      refine ⟨hom v, p.map hom, ?_, ?_⟩
      · exact (SimpleGraph.Walk.map_isCycle_iff_of_injective (by
          intro a b hab
          exact hab)).2 hp
      · simpa using hcyclelen
    · have hgap : ℓ = 2 ^ k + k + 1 := by
        have hnotShort : 2 ^ k + k < ℓ := by omega
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
        omega
      have hcyclelen : n - 2 ^ k = ℓ := by
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
        omega
      obtain ⟨v, p, hp, hlenCycle⟩ := recursiveShortcutGraph_gap_cycle n k hnLong hk
      refine ⟨v, p, hp, ?_⟩
      simpa [hcyclelen] using hlenCycle

theorem pancyclic_excess_integer_upper_bound (n : ℕ) (hn : 7 ≤ n) :
    Erdos1016.Problem1016.h n ≤ n.log2 + logStar n + 1 := by
  obtain ⟨k, hk, hfit, hmax⟩ := exists_maximal_shortcut_k hn
  have hnk : shortcutSize k + 1 ≤ n := by
    have hf : 2 ^ k + k + 1 ≤ n := by simpa [shortcutFits] using hfit
    rw [shortcutSize_eq]
    have hpow : 0 < 2 ^ k := Nat.pow_pos (by decide)
    omega
  have hPan := recursiveShortcutGraph_pancyclic_of_maximal_fit n k hk hfit hmax
  have hExcess := recursiveShortcutGraph_excess_le n k hnk (by omega)
  have hExtra := recursiveShortcutExtraEdges_card_le n k hnk
  have hlevels := recursiveClosureLevels_length k
  have hbudget : k + (recursiveClosureLevels k).length + 1 ≤
      n.log2 + logStar n + 1 := by
    have hb := shortcut_added_edges_bound (by omega : 0 < n) hk hfit
    rw [← hlevels] at hb
    omega
  calc
    Erdos1016.Problem1016.h n ≤
        Erdos1016.Problem1016.excess n (recursiveShortcutGraph n k hnk) :=
      Erdos1016.Problem1016.h_le_excess_of_isPancyclic n _ hPan
    _ ≤ (recursiveShortcutExtraEdges n k hnk).card := hExcess
    _ ≤ k + (recursiveClosureLevels k).length + 1 := hExtra
    _ ≤ n.log2 + logStar n + 1 := hbudget




end Erdos1016.Extremal

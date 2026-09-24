import Erdos1016.Extremal.Construction.CycleClosure

set_option autoImplicit false

/-!
# Cumulative-index graph for the binary shortcut chain

Vertices are positions along the original chain. Segment `i` has `2^i+1`
ordinary edges, and the extra edges join its successive boundary positions.
-/

namespace Erdos1016.Extremal

open SimpleGraph

/-- Position of the boundary after the first `i` segments. -/
def shortcutBoundary (i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range i, (2 ^ t + 1)

/-- Total length of the first `j` original segments. -/
def shortcutSize (j : ℕ) : ℕ := shortcutBoundary j

lemma shortcutBoundary_zero : shortcutBoundary 0 = 0 := by simp [shortcutBoundary]

lemma shortcutBoundary_succ (i : ℕ) :
    shortcutBoundary (i + 1) = shortcutBoundary i + (2 ^ i + 1) := by
  simp [shortcutBoundary, Finset.sum_range_succ]

lemma shortcutBoundary_mono {i j : ℕ} (h : i ≤ j) :
    shortcutBoundary i ≤ shortcutBoundary j := by
  unfold shortcutBoundary
  apply Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Vertices are positions on the original chain. -/
abbrev ShortcutVertex (j : ℕ) := Fin (shortcutSize j + 1)

/-- The boundary vertex after `i` segments, when `i ≤ j`. -/
def shortcutVertex (j i : ℕ) (h : i ≤ j) : ShortcutVertex j :=
  ⟨shortcutBoundary i, by
    unfold shortcutSize
    exact Nat.lt_succ_of_le (shortcutBoundary_mono h)⟩

/-- The finite simple graph consisting of original consecutive edges and the
binary shortcut edges between adjacent segment boundaries. -/
def binaryShortcutGraph (j : ℕ) : SimpleGraph (ShortcutVertex j) where
  Adj v w :=
    v.val + 1 = w.val ∨ w.val + 1 = v.val ∨
      ∃ i, i < j ∧
        ((v.val = shortcutBoundary i ∧ w.val = shortcutBoundary (i + 1)) ∨
         (w.val = shortcutBoundary i ∧ v.val = shortcutBoundary (i + 1)))
  loopless := by
    intro v h
    rcases h with h | h | ⟨i, hi, h⟩
    · omega
    · omega
    · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have hb := shortcutBoundary_succ i
        have hp : 0 < 2 ^ i + 1 := by positivity
        omega
      · have hb := shortcutBoundary_succ i
        have hp : 0 < 2 ^ i + 1 := by positivity
        omega
  symm := by
    intro v w h
    rcases h with h | h | ⟨i, hi, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inr (Or.inr ⟨i, hi, Or.inr ⟨h₁, h₂⟩⟩)
      · exact Or.inr (Or.inr ⟨i, hi, Or.inl ⟨h₁, h₂⟩⟩)

/-- Every original edge between consecutive chain positions is present. -/
theorem original_consecutive_adj (j a : ℕ) (ha : a + 1 ≤ shortcutSize j) :
    (binaryShortcutGraph j).Adj
      ⟨a, by omega⟩ ⟨a + 1, by omega⟩ := by
  exact Or.inl rfl

/-- The graph contains the shortcut edge across each segment. -/
theorem segment_shortcut_adj (j i : ℕ) (hi : i < j) :
    (binaryShortcutGraph j).Adj
      (shortcutVertex j i (by omega))
      (shortcutVertex j (i + 1) (by omega)) := by
  apply Or.inr
  apply Or.inr
  refine ⟨i, hi, Or.inl ?_⟩
  simp [shortcutVertex]

/-- Walk along an ordinary segment, one original edge at a time. -/
def originalSegmentWalk (j : ℕ) : (n a : ℕ) → (h : a + n ≤ shortcutSize j) →
    (binaryShortcutGraph j).Walk ⟨a, by omega⟩ ⟨a + n, by omega⟩
  | 0, a, _ => Walk.nil
  | n + 1, a, h =>
      (Walk.cons (original_consecutive_adj j a (by omega))
        (originalSegmentWalk j n (a + 1) (by omega))).copy rfl (Fin.ext (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))

theorem originalSegmentWalk_length (j a n : ℕ) (h : a + n ≤ shortcutSize j) :
    (originalSegmentWalk j n a h).length = n := by
  induction n generalizing a with
  | zero => simp [originalSegmentWalk]
  | succ n ih =>
      simp [originalSegmentWalk, Walk.length_cons, ih]

theorem originalSegmentWalk_support_ge (j a n : ℕ) (h : a + n ≤ shortcutSize j)
    {x : ShortcutVertex j} (hx : x ∈ (originalSegmentWalk j n a h).support) :
    a ≤ x.val := by
  induction n generalizing a with
  | zero =>
      simp [originalSegmentWalk] at hx
      subst x
      exact Nat.le_refl _
  | succ n ih =>
      simp [originalSegmentWalk, Walk.support_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_refl _
      · have hlow := ih (a + 1) (by omega) hx
        omega

theorem originalSegmentWalk_support_le (j a n : ℕ) (h : a + n ≤ shortcutSize j)
    {x : ShortcutVertex j} (hx : x ∈ (originalSegmentWalk j n a h).support) :
    x.val ≤ a + n := by
  induction n generalizing a with
  | zero =>
      simp [originalSegmentWalk] at hx
      subst x
      simpa using (Nat.le_refl a)
  | succ n ih =>
      simp [originalSegmentWalk, Walk.support_cons] at hx
      rcases hx with rfl | hx
      · simp

      · have hle := ih (a + 1) (by omega) hx
        omega

theorem originalSegmentWalk_isPath (j a n : ℕ) (h : a + n ≤ shortcutSize j) :
    (originalSegmentWalk j n a h).IsPath := by
  induction n generalizing a with
  | zero => simp [originalSegmentWalk, Walk.IsPath.nil]
  | succ n ih =>
      rw [originalSegmentWalk]
      rw [Walk.isPath_copy]
      apply (Walk.cons_isPath_iff _ _).2
      refine ⟨?_, ?_⟩
      · simpa using ih (a + 1) (by omega)
      · intro hx
        have hx' : (⟨a, by omega⟩ : ShortcutVertex j) ∈
            (originalSegmentWalk j n (a + 1) (by omega)).support := by
          simpa [originalSegmentWalk] using hx
        have hlow := originalSegmentWalk_support_ge j (a + 1) n (by omega) hx'
        have hbad : a + 1 ≤ a := by simpa using hlow
        omega

/-- One segment, traversed either along the original arc or by its shortcut. -/
def shortcutSegmentWalk (j i : ℕ) (hi : i < j) (useArc : Bool) :
    (binaryShortcutGraph j).Walk
      (shortcutVertex j i (by omega))
      (shortcutVertex j (i + 1) (by omega)) := by
  by_cases h : useArc = true
  · subst useArc
    let p := originalSegmentWalk j (2 ^ i + 1) (shortcutBoundary i) (by
      calc
        shortcutBoundary i + (2 ^ i + 1) = shortcutBoundary (i + 1) := (shortcutBoundary_succ i).symm
        _ ≤ shortcutBoundary j := shortcutBoundary_mono (Nat.succ_le_of_lt hi))
    exact p.copy rfl (Fin.ext (by simp [p, shortcutVertex, shortcutBoundary_succ]))
  · have hadj := segment_shortcut_adj j i hi
    exact hadj.toWalk

theorem shortcutSegmentWalk_isPath (j i : ℕ) (hi : i < j) (useArc : Bool) :
    (shortcutSegmentWalk j i hi useArc).IsPath := by
  unfold shortcutSegmentWalk
  split_ifs with h
  · subst useArc
    have hp := originalSegmentWalk_isPath j (shortcutBoundary i) (2 ^ i + 1) (by
      calc
        shortcutBoundary i + (2 ^ i + 1) = shortcutBoundary (i + 1) := (shortcutBoundary_succ i).symm
        _ ≤ shortcutBoundary j := shortcutBoundary_mono (Nat.succ_le_of_lt hi))
    exact (Walk.isPath_copy _ rfl (Fin.ext (by simp [shortcutVertex, shortcutBoundary_succ]))).2 hp
  · exact Walk.IsPath.of_adj (segment_shortcut_adj j i hi)

theorem shortcutSegmentWalk_length (j i : ℕ) (hi : i < j) (useArc : Bool) :
    (shortcutSegmentWalk j i hi useArc).length = if useArc then 2 ^ i + 1 else 1 := by
  unfold shortcutSegmentWalk
  split_ifs with h
  · subst useArc
    simp [originalSegmentWalk_length]
  · simp

theorem shortcutSegmentWalk_support_lower (j i : ℕ) (hi : i < j) (useArc : Bool)
    {x : ShortcutVertex j}
    (hx : x ∈ (shortcutSegmentWalk j i hi useArc).support) :
    shortcutBoundary i ≤ x.val := by
  by_cases h : useArc = true
  · subst useArc
    have hx' : x ∈ (originalSegmentWalk j (2 ^ i + 1) (shortcutBoundary i) (by
      calc
        shortcutBoundary i + (2 ^ i + 1) = shortcutBoundary (i + 1) := (shortcutBoundary_succ i).symm
        _ ≤ shortcutBoundary j := shortcutBoundary_mono (Nat.succ_le_of_lt hi))).support := by
      simpa [shortcutSegmentWalk] using hx
    exact originalSegmentWalk_support_ge j (shortcutBoundary i) (2 ^ i + 1) _ hx'
  · have hx' := hx
    simp [shortcutSegmentWalk, h] at hx'
    rcases hx' with rfl | rfl
    · simp [shortcutVertex]
    · have hb : shortcutBoundary i ≤ shortcutBoundary (i + 1) := by
        rw [shortcutBoundary_succ]
        have hp : 0 < 2 ^ i + 1 := by positivity
        omega
      simpa [shortcutVertex] using hb

theorem shortcutSegmentWalk_support_upper (j i : ℕ) (hi : i < j) (useArc : Bool)
    {x : ShortcutVertex j}
    (hx : x ∈ (shortcutSegmentWalk j i hi useArc).support) :
    x.val ≤ shortcutBoundary (i + 1) := by
  by_cases h : useArc = true
  · subst useArc
    have hx' : x ∈ (originalSegmentWalk j (2 ^ i + 1) (shortcutBoundary i) (by
      calc
        shortcutBoundary i + (2 ^ i + 1) = shortcutBoundary (i + 1) := (shortcutBoundary_succ i).symm
        _ ≤ shortcutBoundary j := shortcutBoundary_mono (Nat.succ_le_of_lt hi))).support := by
      simpa [shortcutSegmentWalk] using hx
    have hle := originalSegmentWalk_support_le j (shortcutBoundary i) (2 ^ i + 1) _ hx'
    simpa [shortcutBoundary_succ] using hle
  · have hx' := hx
    simp [shortcutSegmentWalk, h] at hx'
    rcases hx' with rfl | rfl
    · have hb : shortcutBoundary i ≤ shortcutBoundary (i + 1) := by
        rw [shortcutBoundary_succ]
        have hp : 0 < 2 ^ i + 1 := by positivity
        omega
      simpa [shortcutVertex] using hb
    · simp [shortcutVertex]

/-- Sum of the powers selected on a consecutive block of segment indices. -/
def chosenPowerSum (a n : ℕ) (choose : ℕ → Bool) : ℕ :=
  ∑ k ∈ Finset.range n, if choose (a + k) then 2 ^ (a + k) else 0

/-- Concatenate, in order, the chosen original arcs and shortcut edges. -/
def selectedChainWalk (j : ℕ) : (n a : ℕ) → (h : a + n ≤ j) →
    (choose : ℕ → Bool) →
    (binaryShortcutGraph j).Walk
      (shortcutVertex j a (by omega))
      (shortcutVertex j (a + n) (by omega))
  | 0, a, _, _ => Walk.nil
  | n + 1, a, h, choose =>
      let p := selectedChainWalk j n a (by omega) choose
      let q := shortcutSegmentWalk j (a + n) (by omega) (choose (a + n))
      (p.append q).copy rfl (Fin.ext (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))

theorem selectedChainWalk_length (j a n : ℕ) (h : a + n ≤ j) (choose : ℕ → Bool) :
    (selectedChainWalk j n a h choose).length = n + chosenPowerSum a n choose := by
  induction n generalizing a with
  | zero => simp [selectedChainWalk, chosenPowerSum]
  | succ n ih =>
      simp [selectedChainWalk, Walk.length_append, shortcutSegmentWalk_length,
        chosenPowerSum, ih, Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [Nat.add_comm n a]
      split_ifs <;> omega

theorem selectedChainWalk_support_lower (j a n : ℕ) (h : a + n ≤ j)
    (choose : ℕ → Bool) {x : ShortcutVertex j}
    (hx : x ∈ (selectedChainWalk j n a h choose).support) :
    shortcutBoundary a ≤ x.val := by
  induction n generalizing a with
  | zero =>
      simp [selectedChainWalk] at hx
      subst x
      simp [shortcutVertex]
  | succ n ih =>
      simp [selectedChainWalk, Walk.support_append] at hx
      rcases hx with hx | hx
      · exact ih a (by omega) hx
      · have hxfull := List.mem_of_mem_tail hx
        exact (shortcutBoundary_mono (Nat.le_add_right a n)).trans
          (shortcutSegmentWalk_support_lower j (a + n) (by omega)
            (choose (a + n)) hxfull)

theorem selectedChainWalk_support_upper (j a n : ℕ) (h : a + n ≤ j)
    (choose : ℕ → Bool) {x : ShortcutVertex j}
    (hx : x ∈ (selectedChainWalk j n a h choose).support) :
    x.val ≤ shortcutBoundary (a + n) := by
  induction n generalizing a with
  | zero =>
      simp [selectedChainWalk] at hx
      subst x
      simp [shortcutVertex]
  | succ n ih =>
      simp [selectedChainWalk, Walk.support_append] at hx
      rcases hx with hx | hx
      · exact (ih a (by omega) hx).trans
          (shortcutBoundary_mono (Nat.le_succ (a + n)))
      · exact shortcutSegmentWalk_support_upper j (a + n) (by omega)
          (choose (a + n)) (List.mem_of_mem_tail hx)

theorem selectedChainWalk_isPath (j a n : ℕ) (h : a + n ≤ j) (choose : ℕ → Bool) :
    (selectedChainWalk j n a h choose).IsPath := by
  induction n generalizing a with
  | zero => simp [selectedChainWalk, Walk.IsPath.nil]
  | succ n ih =>
      unfold selectedChainWalk
      apply isPath_append_of_support_disjoint
      · exact ih a (by omega)
      · exact shortcutSegmentWalk_isPath j (a + n) (by omega) (choose (a + n))
      · intro x hx hy
        have hxupper := selectedChainWalk_support_upper j a n (by omega) choose hx
        have hylower := shortcutSegmentWalk_support_lower j (a + n) (by omega)
          (choose (a + n)) (List.mem_of_mem_tail hy)
        have hneq : x.val ≠ shortcutBoundary (a + n) := by
          intro heq
          have hxs : x = shortcutVertex j (a + n) (by omega) := by
            apply Fin.ext
            simpa using heq
          have hstart : shortcutVertex j (a + n) (by omega) ∉
              (shortcutSegmentWalk j (a + n) (by omega) (choose (a + n))).support.tail := by
            have hq := shortcutSegmentWalk_isPath j (a + n) (by omega) (choose (a + n))
            have hqn := hq.support_nodup
            rw [Walk.support_eq_cons] at hqn
            exact (List.nodup_cons.mp hqn).1
          exact hstart (by simpa [hxs] using hy)
        have hstrict : shortcutBoundary (a + n) < x.val := by
          omega
        omega

lemma shortcutBoundary_lt_succ (i : ℕ) : shortcutBoundary i < shortcutBoundary (i + 1) := by
  rw [shortcutBoundary_succ]
  have hp : 0 < 2 ^ i + 1 := by positivity
  omega

theorem shortcutBoundary_strictMono : StrictMono shortcutBoundary :=
  strictMono_nat_of_lt_succ shortcutBoundary_lt_succ

/-- For at least two segments the chain graph has no edge joining its two
extreme boundaries; this is the new closing chord in the construction. -/
theorem no_adj_extreme_boundaries (j : ℕ) (hj : 2 ≤ j) :
    ¬ (binaryShortcutGraph j).Adj
      (shortcutVertex j 0 (by omega)) (shortcutVertex j j (by omega)) := by
  intro hadj
  have h0 : shortcutBoundary 0 = 0 := shortcutBoundary_zero
  have h02 : shortcutBoundary 0 < shortcutBoundary j :=
    shortcutBoundary_strictMono (by omega)
  rcases hadj with hadj | hadj | ⟨i, hi, h⟩
  · have hval : 0 + 1 = shortcutBoundary j := by simpa [shortcutVertex, h0] using hadj
    have hbig : 1 < shortcutBoundary j := by
      have := shortcutBoundary_strictMono (show 1 < j by omega)
      have h1 : shortcutBoundary 1 = 2 := by simp [shortcutBoundary_succ, h0]
      omega
    omega
  · have hval : shortcutBoundary j + 1 = 0 := by simpa [shortcutVertex, h0] using hadj
    omega
  · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have hi0 : i = 0 := shortcutBoundary_strictMono.injective (by simpa [h0] using h₁.symm)
      have hij : i + 1 = j := shortcutBoundary_strictMono.injective h₂.symm
      omega
    · have hstep := shortcutBoundary_lt_succ i
      have h1' : shortcutBoundary j = shortcutBoundary i := by simpa [shortcutVertex] using h₁
      have h2' : shortcutBoundary 0 = shortcutBoundary (i + 1) := by simpa [shortcutVertex] using h₂
      have hlt : shortcutBoundary j < shortcutBoundary 0 := by rw [h1', h2']; exact hstep
      omega

/-- Every target length in the binary-chain interval is realized by a simple
path, with the original selected arcs and shortcut edges in their natural
finite graph. The path avoids the future closing edge. -/
theorem selectedChainPath_family (j ℓ : ℕ) (hj : 2 ≤ j)
    (hlo : j ≤ ℓ) (hhi : ℓ < j + 2 ^ j) :
    ∃ p : (binaryShortcutGraph j).Walk
      (shortcutVertex j 0 (by omega)) (shortcutVertex j j (by omega)),
      p.IsPath ∧ p.length = ℓ ∧
      s(shortcutVertex j j (by omega), shortcutVertex j 0 (by omega)) ∉ p.edges := by
  obtain ⟨s, hs, hsum⟩ := exists_subset_sum_powers j (ℓ - j) (by omega)
  let choose : ℕ → Bool := fun i => decide (i ∈ s)
  let q := selectedChainWalk j j 0 (by omega) choose
  have hend : shortcutVertex j (0 + j) (by omega) = shortcutVertex j j (by omega) := by
    apply Fin.ext
    simp [Nat.zero_add]
  let p := q.copy rfl hend
  have hpow : chosenPowerSum 0 j choose = ∑ i ∈ s, 2 ^ i := by
    calc
      chosenPowerSum 0 j choose =
          ∑ i ∈ Finset.range j, if i ∈ s then 2 ^ i else 0 := by
            simp [chosenPowerSum, choose]
      _ = ∑ i ∈ {i ∈ Finset.range j | i ∈ s}, 2 ^ i := by
            exact (Finset.sum_filter (fun i => i ∈ s) (fun i => 2 ^ i) (s := Finset.range j)).symm
      _ = ∑ i ∈ s, 2 ^ i := by
            have hfilter : {i ∈ Finset.range j | i ∈ s} = s := by
              ext i
              simp only [Finset.mem_filter]
              exact ⟨And.right, fun hi => ⟨hs hi, hi⟩⟩
            rw [hfilter]
  refine ⟨p, ?_, ?_, ?_⟩
  · exact (Walk.isPath_copy q rfl hend).2
      (selectedChainWalk_isPath j 0 j (by omega) choose)
  · dsimp [p, q]
    simp only [Walk.length_copy]
    rw [selectedChainWalk_length, hpow, hsum]
    omega
  · intro hedge
    have hadj := Walk.adj_of_mem_edges p hedge
    exact no_adj_extreme_boundaries j hj hadj.symm



/-- The chain graph with the additional closing edge between its extreme
vertices. -/
def closedShortcutGraph (j : ℕ) : SimpleGraph (ShortcutVertex j) where
  Adj v w := (binaryShortcutGraph j).Adj v w ∨
    (2 ≤ j ∧ ((v.val = 0 ∧ w.val = shortcutBoundary j) ∨
              (w.val = 0 ∧ v.val = shortcutBoundary j)))
  loopless := by
    intro v h
    rcases h with h | ⟨hj, h⟩
    · exact (binaryShortcutGraph j).loopless v h
    · rcases h with ⟨h0, hjv⟩ | ⟨h0, hjv⟩
      · have hpos : 0 < shortcutBoundary j := by
          have hlt := shortcutBoundary_strictMono (show 0 < j by omega)
          simpa [shortcutBoundary_zero] using hlt
        omega
      · have hpos : 0 < shortcutBoundary j := by
          have hlt := shortcutBoundary_strictMono (show 0 < j by omega)
          simpa [shortcutBoundary_zero] using hlt
        omega
  symm := by
    intro v w h
    rcases h with h | ⟨hj, h⟩
    · exact Or.inl ((binaryShortcutGraph j).symm h)
    · rcases h with ⟨h0, hjv⟩ | ⟨h0, hjv⟩
      · exact Or.inr ⟨hj, Or.inr ⟨h0, hjv⟩⟩
      · exact Or.inr ⟨hj, Or.inl ⟨h0, hjv⟩⟩

theorem closedShortcutGraph_adj_ends (j : ℕ) (hj : 2 ≤ j) :
    (closedShortcutGraph j).Adj
      (shortcutVertex j j (by omega)) (shortcutVertex j 0 (by omega)) := by
  apply Or.inr
  refine ⟨hj, Or.inr ?_⟩
  simp [shortcutVertex, shortcutBoundary_zero]

/-- The chain edges remain edges after adjoining the closing chord. -/
private theorem chain_le_closed (j : ℕ) :
    binaryShortcutGraph j ≤ closedShortcutGraph j := by
  intro v w h
  exact Or.inl h

/-- Closing the finite binary shortcut chain supplies every cycle length in
its full interval. -/
theorem closedShortcut_cycle_interval (j c : ℕ) (hj : 2 ≤ j)
    (hlo : j + 1 ≤ c) (hhi : c ≤ 2 ^ j + j) :
    Erdos1016.Problem1016.HasCycleLength (closedShortcutGraph j) c := by
  apply cycle_interval_of_path_family (closedShortcutGraph j) j
    (u := shortcutVertex j 0 (by omega)) (v := shortcutVertex j j (by omega))
    (closedShortcutGraph_adj_ends j hj)
  · intro ℓ hℓ hℓ'
    obtain ⟨p, hp, hlen, hnew⟩ := selectedChainPath_family j ℓ hj hℓ hℓ'
    let htrans : ∀ (e : Sym2 (ShortcutVertex j)), e ∈ p.edges →
        e ∈ (closedShortcutGraph j).edgeSet := by
      intro e he
      exact SimpleGraph.edgeSet_mono (chain_le_closed j) (p.edges_subset_edgeSet he)
    let q := p.transfer (closedShortcutGraph j) htrans
    refine ⟨q, Walk.IsPath.transfer htrans hp, ?_, ?_⟩
    · simpa [q] using hlen
    · simpa [q, Walk.edges_transfer] using hnew
  · omega
  · omega

end Erdos1016.Extremal

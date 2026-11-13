import Erdos1016.ExactMaximum.GirthFive.GeodesicRails

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Two terminals at girth five: the count

`K` is a finite simple graph in which every cycle has more than four edges and every vertex has
at most three neighbours. `B` is a set of vertices, and `KB` is the graph `K` inside `B`. Let
`A` be a shortest walk of `KB` between two different vertices, and suppose that every cycle of
`KB` meets `A`. Then `B` is small: `|B| ≤ 400 (|D| + 2)`, where `D` contains every vertex of `B`
that has fewer than three neighbours or a neighbour outside `B`.

The proof is a count. Put `F = B - V(A)`.

* A vertex of `F` has at most one neighbour on `A` (`attach_unique`).
* The graph on `F` has at most `|F|` edges; this is the hypothesis `hedges` (the graph is a
  forest). So at most `2 |D|` vertices of `F` outside `D` have no neighbour on `A`.
* Let `E` be the set of the vertices of `F` that are in `D`, or have no neighbour on `A`, or are
  adjacent to an end of `A`. A vertex `w` of `F` outside `E` has exactly two neighbours in `F`.
  If no vertex of `E` is within distance three of `w`, the walk in `F` through `w` with three
  steps in each direction is a rail with seven vertices, which `no_rail` excludes.
* So `|F| ≤ 64 |E|`, and every vertex of `A` outside `D` has a neighbour in `F`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph Erdos1016.Nonbacktracking Erdos1016.Nonbacktracking.ShortWalks

local instance twoTerminalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem girthGreater_mono {K K' : SimpleGraph V} (h : K' ≤ K) (D : ℕ)
    (hg : GirthGreater K D) : GirthGreater K' D := by
  intro u p hp
  have hh := hg u (p.mapLe h) ((Walk.mapLe_isCycle h).mpr hp)
  simpa using hh

/-- If every edge of a graph ends in a vertex with the property `P`, then every vertex of a walk
that starts in such a vertex has the property. -/
theorem walk_support_of_adj {H : SimpleGraph V} (P : V → Prop)
    (hH : ∀ u v, H.Adj u v → P v) {u v : V} (p : H.Walk u v) (hu : P u) :
    ∀ z ∈ p.support, P z := by
  induction p with
  | nil =>
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    rw [hz]
    exact hu
  | cons h p ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih (hH _ _ h) z hz

variable [Fintype V]

/-- The neighbours of a vertex. -/
def nbrs (K : SimpleGraph V) (v : V) : Finset V := Finset.univ.filter (K.Adj v)

theorem mem_nbrs (K : SimpleGraph V) (v u : V) : u ∈ nbrs K v ↔ K.Adj v u := by
  simp [nbrs]

/-- A set together with the neighbours of its vertices. -/
def nb (K : SimpleGraph V) (T : Finset V) : Finset V := T ∪ T.biUnion (nbrs K)

theorem card_nb_le (K : SimpleGraph V) (hdeg : ∀ v, (nbrs K v).card ≤ 3) (T : Finset V) :
    (nb K T).card ≤ 4 * T.card := by
  have h1 := Finset.card_union_le T (T.biUnion (nbrs K))
  have h2 := Finset.card_biUnion_le_card_mul T (nbrs K) 3 (fun a _ => hdeg a)
  unfold nb
  omega

theorem not_mem_nb (K : SimpleGraph V) {T : Finset V} {z : V} (hz : z ∉ nb K T) :
    z ∉ T ∧ ∀ u, K.Adj z u → u ∉ T := by
  unfold nb at hz
  rw [Finset.mem_union, not_or] at hz
  refine ⟨hz.1, fun u hzu hu => hz.2 ?_⟩
  exact Finset.mem_biUnion.mpr ⟨u, hu, (mem_nbrs K u z).mpr hzu.symm⟩

/-- A sequence of seven vertices as a function on the natural numbers. -/
def seq7 {α : Type*} (a b c d e f g : α) : ℕ → α
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | _ => g

/-- **Two terminals at girth five.** -/
theorem two_terminal_card_le (K : SimpleGraph V) (hg : GirthGreater K 4)
    (hdeg : ∀ v, (nbrs K v).card ≤ 3)
    (B : Finset V) {x y : V} (hxy : x ≠ y)
    (KB : SimpleGraph V) (hKB : ∀ u v, KB.Adj u v ↔ K.Adj u v ∧ u ∈ B ∧ v ∈ B)
    (A : KB.Walk x y) (hshort : ∀ q : KB.Walk x y, A.length ≤ q.length)
    (hforest : ∀ (u : V) (c : KB.Walk u u), c.IsCycle → ∃ z ∈ c.support, z ∈ A.support)
    (hedges : (∑ v ∈ B.filter (fun v => v ∉ A.support),
        ((nbrs K v).filter (fun u => u ∈ B ∧ u ∉ A.support)).card) ≤
      2 * (B.filter (fun v => v ∉ A.support)).card)
    (D : Finset V)
    (hD : ∀ v ∈ B, v ∉ D → (nbrs K v).card = 3 ∧ ∀ u, K.Adj v u → u ∈ B) :
    B.card ≤ 400 * (D.card + 2) := by
  classical
  let F : Finset V := B.filter (fun v => v ∉ A.support)
  have hmemF : ∀ v, v ∈ F ↔ v ∈ B ∧ v ∉ A.support := by
    intro v
    simp only [F, Finset.mem_filter]
  have hgB : GirthGreater KB 4 :=
    girthGreater_mono (fun u v h => ((hKB u v).mp h).1) 4 hg
  have hpos : ∀ z ∈ A.support, ∃ i, i ≤ A.length ∧ A.getVert i = z := by
    intro z hz
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    exact ⟨i, hil, hi⟩
  have hlen : 1 ≤ A.length := by
    by_contra h
    have h0 : A.length = 0 := by omega
    exact hxy (Walk.eq_of_length_eq_zero h0)
  have hSB : ∀ z ∈ A.support, z ∈ B := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hpos z hz
    by_cases hlt : i < A.length
    · exact ((hKB _ _).mp (A.adj_getVert_succ hlt)).2.1
    · have hi' : i = A.length := by omega
      have hh := A.adj_getVert_succ (show A.length - 1 < A.length by omega)
      rw [show A.length - 1 + 1 = A.length by omega] at hh
      rw [hi']
      exact ((hKB _ _).mp hh).2.2
  -- no vertex has four neighbours in `KB`
  have hdeg4 : ∀ z a b c d : V, KB.Adj z a → KB.Adj z b → KB.Adj z c → KB.Adj z d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
    intro z a b c d ha hb hc hd
    by_contra hcon
    push_neg at hcon
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hcon
    have hsub : ({a, b, c, d} : Finset V) ⊆ nbrs K z := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rw [mem_nbrs]
      rcases hu with rfl | rfl | rfl | rfl
      · exact ((hKB _ _).mp ha).1
      · exact ((hKB _ _).mp hb).1
      · exact ((hKB _ _).mp hc).1
      · exact ((hKB _ _).mp hd).1
    have hcard : ({a, b, c, d} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_insert_of_not_mem, Finset.card_singleton]
      · simpa using hcd
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
    have hle := (Finset.card_le_card hsub).trans (hdeg z)
    omega
  -- a vertex of `F` has at most one neighbour on `A`
  have hatt : ∀ v, v ∈ F → ∀ a ∈ A.support, ∀ a' ∈ A.support,
      K.Adj v a → K.Adj v a' → a = a' := by
    intro v hv a ha a' ha' hva hva'
    obtain ⟨hvB, hvA⟩ := (hmemF v).mp hv
    obtain ⟨i, hi, rfl⟩ := hpos a ha
    obtain ⟨j, hj, rfl⟩ := hpos a' ha'
    have h1 : KB.Adj v (A.getVert i) := (hKB _ _).mpr ⟨hva, hvB, hSB _ ha⟩
    have h2 : KB.Adj v (A.getVert j) := (hKB _ _).mpr ⟨hva', hvB, hSB _ ha'⟩
    rw [attach_unique A hshort hgB hvA hi hj h1 h2]
  -- the neighbours in `F` and on `A`
  let NF : V → Finset V := fun v => (nbrs K v).filter (fun u => u ∈ B ∧ u ∉ A.support)
  let NS : V → Finset V := fun v => (nbrs K v).filter (fun u => u ∈ A.support)
  have hNFmem : ∀ v u, u ∈ NF v ↔ K.Adj v u ∧ u ∈ F := by
    intro v u
    simp only [NF, Finset.mem_filter, mem_nbrs, hmemF]
  have hNSmem : ∀ v u, u ∈ NS v ↔ K.Adj v u ∧ u ∈ A.support := by
    intro v u
    simp only [NS, Finset.mem_filter, mem_nbrs]
  have hsplit : ∀ v ∈ B, v ∉ D → (NF v).card + (NS v).card = 3 := by
    intro v hv hvD
    obtain ⟨h3, hin⟩ := hD v hv hvD
    have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := nbrs K v)
      (fun u => u ∈ A.support)
    have heq : (nbrs K v).filter (fun u => ¬ u ∈ A.support) = NF v := by
      ext u
      simp only [NF, Finset.mem_filter, mem_nbrs]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, hin u h1, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
    rw [heq] at hh
    have hNS' : (nbrs K v).filter (fun u => u ∈ A.support) = NS v := rfl
    rw [hNS'] at hh
    omega
  have hNS1 : ∀ v ∈ F, (NS v).card ≤ 1 := by
    intro v hv
    rw [Finset.card_le_one]
    intro a ha a' ha'
    rw [hNSmem] at ha ha'
    exact hatt v hv a ha.2 a' ha'.2 ha.1 ha'.1
  -- the vertices of `F` outside `D` without a neighbour on `A`
  let FD : Finset V := F.filter (fun v => v ∈ D)
  let FN : Finset V := F.filter (fun v => ¬ v ∈ D)
  have hFcard : FD.card + FN.card = F.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := F) (fun v => v ∈ D)
  let U0 : Finset V := FN.filter (fun v => NS v = ∅)
  have hU0 : U0.card ≤ 2 * FD.card := by
    have hlow : ∑ v ∈ FN, (2 + if NS v = ∅ then 1 else 0) ≤ ∑ v ∈ FN, (NF v).card := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvF, hvD⟩ := Finset.mem_filter.mp hv
      have h3 := hsplit v ((hmemF v).mp hvF).1 hvD
      have h1 := hNS1 v hvF
      split_ifs with h0
      · have hz : (NS v).card = 0 := by rw [h0]; rfl
        omega
      · omega
    have hsum : ∑ v ∈ FN, (2 + if NS v = ∅ then 1 else 0) = 2 * FN.card + U0.card := by
      have hU : U0.card = ∑ v ∈ FN, if NS v = ∅ then 1 else 0 := Finset.card_filter _ _
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hU, mul_comm]
    have hsub : ∑ v ∈ FN, (NF v).card ≤ ∑ v ∈ F, (NF v).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hedges' : ∑ v ∈ F, (NF v).card ≤ 2 * F.card := hedges
    omega
  -- the exceptional set
  let E : Finset V := FD ∪ U0 ∪ F.filter (K.Adj x) ∪ F.filter (K.Adj y)
  have hE : E.card ≤ 3 * D.card + 6 := by
    have h1 : FD.card ≤ D.card :=
      Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
    have h2 : (F.filter (K.Adj x)).card ≤ 3 :=
      (Finset.card_le_card (fun v hv =>
        (mem_nbrs K x v).mpr (Finset.mem_filter.mp hv).2)).trans (hdeg x)
    have h3 : (F.filter (K.Adj y)).card ≤ 3 :=
      (Finset.card_le_card (fun v hv =>
        (mem_nbrs K y v).mpr (Finset.mem_filter.mp hv).2)).trans (hdeg y)
    have h4 := Finset.card_union_le (FD ∪ U0 ∪ F.filter (K.Adj x)) (F.filter (K.Adj y))
    have h5 := Finset.card_union_le (FD ∪ U0) (F.filter (K.Adj x))
    have h6 := Finset.card_union_le FD U0
    show (FD ∪ U0 ∪ F.filter (K.Adj x) ∪ F.filter (K.Adj y)).card ≤ 3 * D.card + 6
    omega
  have hEmem : ∀ w, w ∈ F → w ∉ E → w ∉ D ∧ NS w ≠ ∅ ∧ ¬ K.Adj x w ∧ ¬ K.Adj y w := by
    intro w hw hwE
    have hwD : w ∉ D := by
      intro h
      apply hwE
      simp only [E, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hw, h⟩)))
    refine ⟨hwD, ?_, ?_, ?_⟩
    · intro h0
      apply hwE
      simp only [E, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hw, hwD⟩, h0⟩)))
    · intro h
      apply hwE
      simp only [E, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hw, h⟩))
    · intro h
      apply hwE
      simp only [E, Finset.mem_union]
      exact Or.inr (Finset.mem_filter.mpr ⟨hw, h⟩)
  -- a vertex of `F` outside `E`: a neighbour at an inner position, and two neighbours in `F`
  have hgood : ∀ w, w ∈ F → w ∉ E →
      (∃ p, 0 < p ∧ p < A.length ∧ K.Adj w (A.getVert p)) ∧ 2 ≤ (NF w).card := by
    intro w hw hwE
    obtain ⟨hwD, hne, hwx, hwy⟩ := hEmem w hw hwE
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [hNSmem] at ha
    obtain ⟨p, hp, hpa⟩ := hpos a ha.2
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [Walk.getVert_zero] at hpa
      rw [← hpa] at ha
      exact hwx ha.1.symm
    have hpl : p ≠ A.length := by
      rintro rfl
      rw [Walk.getVert_length] at hpa
      rw [← hpa] at ha
      exact hwy ha.1.symm
    have h3 := hsplit w ((hmemF w).mp hw).1 hwD
    have h1 := hNS1 w hw
    refine ⟨⟨p, by omega, by omega, ?_⟩, by omega⟩
    rw [hpa]
    exact ha.1
  have hext : ∀ w, w ∈ F → w ∉ E → ∀ u' : V, ∃ u'', K.Adj w u'' ∧ u'' ∈ F ∧ u'' ≠ u' := by
    intro w hw hwE u'
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
      (show 1 < (NF w).card by have := (hgood w hw hwE).2; omega)
    rw [hNFmem] at ha hb
    by_cases h : a = u'
    · exact ⟨b, hb.1, hb.2, fun hb' => hab (h.trans hb'.symm)⟩
    · exact ⟨a, ha.1, ha.2, h⟩
  -- the graph on `F`
  let KF : SimpleGraph V :=
    { Adj := fun u v => KB.Adj u v ∧ u ∉ A.support ∧ v ∉ A.support
      symm := fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩
      loopless := fun u h => KB.loopless u h.1 }
  have hKFle : KF ≤ KB := fun u v h => h.1
  have hKFacyc : KF.IsAcyclic := by
    intro u c hc
    obtain ⟨z, hz, hzA⟩ := hforest u (c.mapLe hKFle) ((Walk.mapLe_isCycle hKFle).mpr hc)
    have hzc : z ∈ c.support := by simpa using hz
    have hu : u ∉ A.support := by
      cases c with
      | nil => exact absurd hc Walk.IsCycle.not_of_nil
      | cons h p => exact h.2.1
    exact walk_support_of_adj (H := KF) (fun v => v ∉ A.support) (fun a b h => h.2.2) c hu z hzc
      hzA
  -- every vertex of `F` is within distance three of `E`
  have hball : ∀ w, w ∈ F → w ∈ nb K (nb K (nb K E)) := by
    intro w hw
    apply Classical.byContradiction
    intro hw3
    obtain ⟨hw2, hw2n⟩ := not_mem_nb K hw3
    obtain ⟨hw1, _⟩ := not_mem_nb K hw2
    obtain ⟨hw0, _⟩ := not_mem_nb K hw1
    -- the two neighbours of `w` in `F`
    obtain ⟨a1, ha1, b1, hb1, hab1⟩ := Finset.one_lt_card.mp
      (show 1 < (NF w).card by have := (hgood w hw hw0).2; omega)
    rw [hNFmem] at ha1 hb1
    -- one side
    have ha1_2 : a1 ∉ nb K (nb K E) := hw2n a1 ha1.1
    obtain ⟨ha1_1, ha1n⟩ := not_mem_nb K ha1_2
    obtain ⟨ha1_0, _⟩ := not_mem_nb K ha1_1
    obtain ⟨a2, ha2adj, ha2F, ha2ne⟩ := hext a1 ha1.2 ha1_0 w
    have ha2_1 : a2 ∉ nb K E := ha1n a2 ha2adj
    obtain ⟨ha2_0, ha2n⟩ := not_mem_nb K ha2_1
    obtain ⟨a3, ha3adj, ha3F, ha3ne⟩ := hext a2 ha2F ha2_0 a1
    have ha3_0 : a3 ∉ E := ha2n a3 ha3adj
    -- the other side
    have hb1_2 : b1 ∉ nb K (nb K E) := hw2n b1 hb1.1
    obtain ⟨hb1_1, hb1n⟩ := not_mem_nb K hb1_2
    obtain ⟨hb1_0, _⟩ := not_mem_nb K hb1_1
    obtain ⟨b2, hb2adj, hb2F, hb2ne⟩ := hext b1 hb1.2 hb1_0 w
    have hb2_1 : b2 ∉ nb K E := hb1n b2 hb2adj
    obtain ⟨hb2_0, hb2n⟩ := not_mem_nb K hb2_1
    obtain ⟨b3, hb3adj, hb3F, hb3ne⟩ := hext b2 hb2F hb2_0 b1
    have hb3_0 : b3 ∉ E := hb2n b3 hb3adj
    -- the rail
    let f : ℕ → V := seq7 b3 b2 b1 w a1 a2 a3
    have hfF : ∀ k, k ≤ 6 → f k ∈ F ∧ f k ∉ E := by
      intro k hk
      interval_cases k
      · exact ⟨hb3F, hb3_0⟩
      · exact ⟨hb2F, hb2_0⟩
      · exact ⟨hb1.2, hb1_0⟩
      · exact ⟨hw, hw0⟩
      · exact ⟨ha1.2, ha1_0⟩
      · exact ⟨ha2F, ha2_0⟩
      · exact ⟨ha3F, ha3_0⟩
    have hfadjK : ∀ k, k < 6 → K.Adj (f k) (f (k + 1)) := by
      intro k hk
      interval_cases k
      · exact hb3adj.symm
      · exact hb2adj.symm
      · exact hb1.1.symm
      · exact ha1.1
      · exact ha2adj
      · exact ha3adj
    have hfred : ∀ m, m + 2 ≤ 6 → f (m + 2) ≠ f m := by
      intro m hm
      have hm' : m ≤ 4 := by omega
      interval_cases m
      · exact fun h => hb3ne h.symm
      · exact fun h => hb2ne h.symm
      · exact fun h => hab1 h
      · exact ha2ne
      · exact ha3ne
    have hfKB : ∀ k, k < 6 → KB.Adj (f k) (f (k + 1)) := by
      intro k hk
      exact (hKB _ _).mpr ⟨hfadjK k hk, ((hmemF _).mp (hfF k (by omega)).1).1,
        ((hmemF _).mp (hfF (k + 1) (by omega)).1).1⟩
    have hfKF : ∀ k, k < 6 → KF.Adj (f k) (f (k + 1)) := by
      intro k hk
      exact ⟨hfKB k hk, ((hmemF _).mp (hfF k (by omega)).1).2,
        ((hmemF _).mp (hfF (k + 1) (by omega)).1).2⟩
    -- the vertices of the rail are pairwise different
    obtain ⟨q, hq, hqv⟩ := exists_walk_of_fn (K := KF) f 6 0 (fun k _ hk => hfKF k (by omega))
    have hqred : Reduced q := by
      apply reduced_of_getVert
      intro m hm
      rw [hq] at hm
      rw [hqv (m + 2) hm, hqv m (by omega)]
      simpa only [zero_add] using hfred m hm
    have hqpath := reduced_isPath_of_acyclic hKFacyc q hqred
    have hfinj : ∀ k l, k < l → l ≤ 6 → f k ≠ f l := by
      intro k l hkl hl heq
      have hk : k ≤ 6 := by omega
      have h1 : q.getVert k = f k := (hqv k hk).trans (congrArg f (zero_add k))
      have h2 : q.getVert l = f l := (hqv l hl).trans (congrArg f (zero_add l))
      have := hqpath.getVert_injOn (by rw [Set.mem_setOf, hq]; exact hk)
        (by rw [Set.mem_setOf, hq]; exact hl) (h1.trans (heq.trans h2.symm))
      omega
    -- the positions on `A`
    have hposf : ∀ k, ∃ p, k ≤ 6 → 0 < p ∧ p < A.length ∧ K.Adj (f k) (A.getVert p) := by
      intro k
      by_cases hk : k ≤ 6
      · obtain ⟨p, hp⟩ := (hgood (f k) (hfF k hk).1 (hfF k hk).2).1
        exact ⟨p, fun _ => hp⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose p hp using hposf
    refine no_rail A hshort hgB hdeg4 f p ?_ hfKB hfinj ?_ ?_
    · intro k hk
      exact ((hmemF _).mp (hfF k hk).1).2
    · intro k hk
      exact ⟨(hp k hk).1, (hp k hk).2.1⟩
    · intro k hk
      exact (hKB _ _).mpr ⟨(hp k hk).2.2, ((hmemF _).mp (hfF k hk).1).1,
        hSB _ (A.getVert_mem_support _)⟩
  have hFle : F.card ≤ 64 * E.card := by
    have h0 : F.card ≤ (nb K (nb K (nb K E))).card := Finset.card_le_card (fun w hw => hball w hw)
    have h1 := card_nb_le K hdeg (nb K (nb K E))
    have h2 := card_nb_le K hdeg (nb K E)
    have h3 := card_nb_le K hdeg E
    omega
  -- the vertices of `A`
  let SB : Finset V := B.filter (fun v => v ∈ A.support)
  have hBcard : SB.card + F.card = B.card :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := B) (fun v => v ∈ A.support)
  let T : Finset V := SB.filter (fun v => ¬ v ∈ D)
  have hSBle : SB.card ≤ T.card + D.card := by
    have h1 := Finset.filter_card_add_filter_neg_card_eq_card (s := SB) (fun v => v ∈ D)
    have h2 : (SB.filter (fun v => v ∈ D)).card ≤ D.card :=
      Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
    have h3 : (SB.filter (fun v => ¬ v ∈ D)).card = T.card := rfl
    omega
  have hNS2 : ∀ a ∈ A.support, (NS a).card ≤ 2 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := hpos a ha
    have hsub : NS (A.getVert i) ⊆ {A.getVert (i - 1), A.getVert (i + 1)} := by
      intro u hu
      rw [hNSmem] at hu
      obtain ⟨j, hj, rfl⟩ := hpos u hu.2
      have hadj : KB.Adj (A.getVert i) (A.getVert j) :=
        (hKB _ _).mpr ⟨hu.1, hSB _ ha, hSB _ hu.2⟩
      have h1 := geodesic_le A hshort hi hj (Walk.cons hadj Walk.nil)
      have h2 := geodesic_le A hshort hj hi (Walk.cons hadj.symm Walk.nil)
      simp only [Walk.length_cons, Walk.length_nil] at h1 h2
      have hne : i ≠ j := by
        rintro rfl
        exact KB.loopless _ hadj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (show j = i - 1 ∨ j = i + 1 by omega) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hTle : T.card ≤ F.card := by
    have hne : ∀ a ∈ T, (NF a).Nonempty := by
      intro a ha
      obtain ⟨haS, haD⟩ := Finset.mem_filter.mp ha
      obtain ⟨haB, haA⟩ := Finset.mem_filter.mp haS
      have h3 := hsplit a haB haD
      have h2 := hNS2 a haA
      apply Finset.card_pos.mp
      omega
    choose! g hg using hne
    apply Finset.card_le_card_of_injOn g
    · intro a ha
      exact ((hNFmem a (g a)).mp (hg a ha)).2
    · intro a ha a' ha' heq
      have h1 := (hNFmem a (g a)).mp (hg a ha)
      have h2 := (hNFmem a' (g a')).mp (hg a' ha')
      have haA : a ∈ A.support := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      have haA' : a' ∈ A.support := (Finset.mem_filter.mp (Finset.mem_filter.mp ha').1).2
      have h2' : K.Adj a' (g a) := by
        have h := h2.1
        rwa [← heq] at h
      exact hatt (g a) h1.2 a haA a' haA' h1.1.symm h2'.symm
  omega

end Erdos1016.ExactMaximum.GirthFive

import Erdos1016.CycleCount.Statement
import Erdos1016.ExactCounting.DisjointCycles
import Erdos1016.ExactCounting.TwoTerminals

set_option autoImplicit false

/-!
# Outside parts without waste

Let `G` be a connected graph and let `S` be a set of edges of `G`, the edge
set of a subgraph `W`. Suppose that for every even edge set `s` of `G` there
is a cycle of `G` that agrees with `s` outside `S`. Then the graph without the
edges of `S` has no two edge-disjoint cycles, and

  `β(G) ≤ β(W) + |V(W)| + 3`.

The proof shows that any two nonempty even sets outside `S` share an edge.
Then the lemma of Erdős and Pósa bounds the number of edges outside `S` by
`n + 3`.
-/

noncomputable section

namespace Erdos1016.ExactCounting

open Finset

/-- An edge set is even if every vertex lies on an even number of its edges. -/
def IsEvenEdgeSet {V : Type*} (s : Set (Sym2 V)) : Prop :=
  ∀ v : V, Even {e | e ∈ s ∧ v ∈ e}.ncard

section Bridge

variable {V : Type*} [DecidableEq V]

/-- An ordered pair of ends that represents an unordered pair. -/
def endsOf (e : Sym2 V) : V × V := Quot.out e

omit [DecidableEq V] in
theorem mk_endsOf (e : Sym2 V) : s((endsOf e).1, (endsOf e).2) = e := Quot.out_eq e

theorem inc_endsOf {e : Sym2 V} (he : ¬ e.IsDiag) (v : V) :
    Multi.inc endsOf e v = if v ∈ e then 1 else 0 := by
  have h := mk_endsOf e
  have hne : (endsOf e).1 ≠ (endsOf e).2 := by
    intro h'
    apply he
    rw [← h]
    exact Sym2.mk_isDiag_iff.2 h'
  have hmem : v ∈ e ↔ (v = (endsOf e).1 ∨ v = (endsOf e).2) := by
    conv_lhs => rw [← h]
    exact Sym2.mem_iff
  unfold Multi.inc
  by_cases h1 : (endsOf e).1 = v
  · have h2 : (endsOf e).2 ≠ v := fun h2 => hne (h1.trans h2.symm)
    rw [if_pos h1, if_neg h2, if_pos (hmem.2 (Or.inl h1.symm))]
  · by_cases h2 : (endsOf e).2 = v
    · rw [if_neg h1, if_pos h2, if_pos (hmem.2 (Or.inr h2.symm))]
    · have hv : ¬ v ∈ e := by
        intro hv
        rcases hmem.1 hv with h' | h'
        · exact h1 h'.symm
        · exact h2 h'.symm
      rw [if_neg h1, if_neg h2, if_neg hv]

theorem deg_endsOf {X : Finset (Sym2 V)} (hX : ∀ e ∈ X, ¬ e.IsDiag) (v : V) :
    Multi.deg endsOf X v = (X.filter fun e => v ∈ e).card := by
  unfold Multi.deg
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun e he => inc_endsOf (hX e he) v

/-- For sets of edges without loops, the two notions of an even set agree. -/
theorem mEven_iff_isEven {X : Finset (Sym2 V)} (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    Multi.MEven endsOf X ↔ IsEven X := by
  unfold Multi.MEven IsEven par
  refine forall_congr' fun v => ?_
  rw [deg_endsOf hX, ZMod.eq_zero_iff_even, Nat.even_iff]

theorem isEvenEdgeSet_coe (X : Finset (Sym2 V)) :
    IsEvenEdgeSet (↑X : Set (Sym2 V)) ↔ IsEven X := by
  unfold IsEvenEdgeSet IsEven par
  refine forall_congr' fun v => ?_
  have h : {e | e ∈ (↑X : Set (Sym2 V)) ∧ v ∈ e} = ↑(X.filter fun e => v ∈ e) := by
    ext e
    simp
  rw [h, Set.ncard_coe_Finset, ZMod.eq_zero_iff_even]

end Bridge

/-- A graph with an edge has more components than isolated vertices. -/
theorem card_add_one_le_components {V : Type*} [Finite V] (S : Set (Sym2 V)) {x y : V}
    (hxy : s(x, y) ∈ S) :
    Nat.card V + 1 ≤ Nat.card (SimpleGraph.fromEdgeSet S).ConnectedComponent +
      {v | ∃ e ∈ S, v ∈ e}.ncard := by
  classical
  have hiso : ∀ v w, v ∉ {v | ∃ e ∈ S, v ∈ e} →
      (SimpleGraph.fromEdgeSet S).Reachable v w → v = w := by
    intro v w hv hr
    obtain ⟨p⟩ := hr
    cases p with
    | nil => rfl
    | cons h _ =>
      exfalso
      rw [SimpleGraph.fromEdgeSet_adj] at h
      exact hv ⟨_, h.1, Sym2.mem_mk_left _ _⟩
  have hx : x ∈ {v | ∃ e ∈ S, v ∈ e} := ⟨_, hxy, Sym2.mem_mk_left _ _⟩
  let f : ({v | ∃ e ∈ S, v ∈ e}ᶜ : Set V) ⊕ Unit →
      (SimpleGraph.fromEdgeSet S).ConnectedComponent := fun z =>
    match z with
    | Sum.inl v => (SimpleGraph.fromEdgeSet S).connectedComponentMk v.1
    | Sum.inr _ => (SimpleGraph.fromEdgeSet S).connectedComponentMk x
  have hf : Function.Injective f := by
    rintro (v | _) (w | _) h
    · have h' : (SimpleGraph.fromEdgeSet S).Reachable v.1 w.1 :=
        SimpleGraph.ConnectedComponent.eq.1 h
      exact congrArg Sum.inl (Subtype.ext (hiso _ _ v.2 h'))
    · exfalso
      have h' : (SimpleGraph.fromEdgeSet S).Reachable v.1 x :=
        SimpleGraph.ConnectedComponent.eq.1 h
      exact v.2 ((hiso _ _ v.2 h') ▸ hx)
    · exfalso
      have h' : (SimpleGraph.fromEdgeSet S).Reachable x w.1 :=
        SimpleGraph.ConnectedComponent.eq.1 h
      exact w.2 ((hiso _ _ w.2 h'.symm) ▸ hx)
    · rfl
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Unit),
    Fintype.card_unit] at hcard
  have hcompl := Set.ncard_add_ncard_compl {v : V | ∃ e ∈ S, v ∈ e}
  omega

/-- Let `G` be a connected simple graph on `Fin n` with cyclomatic number `r`,
and let `S` be a set of edges of `G`, the edge set of a subgraph `W` with
cyclomatic number `t`. Suppose that every outside part is the outside part of
a cycle. Then the graph without `S` has no two edge-disjoint cycles, and
`r ≤ t + |V(W)| + 3`. -/
def NoWasteStatement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (r t : ℕ),
    G.Connected → S ⊆ G.edgeSet →
    r + n = Nat.card G.edgeSet + 1 →
    t + n = S.ncard + Nat.card (SimpleGraph.fromEdgeSet S).ConnectedComponent →
    (∀ s : Set (Sym2 (Fin n)), s ⊆ G.edgeSet → IsEvenEdgeSet s →
      ∃ c ∈ CycleCount.cycleEdgeSets G, c \ S = s \ S) →
    (∀ c₁ ∈ CycleCount.cycleEdgeSets (G.deleteEdges S),
      ∀ c₂ ∈ CycleCount.cycleEdgeSets (G.deleteEdges S), ¬ Disjoint c₁ c₂) ∧
    r ≤ t + {v | ∃ e ∈ S, v ∈ e}.ncard + 3

theorem noWasteStatement : NoWasteStatement := by
  intro n G S r t _ hS hr ht hW
  classical
  have hSF : (↑(G.edgeFinset.filter fun e => e ∈ S) : Set (Sym2 (Fin n))) = S := by
    ext e
    simp only [coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hA : ∀ e, e ∈ G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S) ↔
      e ∈ G.edgeSet ∧ e ∉ S := by
    intro e
    simp only [mem_sdiff, mem_filter, SimpleGraph.mem_edgeFinset, not_and]
    exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  have hdiag : ∀ X : Finset (Sym2 (Fin n)),
      X ⊆ G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S) → ∀ e ∈ X, ¬ e.IsDiag :=
    fun X hX e he => G.not_isDiag_of_mem_edgeSet ((hA e).1 (hX he)).1
  -- A cycle of `G` as a finite edge set.
  have hcyc : ∀ (H : SimpleGraph (Fin n)) (c : Set (Sym2 (Fin n))),
      c ∈ CycleCount.cycleEdgeSets H →
      ∃ (x : Fin n) (p : H.Walk x x), p.IsCycle ∧ c = ↑p.edges.toFinset := by
    rintro H c ⟨x, p, hp, rfl⟩
    refine ⟨x, p, hp, ?_⟩
    ext a
    simp
  have hcycne : ∀ (H : SimpleGraph (Fin n)) (x : Fin n) (p : H.Walk x x), p.IsCycle →
      p.edges.toFinset.Nonempty := by
    intro H x p hp
    have h3 := hp.three_le_length
    rw [← SimpleGraph.Walk.length_edges] at h3
    rcases hpl : p.edges with _ | ⟨e, l⟩
    · rw [hpl] at h3
      simp at h3
    · exact ⟨e, by simp⟩
  -- Any two nonempty even sets outside `S` share an edge.
  have hInt : Multi.Intersecting (endsOf (V := Fin n))
      (G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S)) := by
    intro X Y hX hY hXne hYne hXev hYev
    rw [mEven_iff_isEven (hdiag X hX)] at hXev
    rw [mEven_iff_isEven (hdiag Y hY)] at hYev
    by_contra hcon
    have hdisj : Disjoint X Y := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.1 hcon
    have hsub : (↑(X ∪ Y) : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
      intro e he
      rcases mem_union.1 (mem_coe.1 he) with h | h
      · exact ((hA e).1 (hX h)).1
      · exact ((hA e).1 (hY h)).1
    obtain ⟨c, hc, hcS⟩ := hW (↑(X ∪ Y)) hsub
      ((isEvenEdgeSet_coe _).2 (hXev.union_of_disjoint hYev hdisj))
    obtain ⟨x, p, hp, rfl⟩ := hcyc G c hc
    have hmemc : ∀ e ∈ X ∪ Y, e ∈ p.edges.toFinset := by
      intro e he
      have hnotS : e ∉ S := by
        rcases mem_union.1 he with h | h
        · exact ((hA e).1 (hX h)).2
        · exact ((hA e).1 (hY h)).2
      have h1 : e ∈ (↑(X ∪ Y) : Set (Sym2 (Fin n))) \ S := ⟨mem_coe.2 he, hnotS⟩
      rw [← hcS] at h1
      exact mem_coe.1 h1.1
    have hXeq : X = p.edges.toFinset :=
      eq_edges_of_subset_cycle p hp (fun e he => hmemc e (mem_union_left _ he)) hXev hXne
    obtain ⟨e, heY⟩ := hYne
    have heX : e ∈ X := by
      rw [hXeq]
      exact hmemc e (mem_union_right _ heY)
    exact (Finset.disjoint_left.1 hdisj heX) heY
  have hAcard : (G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S)).card ≤ n + 3 := by
    have h := Multi.card_le_of_intersecting (endsOf (V := Fin n)) _ Finset.univ
      (fun e _ => ⟨mem_univ _, mem_univ _⟩) hInt
    rwa [Finset.card_univ, Fintype.card_fin] at h
  constructor
  · -- No two edge-disjoint cycles outside `S`.
    intro c₁ hc₁ c₂ hc₂
    obtain ⟨x₁, p₁, hp₁, rfl⟩ := hcyc _ c₁ hc₁
    obtain ⟨x₂, p₂, hp₂, rfl⟩ := hcyc _ c₂ hc₂
    have hsubA : ∀ (x : Fin n) (p : (G.deleteEdges S).Walk x x),
        p.edges.toFinset ⊆ G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S) := by
      intro x p e he
      have h1 := p.edges_subset_edgeSet (List.mem_toFinset.1 he)
      rw [SimpleGraph.edgeSet_deleteEdges] at h1
      exact (hA e).2 h1
    have hev₁ : Multi.MEven (endsOf (V := Fin n)) p₁.edges.toFinset :=
      (mEven_iff_isEven (hdiag _ (hsubA x₁ p₁))).2
        (isEven_edges_of_isTrail p₁ hp₁.isCircuit.isTrail)
    have hev₂ : Multi.MEven (endsOf (V := Fin n)) p₂.edges.toFinset :=
      (mEven_iff_isEven (hdiag _ (hsubA x₂ p₂))).2
        (isEven_edges_of_isTrail p₂ hp₂.isCircuit.isTrail)
    obtain ⟨g, hg⟩ := hInt _ _ (hsubA x₁ p₁) (hsubA x₂ p₂) (hcycne _ x₁ p₁ hp₁)
      (hcycne _ x₂ p₂ hp₂) hev₁ hev₂
    rw [mem_inter] at hg
    exact Set.not_disjoint_iff.2 ⟨g, mem_coe.2 hg.1, mem_coe.2 hg.2⟩
  · -- The bound on the cyclomatic numbers.
    obtain ⟨c, hc, hcS⟩ := hW ∅ (Set.empty_subset _)
      (by intro v; simp)
    obtain ⟨x, p, hp, rfl⟩ := hcyc G c hc
    obtain ⟨e, he⟩ := hcycne G x p hp
    have heS : e ∈ S := by
      by_contra hnot
      have h1 : e ∈ (↑p.edges.toFinset : Set (Sym2 (Fin n))) \ S := ⟨mem_coe.2 he, hnot⟩
      rw [hcS] at h1
      exact h1.1
    have hcomp : n + 1 ≤ Nat.card (SimpleGraph.fromEdgeSet S).ConnectedComponent +
        {v | ∃ e ∈ S, v ∈ e}.ncard := by
      revert heS
      refine Sym2.ind (fun a b => ?_) e
      intro heS
      have h := card_add_one_le_components S heS
      rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have hEcard : Nat.card G.edgeSet = G.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
    have hScard : S.ncard = (G.edgeFinset.filter fun e => e ∈ S).card := by
      rw [← Set.ncard_coe_Finset, hSF]
    have hsplit : (G.edgeFinset \ (G.edgeFinset.filter fun e => e ∈ S)).card =
        G.edgeFinset.card - (G.edgeFinset.filter fun e => e ∈ S).card :=
      card_sdiff (filter_subset _ _)
    have hle : (G.edgeFinset.filter fun e => e ∈ S).card ≤ G.edgeFinset.card :=
      card_le_card (filter_subset _ _)
    omega

end Erdos1016.ExactCounting

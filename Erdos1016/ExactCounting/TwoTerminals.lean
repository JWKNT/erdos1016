import Erdos1016.ExactCounting.EvenSets

set_option autoImplicit false

/-!
# Paths between two terminals

Let `G` be a connected graph with `r + n = m + 1`, and let `u` and `v` be two
vertices. The edge set of a path from `u` to `v` has odd parity exactly at `u`
and `v`. Such edge sets form a coset of the even sets, so there are at most
`2^r` of them. Hence `G` has at most `2^r` paths from `u` to `v`.

If `G` has exactly `2^r` such paths, then every edge set with this parity
pattern is a path. Then no nonempty even set avoids a given path `p`. So the
graph without the edges of `p` is acyclic, and `p` has at least `r` edges.
-/

noncomputable section

namespace Erdos1016.ExactCounting

open Finset

/-- The edge sets of the paths from `u` to `v`. -/
def pathEdgeSets {V : Type*} (G : SimpleGraph V) (u v : V) : Set (Set (Sym2 V)) :=
  {s | ∃ p : G.Walk u v, p.IsPath ∧ s = {a | a ∈ p.edges}}

/-- The number of paths from `u` to `v`. A path is determined by its edge set. -/
def numPaths {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ := (pathEdgeSets G u v).ncard

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parity pattern of a path from `u` to `v`. -/
def IsJoin (u v : V) (X : Finset (Sym2 V)) : Prop :=
  ∀ w, par X w = (if w = u then 1 else 0) + (if w = v then 1 else 0)

instance decidableIsJoin (u v : V) : DecidablePred (IsJoin u v) := fun X =>
  inferInstanceAs (Decidable (∀ w, par X w = (if w = u then 1 else 0) + (if w = v then 1 else 0)))

/-- The two-terminal theorem for a graph on a finite vertex type, with the edge
set given as a finite set. -/
theorem two_terminal_aux (G : SimpleGraph V) (hG : G.Connected) (E : Finset (Sym2 V))
    (hE : ∀ e, e ∈ E ↔ e ∈ G.edgeSet) (r : ℕ) (hr : r + Fintype.card V = E.card + 1)
    (u v : V) :
    numPaths G u v ≤ 2 ^ r ∧
      (numPaths G u v = 2 ^ r → ∀ p : G.Walk u v, p.IsPath →
        r ≤ p.length ∧ (G.deleteEdges {a | a ∈ p.edges}).IsAcyclic) := by
  classical
  have hEvcard : (E.powerset.filter IsEven).card ≤ 2 ^ r := card_even_le_two_pow hG E hE r hr
  -- The joins inject into the even sets.
  have hJcard : (E.powerset.filter (IsJoin u v)).card ≤ (E.powerset.filter IsEven).card := by
    rcases (E.powerset.filter (IsJoin u v)).eq_empty_or_nonempty with h0 | ⟨J0, hJ0⟩
    · rw [h0]
      simp
    · have hJ0' := mem_filter.1 hJ0
      apply Finset.card_le_card_of_injOn (fun X => symmDiff X J0)
      · intro X hX
        have hX' := mem_filter.1 (mem_coe.1 hX)
        refine mem_coe.2 (mem_filter.2 ⟨mem_powerset.2 ?_, ?_⟩)
        · intro e he
          rcases mem_symmDiff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact mem_powerset.1 hX'.1 h1
          · exact mem_powerset.1 hJ0'.1 h1
        · intro w
          rw [par_symmDiff, hX'.2 w, hJ0'.2 w]
          exact CharTwo.add_self_eq_zero _
      · intro X _ X' _ h
        exact symmDiff_left_injective J0 h
  -- The edge set of a path is a join.
  have hpath : ∀ p : G.Walk u v, p.IsPath →
      p.edges.toFinset ∈ E.powerset.filter (IsJoin u v) := by
    intro p hp
    refine mem_filter.2 ⟨mem_powerset.2 ?_, fun w => par_edges_of_isTrail p hp.isTrail w⟩
    intro e he
    exact (hE e).2 (p.edges_subset_edgeSet (List.mem_toFinset.1 he))
  have hsub : pathEdgeSets G u v ⊆
      (fun X : Finset (Sym2 V) => (↑X : Set (Sym2 V))) ''
        (↑(E.powerset.filter (IsJoin u v)) : Set (Finset (Sym2 V))) := by
    rintro s ⟨p, hp, rfl⟩
    refine ⟨p.edges.toFinset, mem_coe.2 (hpath p hp), ?_⟩
    ext a
    simp
  have hfin : ((fun X : Finset (Sym2 V) => (↑X : Set (Sym2 V))) ''
      (↑(E.powerset.filter (IsJoin u v)) : Set (Finset (Sym2 V)))).Finite :=
    (Finset.finite_toSet _).image _
  have himg : ((fun X : Finset (Sym2 V) => (↑X : Set (Sym2 V))) ''
      (↑(E.powerset.filter (IsJoin u v)) : Set (Finset (Sym2 V)))).ncard ≤
      (E.powerset.filter (IsJoin u v)).card := by
    have h := Set.ncard_image_le (f := fun X : Finset (Sym2 V) => (↑X : Set (Sym2 V)))
      (Finset.finite_toSet (E.powerset.filter (IsJoin u v)))
    rwa [Set.ncard_coe_Finset] at h
  have hle : numPaths G u v ≤ (E.powerset.filter (IsJoin u v)).card :=
    (Set.ncard_le_ncard hsub hfin).trans himg
  refine ⟨hle.trans (hJcard.trans hEvcard), ?_⟩
  intro heq p hp
  -- Every join is the edge set of a path.
  have himage : pathEdgeSets G u v =
      (fun X : Finset (Sym2 V) => (↑X : Set (Sym2 V))) ''
        (↑(E.powerset.filter (IsJoin u v)) : Set (Finset (Sym2 V))) := by
    apply Set.eq_of_subset_of_ncard_le hsub _ hfin
    calc _ ≤ (E.powerset.filter (IsJoin u v)).card := himg
      _ ≤ 2 ^ r := hJcard.trans hEvcard
      _ = numPaths G u v := heq.symm
  have hall : ∀ X ∈ E.powerset.filter (IsJoin u v),
      ∃ q : G.Walk u v, q.IsPath ∧ X ⊆ q.edges.toFinset := by
    intro X hX
    have hmem : (↑X : Set (Sym2 V)) ∈ pathEdgeSets G u v := by
      rw [himage]
      exact ⟨X, mem_coe.2 hX, rfl⟩
    obtain ⟨q, hq, hXq⟩ := hmem
    refine ⟨q, hq, ?_⟩
    intro a ha
    have h1 : a ∈ (↑X : Set (Sym2 V)) := mem_coe.2 ha
    rw [hXq] at h1
    exact List.mem_toFinset.2 h1
  -- No nonempty even set avoids the path `p`.
  have hkey : ∀ C : Finset (Sym2 V), C ⊆ E → IsEven C → Disjoint C p.edges.toFinset →
      C = ∅ := by
    intro C hCE hCev hdisj
    have hmem : C ∪ p.edges.toFinset ∈ E.powerset.filter (IsJoin u v) := by
      refine mem_filter.2 ⟨mem_powerset.2 ?_, fun w => ?_⟩
      · exact union_subset hCE (mem_powerset.1 (mem_filter.1 (hpath p hp)).1)
      · rw [par_union_of_disjoint hdisj, hCev w, zero_add]
        exact par_edges_of_isTrail p hp.isTrail w
    obtain ⟨q, hq, hXq⟩ := hall _ hmem
    exact eq_empty_of_subset_path q hq (subset_union_left.trans hXq) hCev
  constructor
  · -- The path has at least `r` edges.
    have hinj : (E.powerset.filter IsEven).card ≤ (p.edges.toFinset.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun X => X ∩ p.edges.toFinset)
      · intro X _
        exact mem_coe.2 (mem_powerset.2 inter_subset_right)
      · intro X hX X' hX' h
        have hXm := mem_filter.1 (mem_coe.1 hX)
        have hXm' := mem_filter.1 (mem_coe.1 hX')
        have h' : X ∩ p.edges.toFinset = X' ∩ p.edges.toFinset := h
        have hC : symmDiff X X' = ∅ := by
          apply hkey
          · intro e he
            rcases mem_symmDiff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact mem_powerset.1 hXm.1 h1
            · exact mem_powerset.1 hXm'.1 h1
          · exact hXm.2.symmDiff hXm'.2
          · rw [Finset.disjoint_left]
            intro e he heP
            have h1 : e ∈ X ↔ e ∈ X' := by
              have h2 : e ∈ X ∩ p.edges.toFinset ↔ e ∈ X' ∩ p.edges.toFinset := by rw [h']
              simpa [mem_inter, heP] using h2
            rcases mem_symmDiff.1 he with ⟨h2, h3⟩ | ⟨h2, h3⟩
            · exact h3 (h1.1 h2)
            · exact h3 (h1.2 h2)
        exact symmDiff_eq_bot.1 hC
    rw [card_powerset, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
      SimpleGraph.Walk.length_edges] at hinj
    have h2 : 2 ^ r ≤ 2 ^ p.length := by
      calc 2 ^ r = numPaths G u v := heq.symm
        _ ≤ (E.powerset.filter (IsJoin u v)).card := hle
        _ ≤ (E.powerset.filter IsEven).card := hJcard
        _ ≤ 2 ^ p.length := hinj
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  · -- The graph without the edges of the path is acyclic.
    intro x c hc
    have hCne : c.edges.toFinset.Nonempty := by
      have h3 := hc.three_le_length
      rw [← SimpleGraph.Walk.length_edges] at h3
      rcases hcl : c.edges with _ | ⟨e, l⟩
      · rw [hcl] at h3
        simp at h3
      · exact ⟨e, by simp⟩
    have hCE : c.edges.toFinset ⊆ E := by
      intro e he
      have h1 := c.edges_subset_edgeSet (List.mem_toFinset.1 he)
      exact (hE e).2 (SimpleGraph.edgeSet_subset_edgeSet.2 (SimpleGraph.deleteEdges_le _) h1)
    have hdisj : Disjoint c.edges.toFinset p.edges.toFinset := by
      rw [Finset.disjoint_left]
      intro e he heP
      have h1 := c.edges_subset_edgeSet (List.mem_toFinset.1 he)
      rw [SimpleGraph.edgeSet_deleteEdges] at h1
      exact h1.2 (List.mem_toFinset.1 heP)
    exact hCne.ne_empty
      (hkey _ hCE (isEven_edges_of_isTrail c hc.isCircuit.isTrail) hdisj)

/-- A connected simple graph on `Fin n` with cyclomatic number `r` has at most
`2^r` paths between two given vertices. If it has exactly `2^r`, then each of
these paths has at least `r` edges, and the graph without the edges of any one
of them is acyclic. -/
def TwoTerminalStatement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ) (u v : Fin n),
    G.Connected → r + n = Nat.card G.edgeSet + 1 →
      numPaths G u v ≤ 2 ^ r ∧
      (numPaths G u v = 2 ^ r →
        ∀ p : G.Walk u v, p.IsPath →
          r ≤ p.length ∧ (G.deleteEdges {a | a ∈ p.edges}).IsAcyclic)

theorem twoTerminalStatement : TwoTerminalStatement := by
  intro n G r u v hG hr
  classical
  apply two_terminal_aux G hG G.edgeFinset (fun e => SimpleGraph.mem_edgeFinset) r _ u v
  have hcard : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [Fintype.card_fin]
  omega

end Erdos1016.ExactCounting

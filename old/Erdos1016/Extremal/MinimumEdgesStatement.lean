import Erdos1016.Extremal.CompleteGraphWitness

set_option autoImplicit false

/-!
# Community Erdős #1016 notation

The repository `baobingzhang/jsp-000846-erdos1016-lean` writes the extremal
quantity as the minimum number of edges in a pancyclic graph, and then defines
`h n` by subtracting `n` in the integers.  This module records those
definitions verbatim in a separate namespace and proves that, from order three
onward, its `h` agrees with the natural excess formulation used by this
development.  The theorem transfer below is a transfer of formulations; it
does not provide a proof of `MainTheorem`.
-/

noncomputable section

namespace Erdos1016.Problem1016.CommunityStatement

/-- The community statement's cycle predicate. -/
def HasCycleOfLength {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = ℓ

/-- Pancyclicity as used in the community statement. -/
def IsPancyclic {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ Fintype.card V → HasCycleOfLength G ℓ

/-- The set of edge counts of pancyclic graphs on `Fin n`. -/
def pancyclicEdgeCounts (n : ℕ) : Set ℕ :=
  {m | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ G.edgeSet.ncard = m}

/-- Community definition: the minimum edge count among pancyclic graphs. -/
noncomputable def minPancyclicEdges (n : ℕ) : ℕ :=
  sInf (pancyclicEdgeCounts n)

/-- Community definition of the excess, retained as integer subtraction. -/
noncomputable def h (n : ℕ) : ℤ := (minPancyclicEdges n : ℤ) - n

end Erdos1016.Problem1016.CommunityStatement

namespace Erdos1016.Problem1016

open CommunityStatement

local instance communityStatementSimpleGraphEdgeFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    Fintype G.edgeSet := Fintype.ofFinite _

private theorem communityPancyclic_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    CommunityStatement.IsPancyclic G ↔ IsPancyclic G := by
  rfl

private theorem edgeCount_eq_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype.card G.edgeSet = G.edgeSet.ncard := by
  classical
  rw [← SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset]
  symm
  exact Set.ncard_eq_toFinset_card G.edgeSet

private theorem n_le_edgeCount_of_pancyclic {n : ℕ}
    (G : SimpleGraph (Fin n)) (hn : 3 ≤ n) (hG : IsPancyclic G) :
    n ≤ G.edgeSet.ncard := by
  have hcycle : HasCycleLength G n := by
    apply hG n hn
    simp
  obtain ⟨_, p, hp, hlen⟩ := hcycle
  have hcard : p.length ≤ Fintype.card G.edgeSet := by
    have h := hp.isTrail.length_le_card_edgeFinset
    simpa using h
  rw [hlen] at hcard
  rw [← edgeCount_eq_ncard G]
  exact hcard

private theorem pancyclicEdgeCounts_nonempty (n : ℕ) :
    (CommunityStatement.pancyclicEdgeCounts n).Nonempty := by
  classical
  refine ⟨(completeGraph (Fin n)).edgeSet.ncard, ?_⟩
  exact ⟨completeGraph (Fin n),
    (communityPancyclic_iff _).2 (completeGraph_isPancyclic n), rfl⟩

/-- For `n ≥ 3`, the two natural-valued extremal minima differ only by the
edge-count offset `n`. -/
theorem community_minPancyclicEdges_sub_eq_h (n : ℕ) (hn : 3 ≤ n) :
    CommunityStatement.minPancyclicEdges n - n = h n := by
  classical
  have hExNonempty : (candidateExcesses n).Nonempty :=
    candidateExcesses_nonempty n
  have hEdgesNonempty :
      (CommunityStatement.pancyclicEdgeCounts n).Nonempty :=
    pancyclicEdgeCounts_nonempty n
  have hExMem : h n ∈ candidateExcesses n := by
    change sInf (candidateExcesses n) ∈ candidateExcesses n
    exact Nat.sInf_mem hExNonempty
  have hEdgesMem :
      CommunityStatement.minPancyclicEdges n ∈
        CommunityStatement.pancyclicEdgeCounts n := by
    change sInf (CommunityStatement.pancyclicEdgeCounts n) ∈ _
    exact Nat.sInf_mem hEdgesNonempty
  apply Nat.le_antisymm
  · obtain ⟨G, hG, hExG⟩ := hExMem
    have hG' : IsPancyclic G := hG
    have hnG : n ≤ G.edgeSet.ncard := n_le_edgeCount_of_pancyclic G hn hG'
    have hcard : Fintype.card G.edgeSet = G.edgeSet.ncard := edgeCount_eq_ncard G
    have hsum : G.edgeSet.ncard = h n + n := by
      have : Fintype.card G.edgeSet - n = h n := by
        simpa [excess, hcard] using hExG
      omega
    have hminLe : CommunityStatement.minPancyclicEdges n ≤ G.edgeSet.ncard :=
      Nat.sInf_le ⟨G, (communityPancyclic_iff _).2 hG', rfl⟩
    omega
  · obtain ⟨G, hG, hcard⟩ := hEdgesMem
    have hG' : IsPancyclic G := (communityPancyclic_iff _).1 hG
    have hnG : n ≤ G.edgeSet.ncard := n_le_edgeCount_of_pancyclic G hn hG'
    have hminG : h n ≤ excess n G := h_le_excess_of_isPancyclic n G hG'
    have hcard' : G.edgeSet.ncard =
        CommunityStatement.minPancyclicEdges n := hcard
    have hminex : excess n G =
        CommunityStatement.minPancyclicEdges n - n := by
      unfold excess
      rw [edgeCount_eq_ncard G, hcard']
    rw [hminex] at hminG
    exact hminG

/-- The integer-valued `h` in the public community statement agrees with the
natural excess `h` used in this project, for every order at least three. -/
theorem community_h_eq_project_h (n : ℕ) (hn : 3 ≤ n) :
    CommunityStatement.h n = (h n : ℤ) := by
  have hnmin : n ≤ CommunityStatement.minPancyclicEdges n := by
    have hEdgesNonempty := pancyclicEdgeCounts_nonempty n
    have hEdgesMem :
        CommunityStatement.minPancyclicEdges n ∈
          CommunityStatement.pancyclicEdgeCounts n := by
      change sInf (CommunityStatement.pancyclicEdgeCounts n) ∈ _
      exact Nat.sInf_mem hEdgesNonempty
    obtain ⟨G, hG, hcount⟩ := hEdgesMem
    exact hcount ▸ n_le_edgeCount_of_pancyclic G hn
      ((communityPancyclic_iff _).1 hG)
  change (CommunityStatement.minPancyclicEdges n : ℤ) - n = (h n : ℤ)
  rw [← Nat.cast_sub hnmin]
  have hnat := community_minPancyclicEdges_sub_eq_h n hn
  exact_mod_cast hnat

/-- The already-established asymptotic statement transfers verbatim to the
community definition of `h`. -/
theorem mainTheorem_community_statement :
    MainTheorem ↔
      ∃ Aminus Aplus : ℝ, ∀ n : ℕ, 3 ≤ n →
        Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) - Aminus ≤
            CommunityStatement.h n ∧
        CommunityStatement.h n ≤
            Real.logb 2 (n : ℝ) + (Erdos1016.Extremal.logStar n : ℝ) + Aplus := by
  constructor
  · rintro ⟨Aminus, Aplus, hbounds⟩
    refine ⟨Aminus, Aplus, ?_⟩
    intro n hn
    have h := hbounds n hn
    rw [community_h_eq_project_h n hn]
    exact h
  · rintro ⟨Aminus, Aplus, hbounds⟩
    refine ⟨Aminus, Aplus, ?_⟩
    intro n hn
    have h := hbounds n hn
    rw [community_h_eq_project_h n hn] at h
    exact h

end Erdos1016.Problem1016

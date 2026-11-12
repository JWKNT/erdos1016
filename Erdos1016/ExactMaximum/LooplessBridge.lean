import Erdos1016.Graph.Multigraph.LoopDecomposition
import Erdos1016.ExactMaximum.Cycles
import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# A multigraph without loops as a network

The statements of the exact maximum are about `FiniteMultiGraph`, where loops are allowed.
Sections 5 to 7 of the paper work with multigraphs without loops, and their formalisation uses
`BoundaryTrace.Network`. This file links the two models through
`FiniteMultiGraph.looplessNetwork`, the network of the edges that are not loops. Parallel edges
are kept.

For an edge word `x` without a loop:

* the selected degrees and the selected graph of `x` are those of `nonloopWord G x`
  (`selectedDegree_eq_deg`, `selectedGraph_eq`);
* `x` is a cycle of the multigraph if and only if `nonloopWord G x` is a cycle of the network
  (`isCycleWord_iff_looplessNetwork`).

For a multigraph `G` without loops:

* `G` and its network have the same number of cycles (`numCycles_eq_looplessNetwork`), the same
  rank (`cycleRank_eq_networkRank`), the same degrees (`degree_eq_deg`), and one is connected if
  and only if the other is (`connected_iff_looplessNetwork`);
* the cut edges of a vertex set are the crossing edges (`mem_cutEdges_iff_crosses`), and a side
  contains a cycle of `G` if and only if it contains a cycle of the network
  (`hasCycleIn_iff_looplessNetwork`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.FiniteMultiGraph

open BoundaryTrace BoundaryDecay

local instance looplessBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- No edge is a loop. -/
def IsLoopless : Prop := ∀ e, G.src e ≠ G.dst e

theorem isLoopless_iff_not_hasLoop : G.IsLoopless ↔ ¬ G.HasLoop := by
  constructor
  · rintro h ⟨e, he⟩
    exact h e he
  · intro h e he
    exact h ⟨e, he⟩

/-! ### Edge words without a loop -/

/-- The selected degrees of an edge word without a loop are the degrees of its word in the
network. -/
theorem selectedDegree_eq_deg (x : G.EdgeWord) (hx : ∀ e, G.src e = G.dst e → x e = 0)
    (v : G.Vertex) :
    G.selectedDegree x v = (looplessNetwork G).deg (nonloopWord G x) v := by
  rw [G.selectedDegree_eq_sum_endpoints x v, Network.deg_eq_sum]
  have h := Network.sum_eq_sum_sub (fun e : G.Edge => G.src e ≠ G.dst e)
    (fun e => if x e ≠ 0 then
      (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) else 0)
    (by
      intro e he
      have hloop : G.src e = G.dst e := Classical.not_not.1 he
      simp [hx e hloop])
  refine Eq.trans h ?_
  apply Finset.sum_congr rfl
  intro e _
  have hne : G.src e.1 ≠ G.dst e.1 := e.2
  by_cases hx0 : x e.1 = 0 <;> by_cases hs : G.src e.1 = v <;> by_cases hd : G.dst e.1 = v
  all_goals first
    | (exfalso; exact hne (hs.trans hd.symm))
    | simp [nonloopWord, looplessNetwork, hx0, hs, hd]

/-- The selected graph of an edge word is the selected graph of its word in the network. -/
theorem selectedGraph_eq (x : G.EdgeWord) :
    G.selectedGraph x = (looplessNetwork G).selectedGraph (nonloopWord G x) := by
  ext u w
  constructor
  · rintro ⟨hne, e, he, hends⟩
    have hloop : G.src e ≠ G.dst e := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact hne
      · rw [h1, h2]
        exact hne.symm
    exact ⟨⟨e, hloop⟩, he, hends⟩
  · rintro ⟨e, he, hends⟩
    have hloop : G.src e.1 ≠ G.dst e.1 := e.2
    refine ⟨?_, e.1, he, hends⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro huw
      exact hloop (h1.trans (huw.trans h2.symm))
    · intro huw
      exact hloop (h1.trans (huw.symm.trans h2.symm))

/-- An edge word without a loop is zero if and only if its word in the network is zero. -/
theorem ne_zero_iff_nonloopWord (x : G.EdgeWord) (hx : ∀ e, G.src e = G.dst e → x e = 0) :
    x ≠ 0 ↔ nonloopWord G x ≠ 0 := by
  constructor
  · intro h h0
    apply h
    funext e
    by_cases he : G.src e = G.dst e
    · exact hx e he
    · exact congrFun h0 ⟨e, he⟩
  · intro h h0
    apply h
    funext e
    exact congrFun h0 e.1

/-- **Cycles agree.** An edge word without a loop is a cycle of the multigraph if and only if
its word in the network is a cycle. -/
theorem isCycleWord_iff_looplessNetwork (x : G.EdgeWord)
    (hx : ∀ e, G.src e = G.dst e → x e = 0) :
    G.IsCycleWord x ↔ (looplessNetwork G).IsCycleWord (nonloopWord G x) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(G.ne_zero_iff_nonloopWord x hx).1 h1, fun v => ?_, fun u v hu hv => ?_⟩
    · rw [← G.selectedDegree_eq_deg x hx v]
      exact h2 v
    · rw [← G.selectedGraph_eq x]
      apply h3 u v
      · rw [G.selectedDegree_eq_deg x hx u]
        exact hu
      · rw [G.selectedDegree_eq_deg x hx v]
        exact hv
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(G.ne_zero_iff_nonloopWord x hx).2 h1, fun v => ?_, fun u v hu hv => ?_⟩
    · rw [G.selectedDegree_eq_deg x hx v]
      exact h2 v
    · rw [G.selectedGraph_eq x]
      apply h3 u v
      · rw [← G.selectedDegree_eq_deg x hx u]
        exact hu
      · rw [← G.selectedDegree_eq_deg x hx v]
        exact hv

/-! ### Multigraphs without loops -/

variable {G}

/-- In a multigraph without loops, every edge word is without a loop. -/
theorem IsLoopless.word (h : G.IsLoopless) (x : G.EdgeWord) :
    ∀ e, G.src e = G.dst e → x e = 0 := fun e he => absurd he (h e)

/-- **The number of cycles.** A multigraph without loops and its network have the same number of
cycles. -/
theorem numCycles_eq_looplessNetwork (h : G.IsLoopless) :
    G.numCycles = (looplessNetwork G).numCycles := by
  let f : {x : G.EdgeWord // G.IsCycleWord x} →
      {y : (looplessNetwork G).Word // (looplessNetwork G).IsCycleWord y} := fun x =>
    ⟨nonloopWord G x.1, (G.isCycleWord_iff_looplessNetwork x.1 (h.word x.1)).1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val hab
      apply Subtype.ext
      funext e
      exact congrFun h' ⟨e, h e⟩
    · rintro ⟨y, hy⟩
      refine ⟨⟨joinLoopWord G 0 y, ?_⟩, ?_⟩
      · rw [G.isCycleWord_iff_looplessNetwork _ (h.word _), nonloopWord_joinLoopWord]
        exact hy
      · apply Subtype.ext
        exact nonloopWord_joinLoopWord G 0 y
  exact Nat.card_eq_of_bijective f hf

/-- The rank of a multigraph is the number of its loops plus the rank of its network. -/
theorem cycleRank_eq_card_loops_add (G : FiniteMultiGraph) :
    G.cycleRank = Fintype.card (LoopEdge G) + networkRank (looplessNetwork G) := by
  have h := (loopCycleSpaceEquiv G).finrank_eq
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- **The rank.** A multigraph without loops and its network have the same rank. -/
theorem cycleRank_eq_networkRank (h : G.IsLoopless) :
    G.cycleRank = networkRank (looplessNetwork G) := by
  have h0 : Fintype.card (LoopEdge G) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun e => h e.1 e.2⟩
  rw [cycleRank_eq_card_loops_add, h0, zero_add]

/-- A multigraph is connected if and only if its network is connected. -/
theorem connected_iff_looplessNetwork (G : FiniteMultiGraph) :
    G.toSimpleGraph.Connected ↔ (looplessNetwork G).graph.Connected := by
  rw [looplessNetwork_graph]

/-- **The degrees.** In a multigraph without loops, the degree of a vertex is its degree in the
word of all edges of the network. -/
theorem degree_eq_deg (h : G.IsLoopless) (v : G.Vertex) :
    G.degree v = (looplessNetwork G).deg (fun _ => 1) v :=
  G.selectedDegree_eq_deg (fun _ => 1) (h.word _) v

/-! ### Cuts -/

/-- An edge that is not a loop is a cut edge of `U` if and only if it crosses the cut of the
network. -/
theorem mem_cutEdges_iff_crosses (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (e : NonloopEdge G) :
    e.1 ∈ G.cutEdges U ↔ (looplessNetwork G).crosses (fun v => v ∈ U) e := by
  unfold cutEdges
  rw [Finset.mem_filter]
  show (e.1 ∈ Finset.univ ∧ ((G.src e.1 ∈ U ∧ G.dst e.1 ∉ U) ∨
    (G.src e.1 ∉ U ∧ G.dst e.1 ∈ U))) ↔ ¬ (G.src e.1 ∈ U ↔ G.dst e.1 ∈ U)
  constructor
  · rintro ⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ hiff
    · exact h2 (hiff.1 h1)
    · exact h1 (hiff.2 h2)
  · intro hc
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases h1 : G.src e.1 ∈ U
    · exact Or.inl ⟨h1, fun h2 => hc ⟨fun _ => h2, fun _ => h1⟩⟩
    · exact Or.inr ⟨h1, Classical.not_not.1 fun h2 =>
        hc ⟨fun h => absurd h h1, fun h => absurd h h2⟩⟩

/-- **Cycles in a side.** In a multigraph without loops, the vertex set `U` contains a cycle if
and only if the network has a cycle within the edges with both ends in `U`. -/
theorem hasCycleIn_iff_looplessNetwork (h : G.IsLoopless) (U : Finset G.Vertex) :
    G.HasCycleIn U ↔ ∃ y : (looplessNetwork G).Word, (looplessNetwork G).IsCycleWord y ∧
      Network.Within y ((looplessNetwork G).inside fun v => v ∈ U) := by
  constructor
  · rintro ⟨x, hx, hsupp⟩
    exact ⟨nonloopWord G x, (G.isCycleWord_iff_looplessNetwork x (h.word x)).1 hx,
      fun e he => hsupp e.1 he⟩
  · rintro ⟨y, hy, hw⟩
    refine ⟨joinLoopWord G 0 y, ?_, ?_⟩
    · rw [G.isCycleWord_iff_looplessNetwork _ (h.word _), nonloopWord_joinLoopWord]
      exact hy
    · intro e he
      have he' : y ⟨e, h e⟩ ≠ 0 := by
        intro h0
        apply he
        show (if hl : G.src e = G.dst e then (0 : LoopEdge G → F₂) ⟨e, hl⟩ else y ⟨e, hl⟩) = 0
        rw [dif_neg (h e)]
        exact h0
      exact hw ⟨e, h e⟩ he'

end Erdos1016.FiniteMultiGraph

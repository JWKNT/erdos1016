import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Branch vertices of a finite terminal forest

A finite forest has no more vertices of degree at least three than vertices
of degree one. Consequently a forest pruned until every remaining
leaf is a terminal has at most as many branch vertices as terminals.
Isolated vertices are allowed throughout and do not consume the terminal budget.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.TerminalForest

variable {V : Type*} [Fintype V]

local instance terminalForestDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance componentFintype (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

/-- In a nontrivial tree the stronger branch-versus-leaf bound has a slack
of two. -/
theorem tree_branch_card_add_two_le_leaf_card
    (G : SimpleGraph V) (hG : G.IsTree) (hV : 2 ≤ Fintype.card V) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card + 2 ≤
      (Finset.univ.filter (fun v => G.degree v = 1)).card := by
  have hpos (v : V) : 1 ≤ G.degree v := by
    obtain ⟨w, hw⟩ : ∃ w : V, w ≠ v := by
      by_contra hn
      have hall : ∀ w : V, w = v := by simpa using hn
      have : Subsingleton V := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have := (Fintype.card_le_one_iff_subsingleton (α := V)).2 this
      omega
    obtain ⟨p⟩ := hG.isConnected v w
    cases p with
    | nil => exact (hw rfl).elim
    | cons hadj p =>
      exact (G.degree_pos_iff_exists_adj v).2 ⟨_, hadj⟩
  have hpoint (v : V) :
      2 + (if 3 ≤ G.degree v then 1 else 0) ≤
        G.degree v + (if G.degree v = 1 then 1 else 0) := by
    have := hpos v
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  have hdegree := G.sum_degrees_eq_twice_card_edges
  have hcard := hG.card_edgeFinset
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Finset.card_filter] at hsum
  omega

/-- The singleton tree case contributes no branch vertices or leaves. -/
theorem tree_branch_card_le_leaf_card (G : SimpleGraph V) (hG : G.IsTree) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤
      (Finset.univ.filter (fun v => G.degree v = 1)).card := by
  by_cases hV : 2 ≤ Fintype.card V
  · exact (Nat.le_add_right _ _).trans
      (tree_branch_card_add_two_le_leaf_card G hG hV)
  · have hempty : Finset.univ.filter (fun v => 3 ≤ G.degree v) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro v hv
      have hdegree := G.degree_lt_card_verts v
      have hbranch := (Finset.mem_filter.mp hv).2
      omega
    simp [hempty]

/-- Inducing a connected component preserves the degree of every vertex. -/
theorem component_degree (G : SimpleGraph V) (c : G.ConnectedComponent)
    (v : c.supp) : (G.induce c.supp).degree v = G.degree v.1 := by
  apply G.degree_induce_of_neighborSet_subset
  intro w hw
  exact (c.mem_supp_congr_adj hw).mp v.2

/-- Predicate counts split exactly over the actual connected components. -/
theorem sum_component_filter_card (G : SimpleGraph V) (P : V → Prop)
    [DecidablePred P] :
    (∑ c : G.ConnectedComponent,
      (Finset.univ.filter (fun v : c.supp => P v.1)).card) =
        (Finset.univ.filter P).card := by
  let e : (Σ c : G.ConnectedComponent, {v : c.supp // P v.1}) ≃ {v : V // P v} :=
    { toFun := fun z => ⟨z.2.1.1, z.2.2⟩
      invFun := fun v => ⟨G.connectedComponentMk v.1,
        ⟨⟨v.1, by simp [SimpleGraph.ConnectedComponent.mem_supp_iff]⟩, v.2⟩⟩
      left_inv := by
        rintro ⟨c, ⟨⟨v, hv⟩, hp⟩⟩
        have hc : G.connectedComponentMk v = c :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c v).1 hv
        subst c
        rfl
      right_inv := by intro v; rfl }
  simpa only [Fintype.card_sigma, Fintype.card_subtype] using Fintype.card_congr e

/-- Acyclicity alone suffices; disconnected forests and isolated vertices
require no extra cases in this statement. -/
theorem branch_card_le_leaf_card (G : SimpleGraph V) (hG : G.IsAcyclic) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤
      (Finset.univ.filter (fun v => G.degree v = 1)).card := by
  have hcomponent (c : G.ConnectedComponent) :
      (Finset.univ.filter (fun v : c.supp => 3 ≤ G.degree v.1)).card ≤
        (Finset.univ.filter (fun v : c.supp => G.degree v.1 = 1)).card := by
    have htree : (G.induce c.supp).IsTree := by
      refine ⟨c.connected_induce_supp, ?_⟩
      intro v p hp
      let emb : G.induce c.supp ↪g G := SimpleGraph.Embedding.induce c.supp
      exact hG (p.map emb.toHom) (hp.map emb.injective)
    simpa only [component_degree] using tree_branch_card_le_leaf_card _ htree
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hcomponent c)
  calc
    _ = ∑ c : G.ConnectedComponent,
        (Finset.univ.filter (fun v : c.supp => 3 ≤ G.degree v.1)).card :=
      (sum_component_filter_card G (fun v => 3 ≤ G.degree v)).symm
    _ ≤ ∑ c : G.ConnectedComponent,
        (Finset.univ.filter (fun v : c.supp => G.degree v.1 = 1)).card := hsum
    _ = _ := sum_component_filter_card G (fun v => G.degree v = 1)

/-- The counting step used after pruning nonterminal leaves. -/
theorem branch_card_le_terminal_card (G : SimpleGraph V) (hG : G.IsAcyclic)
    (terminals : Finset V) (hleaf : ∀ v, G.degree v = 1 → v ∈ terminals) :
    (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ terminals.card := by
  refine (branch_card_le_leaf_card G hG).trans (Finset.card_le_card ?_)
  intro v hv
  exact hleaf v (Finset.mem_filter.mp hv).2

/-- Any distinct family represented by branch vertices of a terminal forest
inherits its terminal budget. The representation is explicit and injective. -/
theorem family_card_le_terminal_card {ι : Type*} (s : Finset ι)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (terminals : Finset V)
    (hleaf : ∀ v, G.degree v = 1 → v ∈ terminals)
    (vertex : ι → V) (hinj : Set.InjOn vertex ↑s)
    (hbranch : ∀ i ∈ s, 3 ≤ G.degree (vertex i)) :
    s.card ≤ terminals.card := by
  refine (Finset.card_le_card_of_injOn vertex ?_ hinj).trans
    (branch_card_le_terminal_card G hG terminals hleaf)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbranch i hi⟩

/-- Retain exactly the edges lying on paths between terminals. For a forest
this is a canonical way to prune all nonterminal leaves, keeping the original
vertex type and allowing the discarded vertices to become isolated. -/
def span (G : SimpleGraph V) (terminals : Finset V) : SimpleGraph V where
  Adj u v := ∃ a ∈ terminals, ∃ b ∈ terminals, ∃ p : G.Walk a b,
    p.IsPath ∧ p.toSubgraph.Adj u v
  symm := by
    rintro u v ⟨a, ha, b, hb, p, hp, huv⟩
    exact ⟨a, ha, b, hb, p, hp, huv.symm⟩
  loopless := by
    rintro u ⟨a, ha, b, hb, p, hp, huu⟩
    exact G.loopless u huu.adj_sub

omit [Fintype V] in
theorem span_le (G : SimpleGraph V) (terminals : Finset V) :
    span G terminals ≤ G := by
  rintro u v ⟨a, ha, b, hb, p, hp, huv⟩
  exact huv.adj_sub

omit [Fintype V] in
theorem span_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic)
    (terminals : Finset V) : (span G terminals).IsAcyclic := by
  intro u p hp
  let f : span G terminals →g G :=
    { toFun := id, map_rel' := by intro a b hab; exact span_le G terminals hab }
  exact hG (p.map f) (hp.map (by intro a b hab; exact hab))

/-- A leaf of the terminal span must itself be a terminal. This also proves
the pruning condition, rather than requesting it as an input. -/
theorem span_leaf_mem (G : SimpleGraph V) (terminals : Finset V) (u : V)
    (hdegree : (span G terminals).degree u = 1) : u ∈ terminals := by
  let H := span G terminals
  obtain ⟨v, hv⟩ := (H.degree_pos_iff_exists_adj u).1 (by
    change 0 < (span G terminals).degree u
    omega)
  obtain ⟨a, ha, b, hb, p, hp, huv⟩ := hv
  by_contra hu
  have hua : u ≠ a := by rintro rfl; exact hu ha
  have hub : u ≠ b := by rintro rfl; exact hu hb
  obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (SimpleGraph.Walk.mem_support_of_adj_toSubgraph huv)
  have hi0 : i ≠ 0 := by
    intro hz
    simp only [hz, SimpleGraph.Walk.getVert_zero] at hi
    exact hua hi.symm
  have hilt : i < p.length := by
    by_contra hn
    have heq : i = p.length := by omega
    simp only [heq, SimpleGraph.Walk.getVert_length] at hi
    exact hub hi.symm
  have hprev : H.Adj u (p.getVert (i - 1)) := by
    refine ⟨a, ha, b, hb, p, hp, ?_⟩
    have h := (p.toSubgraph_adj_getVert (by omega : i - 1 < p.length)).symm
    have heq : i - 1 + 1 = i := by omega
    simpa only [heq, hi] using h
  have hnext : H.Adj u (p.getVert (i + 1)) := by
    refine ⟨a, ha, b, hb, p, hp, ?_⟩
    simpa only [hi] using p.toSubgraph_adj_getVert hilt
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
    omega
  have hpair : {p.getVert (i - 1), p.getVert (i + 1)} ⊆ H.neighborFinset u := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hprev
    · exact (H.mem_neighborFinset _ _).mpr hnext
  have htwo : 2 ≤ H.degree u := by
    have hcard := Finset.card_le_card hpair
    simpa [hne] using hcard
  change H.degree u = 1 at hdegree
  omega

/-- The terminal budget for the actual, canonically constructed pruned forest. -/
theorem span_branch_card_le (G : SimpleGraph V) (hG : G.IsAcyclic)
    (terminals : Finset V) :
    (Finset.univ.filter (fun v => 3 ≤ (span G terminals).degree v)).card ≤
      terminals.card :=
  branch_card_le_terminal_card _ (span_isAcyclic G hG terminals) terminals
    (span_leaf_mem G terminals)

theorem family_card_le_of_span_branches {ι : Type*} (s : Finset ι)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (terminals : Finset V)
    (vertex : ι → V) (hinj : Set.InjOn vertex ↑s)
    (hbranch : ∀ i ∈ s, 3 ≤ (span G terminals).degree (vertex i)) :
    s.card ≤ terminals.card :=
  family_card_le_terminal_card s _ (span_isAcyclic G hG terminals) terminals
    (span_leaf_mem G terminals) vertex hinj hbranch

omit [Fintype V] in
/-- In a forest, two paths with the same starting vertex and different first
steps cannot meet again. -/
theorem routes_intersect_only_at_start (G : SimpleGraph V) (hG : G.IsAcyclic)
    {w a b : V} (p : G.Walk w a) (q : G.Walk w b)
    (hp : p.IsPath) (hq : q.IsPath) (hfirst : p.snd ≠ q.snd)
    {x : V} (hxp : x ∈ p.support) (hxq : x ∈ q.support) : x = w := by
  by_contra hne
  have heq : p.takeUntil x hxp = q.takeUntil x hxq :=
    congrArg Subtype.val (hG.path_unique
      ⟨p.takeUntil x hxp, hp.takeUntil hxp⟩
      ⟨q.takeUntil x hxq, hq.takeUntil hxq⟩)
  have hsnd := congrArg SimpleGraph.Walk.snd heq
  rw [SimpleGraph.Walk.snd_takeUntil hne p hxp,
    SimpleGraph.Walk.snd_takeUntil hne q hxq] at hsnd
  exact hfirst hsnd

omit [Fintype V] in
/-- Joining two such routes produces an actual terminal-to-terminal path. -/
theorem joined_routes_isPath (G : SimpleGraph V) (hG : G.IsAcyclic)
    {w a b : V} (p : G.Walk w a) (q : G.Walk w b)
    (hp : p.IsPath) (hq : q.IsPath) (hfirst : p.snd ≠ q.snd) :
    (p.reverse.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hp.reverse.support_nodup, hq.support_nodup.tail, ?_⟩
  apply List.disjoint_left.mpr
  intro x hxp hxq
  have hx : x = w := routes_intersect_only_at_start G hG p q hp hq hfirst
    (by simpa using hxp) (List.mem_of_mem_tail hxq)
  have hn : w ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [q.support_eq_cons, List.nodup_cons] at hn
    exact hn.1
  exact hn (hx ▸ hxq)

omit [Fintype V] in
/-- Every nontrivial terminal route survives pruning as soon as a terminal
route in a different branch is present. -/
theorem span_adj_of_two_terminal_routes (G : SimpleGraph V) (hG : G.IsAcyclic)
    (terminals : Finset V) {w a b : V} (ha : a ∈ terminals) (hb : b ∈ terminals)
    (p : G.Walk w a) (q : G.Walk w b) (hp : p.IsPath) (hq : q.IsPath)
    (hpnontrivial : ¬ p.Nil) (hfirst : p.snd ≠ q.snd) :
    (span G terminals).Adj w p.snd := by
  refine ⟨a, ha, b, hb, p.reverse.append q,
    joined_routes_isPath G hG p q hp hq hfirst, ?_⟩
  rw [SimpleGraph.Walk.toSubgraph_append, SimpleGraph.Walk.toSubgraph_reverse]
  exact Or.inl (p.toSubgraph_adj_snd hpnontrivial)

/-- Distinct terminal-containing branches give distinct retained incidences.
The route index may be the actual finite link type of a graph. -/
theorem route_card_le_span_degree {ι : Type*} [Fintype ι] [Nontrivial ι]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (terminals : Finset V)
    (w : V) (terminal : ι → V) (hterminal : ∀ i, terminal i ∈ terminals)
    (route : ∀ i, G.Walk w (terminal i)) (hpath : ∀ i, (route i).IsPath)
    (hnontrivial : ∀ i, ¬ (route i).Nil)
    (hfirst : Function.Injective (fun i => (route i).snd)) :
    Fintype.card ι ≤ (span G terminals).degree w := by
  let f : ι → (span G terminals).neighborSet w := fun i => ⟨(route i).snd, by
    obtain ⟨j, hji⟩ := exists_ne i
    exact span_adj_of_two_terminal_routes G hG terminals
      (hterminal i) (hterminal j) (route i) (route j) (hpath i) (hpath j)
      (hnontrivial i) (fun heq => hji (hfirst heq).symm)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    exact hfirst (congrArg Subtype.val hij)
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hinj

omit [Fintype V] in
/-- Replacing each edge of a walk by a connecting walk transports
reachability, without requiring a graph homomorphism. -/
theorem reachable_of_adj_reachable (G H : SimpleGraph V)
    (h : ∀ u v, G.Adj u v → H.Reachable u v) {a b : V}
    (hab : G.Reachable a b) : H.Reachable a b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons huv p ih => exact (h _ _ huv).trans ih

omit [Fintype V] in
/-- Deleting a non-bridge preserves every connected component, including
in a disconnected graph. -/
theorem reachable_deleteEdge_of_not_bridge (G : SimpleGraph V) {x y : V}
    (hn : ¬ G.IsBridge s(x,y)) {a b : V} (hab : G.Reachable a b) :
    (G.deleteEdges {s(x,y)}).Reachable a b := by
  apply reachable_of_adj_reachable G _ ?_ hab
  intro u v huv
  by_cases he : s(u,v) = s(x,y)
  · have hxy : G.Adj x y := by
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    have hreach : (G.deleteEdges {s(x,y)}).Reachable x y := by
      simpa only [SimpleGraph.isBridge_iff, hxy, true_and, not_not,
        SimpleGraph.deleteEdges] using hn
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hreach
    · exact hreach.symm
  · apply SimpleGraph.Adj.reachable
    simpa [SimpleGraph.deleteEdges, he] using huv

/-- Every finite graph has a spanning forest preserving its complete
reachability relation; no connectedness or chosen-root assumption is needed. -/
theorem exists_spanning_forest (G : SimpleGraph V) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      ∀ u v, G.Reachable u v → F.Reachable u v := by
  let P : SimpleGraph V → Prop := fun F =>
    ∀ u v, G.Reachable u v → F.Reachable u v
  have hPG : P G := fun _ _ h => h
  obtain ⟨F, hFG, hmin⟩ := {F : SimpleGraph V | P F}.toFinite.exists_minimal_le hPG
  refine ⟨F, hFG, ?_, hmin.prop⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  by_contra hn
  have hdel : P (F.deleteEdges {s(x,y)}) := by
    intro u v huv
    exact reachable_deleteEdge_of_not_bridge F hn (hmin.prop u v huv)
  apply hmin.not_prop_of_lt ?_ hdel
  simpa [SimpleGraph.deleteEdges, ← SimpleGraph.edgeSet_ssubset_edgeSet] using hxy

end Erdos1016.TerminalForest

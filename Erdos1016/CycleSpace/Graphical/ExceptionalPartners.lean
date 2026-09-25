import Erdos1016.Graph.TerminalForest
import Erdos1016.Graph.Multigraph.Components

set_option autoImplicit false

/-!
# Exceptional partners from terminal branches

The first step is a graph theorem with no supplied forest certificate: for
any finite graph and designated terminal set, at most `card terminals`
vertices separate their connected component into three or more
terminal-containing branches. A spanning forest and its terminal pruning are
constructed inside the proof.
-/

noncomputable section

namespace Erdos1016.ExceptionalPartners

variable {V : Type*} [Fintype V]

local instance exceptionalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

local instance componentFintype (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

abbrev DeletedVertex (w : V) := {v : V // v ≠ w}

def deleted (G : SimpleGraph V) (w : V) : SimpleGraph (DeletedVertex w) :=
  G.induce {v | v ≠ w}

/-- A component after deleting `w` containing a designated terminal that
was reachable from `w` before deletion. -/
def TerminalBranch (G : SimpleGraph V) (terminals : Finset V) (w : V) :=
  {c : (deleted G w).ConnectedComponent //
    ∃ t : DeletedVertex w, t.1 ∈ terminals ∧
      (deleted G w).connectedComponentMk t = c ∧ G.Reachable w t.1}

instance terminalBranchFintype (G : SimpleGraph V) (terminals : Finset V) (w : V) :
    Fintype (TerminalBranch G terminals w) := inferInstanceAs
      (Fintype {c : (deleted G w).ConnectedComponent //
        ∃ t : DeletedVertex w, t.1 ∈ terminals ∧
          (deleted G w).connectedComponentMk t = c ∧ G.Reachable w t.1})

/-- Restrict a supported walk to an induced graph. -/
def restrictWalk (G : SimpleGraph V) (S : Set V) {u v : V}
    (p : G.Walk u v) (hu : u ∈ S) (hv : v ∈ S)
    (hsupport : ∀ z ∈ p.support, z ∈ S) :
    (G.induce S).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact .nil
  | @cons a b c hab tail ih =>
      have hb : b ∈ S := hsupport b (by simp)
      exact .cons (show (G.induce S).Adj ⟨a, hu⟩ ⟨b, hb⟩ from hab)
        (ih hb hv (fun z hz => hsupport z (by simp [hz])))

omit [Fintype V] in
/-- The first vertex of a simple route and its terminal lie in the same
component after deleting its starting vertex. -/
theorem first_component_eq_terminal (G F : SimpleGraph V) (hFG : F ≤ G)
    {w t : V} (ht : t ≠ w) (p : F.Walk w t) (hp : p.IsPath) :
    ∃ hs : p.snd ≠ w,
      (deleted G w).connectedComponentMk ⟨p.snd, hs⟩ =
        (deleted G w).connectedComponentMk ⟨t, ht⟩ := by
  cases p with
  | nil => exact (ht rfl).elim
  | @cons w u t hwu p =>
      have hparts := (SimpleGraph.Walk.cons_isPath_iff hwu p).mp hp
      have hu : u ≠ w := hwu.ne.symm
      refine ⟨by simpa using hu, ?_⟩
      have hsupport : ∀ z ∈ (p.map (SimpleGraph.Hom.ofLE hFG)).support, z ≠ w := by
        intro z hz
        have hz' : z ∈ p.support := by simpa using hz
        intro heq
        exact hparts.2 (heq ▸ hz')
      let q := restrictWalk G {z | z ≠ w}
        (p.map (SimpleGraph.Hom.ofLE hFG)) hu ht hsupport
      simpa only [SimpleGraph.Walk.snd_cons] using
        (SimpleGraph.ConnectedComponent.sound q.reachable)

omit [Fintype V] in
/-- Reachability from the deleted vertex is equivalent to an actual edge
from that vertex to the component. Thus `TerminalBranch` uses exactly the
usual “component attached to both sides” condition. -/
theorem terminalBranch_condition_iff (G : SimpleGraph V) (terminals : Finset V)
    (w : V) (c : (deleted G w).ConnectedComponent) :
    (∃ t : DeletedVertex w, t.1 ∈ terminals ∧
      (deleted G w).connectedComponentMk t = c ∧ G.Reachable w t.1) ↔
    (∃ t : DeletedVertex w, t.1 ∈ terminals ∧
      (deleted G w).connectedComponentMk t = c) ∧
    (∃ u : DeletedVertex w, G.Adj w u.1 ∧
      (deleted G w).connectedComponentMk u = c) := by
  constructor
  · rintro ⟨t, ht, hc, hr⟩
    obtain ⟨p, hp⟩ := hr.exists_isPath
    obtain ⟨hs, hcomp⟩ := first_component_eq_terminal G G le_rfl t.2 p hp
    have hn : ¬ p.Nil := fun h => t.2 h.eq.symm
    exact ⟨⟨t, ht, hc⟩, ⟨⟨p.snd, hs⟩,
      (p.toSubgraph_adj_snd hn).adj_sub, hcomp.trans hc⟩⟩
  · rintro ⟨⟨t, ht, hc⟩, ⟨u, hu, huc⟩⟩
    have hreach : (deleted G w).Reachable u t :=
      SimpleGraph.ConnectedComponent.exact (huc.trans hc.symm)
    let inc : deleted G w →g G := (SimpleGraph.Embedding.induce (G := G) {z | z ≠ w}).toHom
    exact ⟨t, ht, hc, hu.reachable.trans (hreach.map inc)⟩

/-- Actual terminal branches inject into the retained incidences of a
spanning forest, rather than being assumed to have such a representation. -/
theorem terminalBranch_card_le_span_degree
    (G F : SimpleGraph V) (hFG : F ≤ G) (hF : F.IsAcyclic)
    (hreach : ∀ u v, G.Reachable u v → F.Reachable u v)
    (terminals : Finset V) (w : V)
    (hthree : 3 ≤ Nat.card (TerminalBranch G terminals w)) :
    Nat.card (TerminalBranch G terminals w) ≤
      (TerminalForest.span F terminals).degree w := by
  let B := TerminalBranch G terminals w
  have hcard : 3 ≤ Fintype.card B := by simpa only [Nat.card_eq_fintype_card] using hthree
  letI : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  choose t ht hcomp hconnected using fun c : B => c.2
  choose p hp using fun c : B => (hreach w (t c).1 (hconnected c)).exists_isPath
  have hnontrivial (c : B) : ¬ (p c).Nil := by
    intro hn
    exact (t c).2 hn.eq.symm
  have hfirst : Function.Injective (fun c : B => (p c).snd) := by
    intro c d heq
    obtain ⟨hc, hpc⟩ := first_component_eq_terminal G F hFG (t c).2 (p c) (hp c)
    obtain ⟨hd, hpd⟩ := first_component_eq_terminal G F hFG (t d).2 (p d) (hp d)
    apply Subtype.ext
    calc
      c.1 = (deleted G w).connectedComponentMk (t c) := (hcomp c).symm
      _ = (deleted G w).connectedComponentMk ⟨(p c).snd, hc⟩ := hpc.symm
      _ = (deleted G w).connectedComponentMk ⟨(p d).snd, hd⟩ := by congr 1; exact Subtype.ext heq
      _ = (deleted G w).connectedComponentMk (t d) := hpd
      _ = d.1 := hcomp d
  simpa only [Nat.card_eq_fintype_card] using
    TerminalForest.route_card_le_span_degree F hF terminals w (fun c : B => (t c).1)
      ht p hp hnontrivial hfirst

/-- No more than `card terminals` vertices have three terminal-containing
branches. The graph may be disconnected; the terminals may occur anywhere. -/
theorem three_terminal_branches_card_le (G : SimpleGraph V) (terminals : Finset V) :
    (Finset.univ.filter (fun w =>
      3 ≤ Nat.card (TerminalBranch G terminals w))).card ≤ terminals.card := by
  obtain ⟨F, hFG, hF, hreach⟩ := TerminalForest.exists_spanning_forest G
  refine (Finset.card_le_card ?_).trans (TerminalForest.span_branch_card_le F hF terminals)
  intro w hw
  have hthree := (Finset.mem_filter.mp hw).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthree.trans
    (terminalBranch_card_le_span_degree G F hFG hF hreach terminals w hthree)⟩

section Incidences

variable {ι : Type*} [Fintype ι]

/-- Attach distinct labelled terminal leaves. Repeated attachment vertices
are allowed and retain the multiplicity of parallel incidences. -/
def withLeaves (G : SimpleGraph V) (attach : ι → V) : SimpleGraph (V ⊕ ι) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr i => u = attach i
    | .inr i, .inl u => attach i = u
    | .inr _, .inr _ => False
  symm := by
    intro a b hab
    cases a <;> cases b
    · exact G.symm hab
    · exact hab.symm
    · exact hab.symm
    · exact hab
  loopless := by intro a; cases a; exact G.loopless _; exact not_false

def leafTerminals : Finset (V ⊕ ι) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

omit [Fintype V] in
@[simp] theorem leafTerminals_card : (leafTerminals (V := V) (ι := ι)).card =
    Fintype.card ι := by simp [leafTerminals]

omit [Fintype V] in
@[simp] theorem mem_leafTerminals (i : ι) :
    Sum.inr i ∈ leafTerminals (V := V) := by simp [leafTerminals]

def oldHom (G : SimpleGraph V) (attach : ι → V) : G →g withLeaves G attach where
  toFun := Sum.inl
  map_rel' := by intro a b hab; exact hab

/-- The old endpoints of the labelled incidences, with repetitions removed
only for testing whether a deleted component contains an incidence. -/
def attachmentVertices (attach : ι → V) : Finset V := Finset.univ.image attach

/-- Links are individual direct incidences and the incidence-containing
components of `G-w` that were connected to `w`. Taking `G` to be an ambient
graph with one vertex deleted gives exactly the exceptional-cut links. -/
def IncidenceLink (G : SimpleGraph V) (attach : ι → V) (w : V) :=
  {i : ι // attach i = w} ⊕ TerminalBranch G (attachmentVertices attach) w

instance incidenceLinkFintype (G : SimpleGraph V) (attach : ι → V) (w : V) :
    Fintype (IncidenceLink G attach w) := inferInstanceAs
      (Fintype ({i : ι // attach i = w} ⊕ TerminalBranch G (attachmentVertices attach) w))

/-- Labels distinguish the deleted components and every terminal leaf whose
attachment was the deleted vertex. -/
def branchLabel (G : SimpleGraph V) (attach : ι → V) (w : V) :
    DeletedVertex (Sum.inl w : V ⊕ ι) → ι ⊕ (deleted G w).ConnectedComponent
  | ⟨.inl x, hx⟩ => .inr ((deleted G w).connectedComponentMk
      ⟨x, fun h => hx (congrArg Sum.inl h)⟩)
  | ⟨.inr i, _⟩ => if h : attach i = w then .inl i else
      .inr ((deleted G w).connectedComponentMk ⟨attach i, h⟩)

omit [Fintype V] [Fintype ι] in
theorem branchLabel_eq_of_adj (G : SimpleGraph V) (attach : ι → V) (w : V)
    (a b : DeletedVertex (Sum.inl w : V ⊕ ι))
    (hab : (deleted (withLeaves G attach) (Sum.inl w)).Adj a b) :
    branchLabel G attach w a = branchLabel G attach w b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          apply congrArg Sum.inr
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab
      | inr i =>
          have hxi : x = attach i := hab
          have hi : attach i ≠ w := by
            intro h
            exact ha (congrArg Sum.inl (hxi.trans h))
          simp only [branchLabel, dif_neg hi]
          congr 2
          exact Subtype.ext hxi
  | inr i =>
      cases b with
      | inl y =>
          have hiy : attach i = y := hab
          have hi : attach i ≠ w := by
            intro h
            exact hb (congrArg Sum.inl (hiy.symm.trans h))
          simp only [branchLabel, dif_neg hi]
          congr 2
          exact Subtype.ext hiy
      | inr j => exact False.elim hab

omit [Fintype V] [Fintype ι] in
theorem branchLabel_eq_of_reachable (G : SimpleGraph V) (attach : ι → V) (w : V)
    {a b : DeletedVertex (Sum.inl w : V ⊕ ι)}
    (hab : (deleted (withLeaves G attach) (Sum.inl w)).Reachable a b) :
    branchLabel G attach w a = branchLabel G attach w b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons h p ih => exact (branchLabel_eq_of_adj G attach w _ _ h).trans ih

omit [Fintype V] in
/-- Recover a physical incidence from an incidence-containing component. -/
theorem component_incidence (G : SimpleGraph V) (attach : ι → V) (w : V)
    (c : TerminalBranch G (attachmentVertices attach) w) :
    ∃ i : ι, ∃ hi : attach i ≠ w,
      (deleted G w).connectedComponentMk ⟨attach i, hi⟩ = c.1 ∧
        G.Reachable w (attach i) := by
  obtain ⟨t, ht, hc, hr⟩ := c.2
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
  refine ⟨i, fun h => t.2 (hi.symm.trans h), ?_, ?_⟩
  · simpa only [hi] using hc
  · simpa only [hi] using hr

def linkTag (G : SimpleGraph V) (attach : ι → V) (w : V) :
    IncidenceLink G attach w → ι ⊕ (deleted G w).ConnectedComponent
  | .inl i => .inl i.1
  | .inr c => .inr c.1

omit [Fintype V] in
theorem linkTag_injective (G : SimpleGraph V) (attach : ι → V) (w : V) :
    Function.Injective (linkTag G attach w) := by
  intro a b hab
  cases a <;> cases b <;> simp only [linkTag, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl] at hab
  · exact congrArg Sum.inl (Subtype.ext hab)
  · exact congrArg Sum.inr (Subtype.ext hab)

omit [Fintype V] in
theorem link_has_terminal (G : SimpleGraph V) (attach : ι → V) (w : V)
    (l : IncidenceLink G attach w) :
    ∃ i : ι,
      (withLeaves G attach).Reachable (Sum.inl w) (Sum.inr i) ∧
        branchLabel G attach w ⟨Sum.inr i, Sum.inr_ne_inl⟩ = linkTag G attach w l := by
  cases l with
  | inl i =>
      refine ⟨i.1, ?_, ?_⟩
      · exact SimpleGraph.Adj.reachable (show (withLeaves G attach).Adj
          (Sum.inl w) (Sum.inr i.1) from i.2.symm)
      · simp [branchLabel, linkTag, i.2]
  | inr c =>
      obtain ⟨i, hi, hc, hr⟩ := component_incidence G attach w c
      refine ⟨i, ?_, ?_⟩
      · exact (hr.map (oldHom G attach)).trans
          (SimpleGraph.Adj.reachable (show (withLeaves G attach).Adj
            (Sum.inl (attach i)) (Sum.inr i) from rfl))
      · simp [branchLabel, linkTag, hi, hc]

/-- The links inject into actual terminal-containing components after
deleting the old vertex of the graph with labelled terminal leaves. -/
theorem incidenceLink_card_le_terminalBranch_card
    (G : SimpleGraph V) (attach : ι → V) (w : V) :
    Nat.card (IncidenceLink G attach w) ≤
      Nat.card (TerminalBranch (withLeaves G attach) leafTerminals (Sum.inl w)) := by
  choose i hreach hlabel using link_has_terminal G attach w
  let f : IncidenceLink G attach w →
      TerminalBranch (withLeaves G attach) leafTerminals (Sum.inl w) := fun l =>
    ⟨(deleted (withLeaves G attach) (Sum.inl w)).connectedComponentMk
      ⟨Sum.inr (i l), Sum.inr_ne_inl⟩,
      ⟨⟨Sum.inr (i l), Sum.inr_ne_inl⟩, mem_leafTerminals (i l), rfl, hreach l⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply linkTag_injective G attach w
    rw [← hlabel a, ← hlabel b]
    apply branchLabel_eq_of_reachable
    exact SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hab)
  exact Nat.card_le_card_of_injective f hf

/-- The linear exceptional-partner bound, with every incidence counted
separately. There is no assumed forest, pruning, route, or packing certificate. -/
theorem three_incidence_links_card_le (G : SimpleGraph V) (attach : ι → V) :
    (Finset.univ.filter (fun w => 3 ≤ Nat.card (IncidenceLink G attach w))).card ≤
      Fintype.card ι := by
  let S := Finset.univ.filter (fun w => 3 ≤ Nat.card (IncidenceLink G attach w))
  have hinj : Set.InjOn (Sum.inl : V → V ⊕ ι) ↑S :=
    Sum.inl_injective.injOn
  have hmap : ∀ w ∈ S, Sum.inl w ∈ Finset.univ.filter (fun z =>
      3 ≤ Nat.card (TerminalBranch (withLeaves G attach) leafTerminals z)) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.trans
      (incidenceLink_card_le_terminalBranch_card G attach w)⟩
  exact (Finset.card_le_card_of_injOn Sum.inl hmap hinj).trans
    ((three_terminal_branches_card_le (withLeaves G attach) leafTerminals).trans_eq
      leafTerminals_card)

end Incidences

section Multigraph

/-- The physical nonloop incidences at a vertex. Loops never belong to its
cut, and parallel edge labels remain distinct elements of this type. -/
def CutIncidence (M : FiniteMultiGraph) (v : M.Vertex) :=
  {e : M.Edge //
    (M.src e = v ∧ M.dst e ≠ v) ∨ (M.dst e = v ∧ M.src e ≠ v)}

instance cutIncidenceFintype (M : FiniteMultiGraph) (v : M.Vertex) :
    Fintype (CutIncidence M v) := inferInstanceAs
      (Fintype {e : M.Edge //
        (M.src e = v ∧ M.dst e ≠ v) ∨ (M.dst e = v ∧ M.src e ≠ v)})

/-- The endpoint left behind when the distinguished vertex is removed. -/
def otherEndpoint (M : FiniteMultiGraph) (v : M.Vertex)
    (e : CutIncidence M v) : DeletedVertex v :=
  if hs : M.src e.1 = v then
    ⟨M.dst e.1, by rcases e.2 with h | h; exact h.2; exact (h.2 hs).elim⟩
  else ⟨M.src e.1, hs⟩

theorem otherEndpoint_eq_iff (M : FiniteMultiGraph) (v : M.Vertex)
    (e : CutIncidence M v) (w : DeletedVertex v) :
    (otherEndpoint M v e).1 = w.1 ↔
      (M.src e.1 = v ∧ M.dst e.1 = w.1) ∨
        (M.dst e.1 = v ∧ M.src e.1 = w.1) := by
  by_cases hs : M.src e.1 = v
  · have hdst : M.dst e.1 ≠ v := by
      rcases e.2 with h | h
      · exact h.2
      · exact (h.2 hs).elim
    simp [otherEndpoint, hs, hdst]
  · have hd : M.dst e.1 = v := by
      rcases e.2 with h | h
      · exact (hs h.1).elim
      · exact h.1
    simp [otherEndpoint, hs, hd]

/-- Exact physical cut size, excluding loops and counting parallel labels. -/
def cutSizeAt (M : FiniteMultiGraph) (v : M.Vertex) : ℕ :=
  (Finset.univ.filter (fun e : M.Edge =>
    (M.src e = v ∧ M.dst e ≠ v) ∨ (M.dst e = v ∧ M.src e ≠ v))).card

theorem cutIncidence_card (M : FiniteMultiGraph) (v : M.Vertex) :
    Fintype.card (CutIncidence M v) = cutSizeAt M v := by
  simp only [CutIncidence, cutSizeAt, Fintype.card_subtype]

/-- The links of the manuscript: physical direct edges to `w`, and
components after deleting `v,w` incident to both sides. The component
attachment to `w` is expressed by reachability before `w` is deleted. -/
def MultigraphLink (M : FiniteMultiGraph) (v : M.Vertex) (w : DeletedVertex v) :=
  IncidenceLink (deleted M.toSimpleGraph v) (otherEndpoint M v) w

/-- The exceptional-vertex bound for an actual labelled multigraph. It is
valid even when the graph is disconnected and may have loops or parallel
edges. Connectedness is needed later for the exact correlation formula. -/
theorem multigraph_three_links_card_le_cut (M : FiniteMultiGraph) (v : M.Vertex) :
    (Finset.univ.filter (fun w : DeletedVertex v =>
      3 ≤ Nat.card (MultigraphLink M v w))).card ≤ cutSizeAt M v := by
  exact (three_incidence_links_card_le (deleted M.toSimpleGraph v)
    (otherEndpoint M v)).trans_eq (cutIncidence_card M v)

/-- A concrete distinct family of vertices obeys the same cut budget. -/
theorem multigraph_family_card_le_cut {κ : Type*} (s : Finset κ)
    (M : FiniteMultiGraph) (v : M.Vertex) (vertex : κ → DeletedVertex v)
    (hinj : Set.InjOn vertex ↑s)
    (hlinks : ∀ i ∈ s, 3 ≤ Nat.card (MultigraphLink M v (vertex i))) :
    s.card ≤ cutSizeAt M v := by
  refine (Finset.card_le_card_of_injOn vertex ?_ hinj).trans
    (multigraph_three_links_card_le_cut M v)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlinks i hi⟩

end Multigraph

end Erdos1016.ExceptionalPartners

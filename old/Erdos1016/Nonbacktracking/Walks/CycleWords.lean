import Erdos1016.Nonbacktracking.Girth.MooreBounds
import Erdos1016.Cycles.Selection.PackingTransversalDichotomy

set_option autoImplicit false

/-!
# Physical cycle words and ordinary short-cycle exclusion

The short-cycle transversal uses physical `CycleWord`s, while the short-walk
proof uses ordinary `Walk.IsCycle`s. This module constructs a physical word
from every ordinary simple cycle, proves equality of its physical length and
vertex support, and transfers the former exclusion to the latter. No
representation-equivalence hypothesis is left in that transfer.

The adapter is one-way, which is all the girth/entropy argument needs. It
makes no assertion about identifying rooted walks with unrooted cycles in
trace counts: that multiplicity is still a separate Section 6 obligation.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
open BoundaryDecay
local instance cycleWalkAdapterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- The unordered physical edge has a unique label in a simple owner. -/
def physicalPair (e : G.Edge) : Sym2 G.Vertex := s(G.src e, G.dst e)

theorem physicalPair_injective : Function.Injective (physicalPair G) := by
  intro e f h
  exact G.simple e f (Sym2.eq_iff.1 h)

private theorem physicalPair_exists {a : Sym2 G.Vertex}
    (ha : a ∈ G.toSimpleGraph.edgeSet) : ∃ e : G.Edge, physicalPair G e = a := by
  revert ha
  refine Sym2.inductionOn a ?_
  intro u v huv
  rcases huv with ⟨e, _, h | h⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inl h)⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inr h)⟩

/-- Characteristic word of the actual edge set of a vertex walk. Repetitions
are discarded here; the length theorem below assumes the walk is a cycle. -/
def walkWord {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) : G.Word :=
  fun e => if physicalPair G e ∈ p.edges then 1 else 0

@[simp] theorem walkWord_nonzero_iff {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (e : G.Edge) :
    walkWord G p e ≠ 0 ↔ physicalPair G e ∈ p.edges := by
  simp [walkWord]

private theorem pair_mem_edges_iff {u v a b : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) : s(a, b) ∈ p.edges ↔ p.toSubgraph.Adj a b := by
  rw [← p.mem_edges_toSubgraph, SimpleGraph.Subgraph.mem_edgeSet]

/-- The selected graph is exactly the walk subgraph, with original isolates
retained. No induced chords are added to the cycle word. -/
theorem walkWord_adj_iff {u v a b : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    (G.selectedGraph (walkWord G p)).Adj a b ↔ p.toSubgraph.Adj a b := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · have hh := (walkWord_nonzero_iff G p e).1 he
      rw [physicalPair, h.1, h.2] at hh
      exact (pair_mem_edges_iff G p).1 hh
    · have hh := (walkWord_nonzero_iff G p e).1 he
      rw [physicalPair, h.1, h.2] at hh
      exact ((pair_mem_edges_iff G p).1 hh).symm
  · intro hab
    rcases p.toSubgraph.adj_sub hab with ⟨e, _, h | h⟩
    · refine ⟨e, (walkWord_nonzero_iff G p e).2 ?_, Or.inl h⟩
      rw [physicalPair, h.1, h.2]
      exact (pair_mem_edges_iff G p).2 hab
    · refine ⟨e, (walkWord_nonzero_iff G p e).2 ?_, Or.inr h⟩
      rw [physicalPair, h.1, h.2]
      exact (pair_mem_edges_iff G p).2 hab.symm

/-- A generic incidence adapter: in a simple graph, selected physical
incidences and selected neighbours have exactly the same cardinality. -/
theorem selectedDegree_eq_neighbor_ncard (x : G.Word) (v : G.Vertex) :
    G.selectedDegree x v = ((G.selectedGraph x).neighborSet v).ncard := by
  let F : Finset G.Edge := Finset.univ.filter fun e => x e ≠ 0 ∧ G.incident e v
  let other : G.Edge → G.Vertex := fun e => if G.src e = v then G.dst e else G.src e
  have hends (e : G.Edge) (he : e ∈ F) :
      (G.src e = v ∧ G.dst e = other e) ∨
      (G.src e = other e ∧ G.dst e = v) := by
    have hi : G.incident e v := (Finset.mem_filter.1 he).2.2
    by_cases hs : G.src e = v
    · exact Or.inl ⟨hs, by simp [other, hs]⟩
    · rcases hi with hi | hi
      · exact False.elim (hs hi)
      · exact Or.inr ⟨by simp [other, hs], hi⟩
  let f : {e // e ∈ F} → (G.selectedGraph x).neighborSet v := fun e =>
    ⟨other e.1, e.1, (Finset.mem_filter.1 e.2).2.1, hends e.1 e.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e d heq
      have ho : other e.1 = other d.1 := congrArg Subtype.val heq
      apply Subtype.ext
      apply G.simple
      rcases hends e.1 e.2 with he | he <;> rcases hends d.1 d.2 with hd | hd
      · exact Or.inl ⟨he.1.trans hd.1.symm, he.2.trans (ho.trans hd.2.symm)⟩
      · exact Or.inr ⟨he.1.trans hd.2.symm, he.2.trans (ho.trans hd.1.symm)⟩
      · exact Or.inr ⟨he.1.trans (ho.trans hd.2.symm), he.2.trans hd.1.symm⟩
      · exact Or.inl ⟨he.1.trans (ho.trans hd.1.symm), he.2.trans hd.2.symm⟩
    · rintro ⟨w, hw⟩
      rcases hw with ⟨e, hxe, he | he⟩
      · have hmem : e ∈ F := Finset.mem_filter.2
          ⟨Finset.mem_univ _, hxe, Or.inl he.1⟩
        refine ⟨⟨e, hmem⟩, Subtype.ext ?_⟩
        change other e = w
        simp [other, he.1, he.2]
      · have hmem : e ∈ F := Finset.mem_filter.2
          ⟨Finset.mem_univ _, hxe, Or.inr he.2⟩
        refine ⟨⟨e, hmem⟩, Subtype.ext ?_⟩
        have hs : G.src e ≠ v := fun h => G.noLoops e (h.trans he.2.symm)
        change other e = w
        simp only [other, hs]
        exact he.1
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  change F.card = Nat.card ((G.selectedGraph x).neighborSet v)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

/-- The boundary bit is the selected degree reduced modulo two. -/
theorem boundary_eq_selectedDegree_cast (x : G.Word) (v : G.Vertex) :
    G.boundary x v = (G.selectedDegree x v : F₂) := by
  have binary (a : F₂) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  change (∑ e, ((if G.src e = v then x e else 0) +
    (if G.dst e = v then x e else 0))) = _
  unfold PhysicalGraph.selectedDegree
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rcases binary (x e) with hx | hx
  · simp [hx]
  · by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v
    all_goals try simp [hx, hs, hd, PhysicalGraph.incident]
    all_goals exact False.elim (G.noLoops e (hs.trans hd.symm))

/-- Every cycle support vertex is used, and no other vertex is introduced. -/
theorem used_walkWord_iff {u : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (hp : p.IsCycle) (v : G.Vertex) :
    v ∈ G.usedVertices (walkWord G p) ↔ v ∈ p.support := by
  constructor
  · intro hv
    obtain ⟨e, he, hi | hi⟩ := (mem_usedVertices _ _).1 hv
    · have hm := (walkWord_nonzero_iff G p e).1 he
      exact hi ▸ p.fst_mem_support_of_mem_edges hm
    · have hm := (walkWord_nonzero_iff G p e).1 he
      exact hi ▸ p.snd_mem_support_of_mem_edges hm
  · intro hv
    have hc := hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hne : (p.toSubgraph.neighborSet v).Nonempty :=
      (Set.ncard_pos (by toFinite_tac)).1 (by rw [hc]; norm_num)
    obtain ⟨w, hw⟩ := hne
    have hs := (walkWord_adj_iff G p).2 hw
    rcases hs with ⟨e, he, hi | hi⟩
    · exact (mem_usedVertices _ _).2 ⟨e, he, Or.inl hi.1⟩
    · exact (mem_usedVertices _ _).2 ⟨e, he, Or.inr hi.2⟩

/-- Every selected incidence of an ordinary simple cycle has degree two. -/
theorem walkWord_degree_two {u : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (hp : p.IsCycle) (v : G.Vertex) (hv : v ∈ p.support) :
    G.selectedDegree (walkWord G p) v = 2 := by
  rw [selectedDegree_eq_neighbor_ncard]
  have heq : (G.selectedGraph (walkWord G p)).neighborSet v =
      p.toSubgraph.neighborSet v := by
    ext w
    exact walkWord_adj_iff G p
  rw [heq]
  exact hp.ncard_neighborSet_toSubgraph_eq_two hv

/-- The ordinary closed simple walk is a nonzero homogeneous physical word,
connected on its exact used support and two-regular there. -/
theorem walkWord_isCycleWord {u : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (hp : p.IsCycle) : G.IsCycleWord (walkWord G p) := by
  have hused : u ∈ G.usedVertices (walkWord G p) :=
    (used_walkWord_iff G p hp u).2 p.start_mem_support
  have hne : walkWord G p ≠ 0 := by
    intro hz
    rw [hz] at hused
    simpa [PhysicalGraph.usedVertices] using hused
  have hboundary : G.boundary (walkWord G p) = 0 := by
    funext v
    rw [boundary_eq_selectedDegree_cast]
    by_cases hv : v ∈ p.support
    · rw [walkWord_degree_two G p hp v hv]
      have htwo : (2 : F₂) = 0 := by decide
      exact htwo
    · have hnot : v ∉ G.usedVertices (walkWord G p) :=
        fun h => hv ((used_walkWord_iff G p hp v).1 h)
      rw [selectedDegree_zero_of_not_used _ _ hnot]
      norm_num
  let f : p.toSubgraph.coe →g
      (G.selectedGraph (walkWord G p)).induce
        (↑(G.usedVertices (walkWord G p)) : Set G.Vertex) := {
    toFun := fun (v : {w : G.Vertex // w ∈ p.toSubgraph.verts}) =>
      (⟨v.1, (used_walkWord_iff G p hp v.1).2
        ((p.mem_verts_toSubgraph).1 v.2)⟩ :
        {w : G.Vertex // w ∈ G.usedVertices (walkWord G p)})
    map_rel' := fun {a b : p.toSubgraph.verts}
        (hab : p.toSubgraph.coe.Adj a b) => by
      change p.toSubgraph.Adj a.1 b.1 at hab
      change (G.selectedGraph (walkWord G p)).Adj a.1 b.1
      exact (walkWord_adj_iff G p).2 hab
  }
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨v.1, (p.mem_verts_toSubgraph).2
      ((used_walkWord_iff G p hp v.1).1 v.2)⟩, ?_⟩
    apply Subtype.ext
    rfl
  refine ⟨hne, hboundary, (p.toSubgraph_connected.coe).map f hsurj, ?_⟩
  intro v hv
  exact walkWord_degree_two G p hp v ((used_walkWord_iff G p hp v).1 hv)

/-- The actual physical cycle associated to a simple closed vertex walk. -/
def cycleWordOfWalk {u : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (hp : p.IsCycle) : G.CycleWord := ⟨walkWord G p, walkWord_isCycleWord G p hp⟩

private theorem walkWord_edge_image {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    (G.edgeSupport (walkWord G p)).image (physicalPair G) = p.edges.toFinset := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
    apply List.mem_toFinset.2
    exact (walkWord_nonzero_iff G p e).1 (Finset.mem_filter.1 he).2
  · intro ha
    have hm : a ∈ p.edges := List.mem_toFinset.1 ha
    have hbase : a ∈ G.toSimpleGraph.edgeSet :=
      p.toSubgraph.edgeSet_subset ((p.mem_edges_toSubgraph).2 hm)
    obtain ⟨e, he⟩ := physicalPair_exists G hbase
    refine Finset.mem_image.2 ⟨e, ?_, he⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, (walkWord_nonzero_iff G p e).2 ?_⟩
    rwa [he]

/-- The cycle word counts each original edge once, with no orientation/root
factor. Those factors are needed only when counting multiple cycle walks. -/
theorem cycleWordOfWalk_length {u : G.Vertex} (p : G.toSimpleGraph.Walk u u)
    (hp : p.IsCycle) : BoundaryDecay.Cycle.length (cycleWordOfWalk G p hp) = p.length := by
  have hc := congrArg Finset.card (walkWord_edge_image G p)
  rw [Finset.card_image_of_injective _ (physicalPair_injective G),
    List.toFinset_card_of_nodup hp.1.1.edges_nodup,
    SimpleGraph.Walk.length_edges] at hc
  change G.wordLength (walkWord G p) = p.length
  simpa [PhysicalGraph.wordLength] using hc



/-- The same bridge on an actual induced vertex region, with each attachment
and original edge retained in the enclosing owner. -/
theorem girthGreater_induce_of_noShortCycles (U : Finset G.Vertex) (D : ℕ)
    (hg : CycleSupply.NoShortCycles G U D) :
    ShortWalks.GirthGreater (G.toSimpleGraph.induce (↑U : Set G.Vertex)) D := by
  intro u p hp
  let incl : G.toSimpleGraph.induce (↑U : Set G.Vertex) →g G.toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := by intro a b hab; exact hab }
  let q : G.toSimpleGraph.Walk u.1 u.1 := p.map incl
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
  let C := cycleWordOfWalk G q hq
  have hCU : Cycle.vertices C ⊆ U := by
    intro v hv
    have hv' : v ∈ G.usedVertices (walkWord G q) := by
      simpa [C, cycleWordOfWalk, BoundaryDecay.Cycle.vertices] using hv
    have hvs : v ∈ q.support := (used_walkWord_iff G q hq v).1 hv'
    have hvs' : ∃ a : U, a ∈ p.support ∧ incl a = v := by
      simpa only [q, SimpleGraph.Walk.support_map, List.mem_map] using hvs
    obtain ⟨a, _, hav⟩ := hvs'
    have hv' : a.1 = v := hav
    simpa [← hv'] using a.2
  have h := hg C hCU
  change D < BoundaryDecay.Cycle.length (cycleWordOfWalk G q hq) at h
  rw [cycleWordOfWalk_length] at h
  simpa [q] using h



end Erdos1016.Nonbacktracking

import Erdos1016.Cleanup.Root.PortExpansion
import Erdos1016.Graph.PathExpansion.RouteConstancy

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpansionCycleSpace

open Erdos1016
open Erdos1016.Proof.PortExpansion
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.FiniteMultiGraph
open SimpleGraph

abbrev Physical (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) : FiniteMultiGraph :=
  { vertexCount := (graph M S h).vertexCount
    edgeCount := (graph M S h).edgeCount
    src := (graph M S h).src
    dst := (graph M S h).dst }

theorem boundary_edgeSetWord_eq_endpoint_sum (G : FiniteMultiGraph)
    (E : Finset G.Edge) :
    G.boundary (edgeSetWord G E) =
      ∑ e ∈ E, endpointDemand G G (fun v => v) e := by
  classical
  ext v
  change (∑ e, ((if G.src e = v then if e ∈ E then (1 : F₂) else 0 else 0) +
    (if G.dst e = v then if e ∈ E then (1 : F₂) else 0 else 0))) = _
  rw [Finset.sum_add_distrib]
  have hs : (∑ e, (if G.src e = v then if e ∈ E then (1 : F₂) else 0 else 0)) =
      ∑ e ∈ E, if G.src e = v then (1 : F₂) else 0 := by
    calc
      _ = ∑ e, if e ∈ E then (if G.src e = v then (1 : F₂) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hs : G.src e = v <;> by_cases hE : e ∈ E <;> simp [hs, hE]
      _ = ∑ e ∈ E, if G.src e = v then (1 : F₂) else 0 := by
        rw [← Finset.sum_filter]
        simp
  have hd : (∑ e, (if G.dst e = v then if e ∈ E then (1 : F₂) else 0 else 0)) =
      ∑ e ∈ E, if G.dst e = v then (1 : F₂) else 0 := by
    calc
      _ = ∑ e, if e ∈ E then (if G.dst e = v then (1 : F₂) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hs : G.dst e = v <;> by_cases hE : e ∈ E <;> simp [hs, hE]
      _ = ∑ e ∈ E, if G.dst e = v then (1 : F₂) else 0 := by
        rw [← Finset.sum_filter]
        simp
  rw [hs, hd]
  unfold endpointDemand
  simp only [Finset.sum_apply, id_eq]
  rw [← Finset.sum_add_distrib]

/-- Split a multigraph boundary into its source-incidence and
 destination-incidence sums. This exposes the finite edge sets that a concrete
port-expansion incidence proof must identify. -/
theorem boundary_sum_split (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) :
    G.boundary x v =
      (∑ e ∈ Finset.univ.filter (fun e : G.Edge => G.src e = v), x e) +
      (∑ e ∈ Finset.univ.filter (fun e : G.Edge => G.dst e = v), x e) := by
  classical
  change (∑ e, ((if G.src e = v then x e else 0) +
    (if G.dst e = v then x e else 0))) = _
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_filter]

private theorem oldVertex_ne_portVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (u : M.Vertex) (p : PortEdge M S) :
    oldVertex M S u ≠ portVertex M S p := by
  intro h
  have hv := (vertexEquiv M S).injective h
  cases hv

private theorem loopVertex_ne_portVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (l : ExteriorLoop M S) (j : Fin 2) (p : PortEdge M S) :
    loopVertex M S l j ≠ portVertex M S p := by
  intro h
  have hv := (vertexEquiv M S).injective h
  cases hv

private theorem portVertex_injective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    {p q : PortEdge M S} (h : portVertex M S p = portVertex M S q) : p = q := by
  have hv := (vertexEquiv M S).injective h
  exact Sum.inl.inj (Sum.inr.inj hv)

private theorem edge_eq_tag (M : FiniteMultiGraph) (S : Finset M.Vertex)
    {i : Fin (edgeCount M S)} {t : PortEdgeType M S}
    (ht : (edgeEquiv M S).symm i = t) : i = edgeEquiv M S t := by
  calc
    i = edgeEquiv M S ((edgeEquiv M S).symm i) := (Equiv.apply_symm_apply _ _).symm
    _ = edgeEquiv M S t := congrArg (edgeEquiv M S) ht

/-- No port-expansion edge has its source at the private port midpoint. -/
theorem portVertex_source_edges_empty (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    (Finset.univ.filter fun e : (Physical M S h).Edge =>
      (Physical M S h).src e = portVertex M S p) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  change (graph M S h).src i = _ at hi
  cases ht : (edgeEquiv M S).symm i with
  | inl e =>
      have heq := edge_eq_tag M S ht
      rw [heq] at hi
      simp only [src_internalEdge] at hi
      exact (oldVertex_ne_portVertex M S (M.src e.1) p hi).elim
  | inr e =>
    cases e with
    | inl e =>
      rcases e with ⟨q, b⟩
      have heq := edge_eq_tag M S ht
      rw [heq] at hi
      cases b
      · simp only [src_portEdge_false] at hi
        exact (oldVertex_ne_portVertex M S (M.src q.1) p hi).elim
      · simp only [src_portEdge_true] at hi
        exact (oldVertex_ne_portVertex M S (M.dst q.1) p hi).elim
    | inr e =>
      rcases e with ⟨l, k⟩
      have heq := edge_eq_tag M S ht
      rw [heq] at hi
      fin_cases k
      · have h' : oldVertex M S (M.src l.1) = portVertex M S p := by simpa using hi
        exact (oldVertex_ne_portVertex M S (M.src l.1) p h').elim
      · have h' : loopVertex M S l 0 = portVertex M S p := by simpa using hi
        exact (loopVertex_ne_portVertex M S l 0 p h').elim
      · have h' : loopVertex M S l 1 = portVertex M S p := by simpa using hi
        exact (loopVertex_ne_portVertex M S l 1 p h').elim

/-- The dst-incidence labels at a private port midpoint are precisely the
 two halves of that port route. -/
theorem portVertex_destination_edges (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    Finset.univ.filter (fun e : (Physical M S h).Edge =>
      (Physical M S h).dst e = portVertex M S p) =
      {edgeEquiv M S (.inr (.inl (p, false))),
       edgeEquiv M S (.inr (.inl (p, true)))} := by
  classical
  ext i
  constructor
  · intro hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    change (graph M S h).dst i = _ at hi
    cases ht : (edgeEquiv M S).symm i with
    | inl e =>
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        simp only [dst_internalEdge] at hi
        exact (oldVertex_ne_portVertex M S (M.dst e.1) p hi).elim
    | inr e =>
      cases e with
      | inl e =>
        rcases e with ⟨q, b⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        simp only [dst_portEdge] at hi
        have hqp : q = p := portVertex_injective M S hi
        subst q
        cases b <;> simp [heq]
      | inr e =>
        rcases e with ⟨l, k⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        fin_cases k
        · have h' : loopVertex M S l 0 = portVertex M S p := by simpa using hi
          exact (loopVertex_ne_portVertex M S l 0 p h').elim
        · have h' : loopVertex M S l 1 = portVertex M S p := by simpa using hi
          exact (loopVertex_ne_portVertex M S l 1 p h').elim
        · have h' : oldVertex M S (M.dst l.1) = portVertex M S p := by simpa using hi
          exact (oldVertex_ne_portVertex M S (M.dst l.1) p h').elim
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with hi | hi
    · rw [hi]
      exact dst_portEdge M S h p false
    · rw [hi]
      exact dst_portEdge M S h p true

/-- The complete boundary at a private port midpoint is the sum of its two
incoming route-edge coordinates. -/
theorem boundary_at_portVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (y : (Physical M S h).EdgeWord) (p : PortEdge M S) :
    (Physical M S h).boundary y (portVertex M S p) =
      y (edgeEquiv M S (.inr (.inl (p, false)))) +
        y (edgeEquiv M S (.inr (.inl (p, true)))) := by
  rw [boundary_sum_split]
  rw [portVertex_source_edges_empty, portVertex_destination_edges]
  simp only [Finset.sum_empty, zero_add]
  have hne : edgeEquiv M S (.inr (.inl (p, false))) ≠
      edgeEquiv M S (.inr (.inl (p, true))) := by
    intro he
    have ht := (edgeEquiv M S).injective he
    cases ht
  exact Finset.sum_pair hne

private theorem loopVertex_eq_iff (M : FiniteMultiGraph) (S : Finset M.Vertex)
    {l l' : ExteriorLoop M S} {i j : Fin 2} :
    loopVertex M S l i = loopVertex M S l' j ↔ l = l' ∧ i = j := by
  constructor
  · intro h
    have hv := (vertexEquiv M S).injective h
    have he := Sum.inr.inj (Sum.inr.inj hv)
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem oldVertex_ne_loopVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (u : M.Vertex) (l : ExteriorLoop M S) (i : Fin 2) :
    oldVertex M S u ≠ loopVertex M S l i := by
  intro h
  have hv := (vertexEquiv M S).injective h
  cases hv

private theorem portVertex_ne_loopVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (p : PortEdge M S) (l : ExteriorLoop M S) (i : Fin 2) :
    portVertex M S p ≠ loopVertex M S l i := by
  intro h
  have hv := (vertexEquiv M S).injective h
  have hinner := Sum.inr.inj hv
  cases hinner

/-- Source incidences at the first private triangle vertex consist exactly
of the middle triangle edge. -/
theorem loopVertex0_source_edges (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    Finset.univ.filter (fun e : (Physical M S h).Edge =>
      (Physical M S h).src e = loopVertex M S l 0) =
      {edgeEquiv M S (.inr (.inr (l, 1)))} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    change (graph M S h).src i = _ at hi
    cases ht : (edgeEquiv M S).symm i with
    | inl e =>
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : oldVertex M S (M.src e.1) = loopVertex M S l 0 := by simpa using hi
        exact (oldVertex_ne_loopVertex M S (M.src e.1) l 0 h').elim
    | inr e =>
      cases e with
      | inl e =>
        rcases e with ⟨p, b⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        cases b
        · have h' : oldVertex M S (M.src p.1) = loopVertex M S l 0 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.src p.1) l 0 h').elim
        · have h' : oldVertex M S (M.dst p.1) = loopVertex M S l 0 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.dst p.1) l 0 h').elim
      | inr e =>
        rcases e with ⟨q, k⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        fin_cases k
        · have h' : oldVertex M S (M.src q.1) = loopVertex M S l 0 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.src q.1) l 0 h').elim
        · have h' : loopVertex M S q 0 = loopVertex M S l 0 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          rw [hq.1] at heq
          exact heq
        · have h' : loopVertex M S q 1 = loopVertex M S l 0 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          exact absurd hq.2 (by decide)
  · intro hi
    rw [hi]
    simp only [src_exteriorLoop_one]

/-- Destination incidences at the first private triangle vertex consist
exactly of the first triangle edge. -/
theorem loopVertex0_destination_edges (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    Finset.univ.filter (fun e : (Physical M S h).Edge =>
      (Physical M S h).dst e = loopVertex M S l 0) =
      {edgeEquiv M S (.inr (.inr (l, 0)))} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    change (graph M S h).dst i = _ at hi
    cases ht : (edgeEquiv M S).symm i with
    | inl e =>
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : oldVertex M S (M.dst e.1) = loopVertex M S l 0 := by simpa using hi
        exact (oldVertex_ne_loopVertex M S (M.dst e.1) l 0 h').elim
    | inr e =>
      cases e with
      | inl e =>
        rcases e with ⟨p, b⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : portVertex M S p = loopVertex M S l 0 := by simpa using hi
        exact (portVertex_ne_loopVertex M S p l 0 h').elim
      | inr e =>
        rcases e with ⟨q, k⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        fin_cases k
        · have h' : loopVertex M S q 0 = loopVertex M S l 0 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          rw [hq.1] at heq
          exact heq
        · have h' : loopVertex M S q 1 = loopVertex M S l 0 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          exact absurd hq.2 (by decide)
        · have h' : oldVertex M S (M.dst q.1) = loopVertex M S l 0 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.dst q.1) l 0 h').elim
  · intro hi
    rw [hi]
    simp only [dst_exteriorLoop_zero]

/-- Source incidences at the second private triangle vertex consist exactly
of the final triangle edge. -/
theorem loopVertex1_source_edges (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    Finset.univ.filter (fun e : (Physical M S h).Edge =>
      (Physical M S h).src e = loopVertex M S l 1) =
      {edgeEquiv M S (.inr (.inr (l, 2)))} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    change (graph M S h).src i = _ at hi
    cases ht : (edgeEquiv M S).symm i with
    | inl e =>
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : oldVertex M S (M.src e.1) = loopVertex M S l 1 := by simpa using hi
        exact (oldVertex_ne_loopVertex M S (M.src e.1) l 1 h').elim
    | inr e =>
      cases e with
      | inl e =>
        rcases e with ⟨p, b⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        cases b
        · have h' : oldVertex M S (M.src p.1) = loopVertex M S l 1 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.src p.1) l 1 h').elim
        · have h' : oldVertex M S (M.dst p.1) = loopVertex M S l 1 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.dst p.1) l 1 h').elim
      | inr e =>
        rcases e with ⟨q, k⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        fin_cases k
        · have h' : oldVertex M S (M.src q.1) = loopVertex M S l 1 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.src q.1) l 1 h').elim
        · have h' : loopVertex M S q 0 = loopVertex M S l 1 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          exact absurd hq.2 (by decide)
        · have h' : loopVertex M S q 1 = loopVertex M S l 1 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          rw [hq.1] at heq
          exact heq
  · intro hi
    rw [hi]
    simp only [src_exteriorLoop_two]

/-- Destination incidences at the second private triangle vertex consist
exactly of the middle triangle edge. -/
theorem loopVertex1_destination_edges (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    Finset.univ.filter (fun e : (Physical M S h).Edge =>
      (Physical M S h).dst e = loopVertex M S l 1) =
      {edgeEquiv M S (.inr (.inr (l, 1)))} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    change (graph M S h).dst i = _ at hi
    cases ht : (edgeEquiv M S).symm i with
    | inl e =>
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : oldVertex M S (M.dst e.1) = loopVertex M S l 1 := by simpa using hi
        exact (oldVertex_ne_loopVertex M S (M.dst e.1) l 1 h').elim
    | inr e =>
      cases e with
      | inl e =>
        rcases e with ⟨p, b⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        have h' : portVertex M S p = loopVertex M S l 1 := by simpa using hi
        exact (portVertex_ne_loopVertex M S p l 1 h').elim
      | inr e =>
        rcases e with ⟨q, k⟩
        have heq := edge_eq_tag M S ht
        rw [heq] at hi
        fin_cases k
        · have h' : loopVertex M S q 0 = loopVertex M S l 1 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          exact absurd hq.2 (by decide)
        · have h' : loopVertex M S q 1 = loopVertex M S l 1 := by simpa using hi
          have hq := (loopVertex_eq_iff M S).mp h'
          rw [hq.1] at heq
          exact heq
        · have h' : oldVertex M S (M.dst q.1) = loopVertex M S l 1 := by simpa using hi
          exact (oldVertex_ne_loopVertex M S (M.dst q.1) l 1 h').elim
  · intro hi
    rw [hi]
    simp only [dst_exteriorLoop_one]

theorem boundary_at_loopVertex0 (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (y : (Physical M S h).EdgeWord) (l : ExteriorLoop M S) :
    (Physical M S h).boundary y (loopVertex M S l 0) =
      y (edgeEquiv M S (.inr (.inr (l, 0)))) +
        y (edgeEquiv M S (.inr (.inr (l, 1)))) := by
  rw [boundary_sum_split, loopVertex0_source_edges, loopVertex0_destination_edges]
  simp only [Finset.sum_empty, zero_add, Finset.sum_singleton]
  ring

theorem boundary_at_loopVertex1 (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (y : (Physical M S h).EdgeWord) (l : ExteriorLoop M S) :
    (Physical M S h).boundary y (loopVertex M S l 1) =
      y (edgeEquiv M S (.inr (.inr (l, 1)))) +
        y (edgeEquiv M S (.inr (.inr (l, 2)))) := by
  rw [boundary_sum_split, loopVertex1_source_edges, loopVertex1_destination_edges]
  simp only [Finset.sum_empty, zero_add, Finset.sum_singleton]
  ring

/-- Every original edge has exactly one port-expansion route type. -/
noncomputable def edgeClass (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge) :
    InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S) := by
  classical
  by_cases hint : M.src e ∈ S ∧ M.dst e ∈ S
  · exact Sum.inl ⟨e, hint⟩
  · by_cases hloop : M.src e = M.dst e
    · have hout : M.src e ∉ S := by
        intro hs
        apply hint
        exact ⟨hs, by simpa [hloop] using hs⟩
      exact Sum.inr (Sum.inr ⟨e, hloop, hout⟩)
    · have hnot : ¬ (M.src e ∈ S ∧ M.dst e ∈ S) := hint
      exact Sum.inr (Sum.inl ⟨e, hloop, hnot⟩)

private def classOwner (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (c : InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S)) : M.Edge :=
  match c with
  | .inl i => i.1
  | .inr (.inl p) => p.1
  | .inr (.inr l) => l.1

private def routeClassOfTag (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (t : PortEdgeType M S) : InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S) :=
  match t with
  | .inl i => .inl i
  | .inr (.inl (p, _)) => .inr (.inl p)
  | .inr (.inr (l, _)) => .inr (.inr l)

private def edgeTagOwner (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (t : PortEdgeType M S) : M.Edge :=
  classOwner M S (routeClassOfTag M S t)

private theorem classOwner_edgeClass (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge) : classOwner M S (edgeClass M S h e) = e := by
  classical
  by_cases hint : M.src e ∈ S ∧ M.dst e ∈ S
  · simp [edgeClass, classOwner, hint]
  · by_cases hloop : M.src e = M.dst e
    · have hout : M.src e ∉ S := by
        intro hs
        apply hint
        exact ⟨hs, by simpa [hloop] using hs⟩
      have houtDst : M.dst e ∉ S := by simpa [hloop] using hout
      simp [edgeClass, classOwner, hint, hloop, hout, houtDst]
    · simp [edgeClass, classOwner, hint, hloop]

/-- The support associated to one of the three nondependent route classes. -/
noncomputable def tagRouteSupport (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S)
    (c : InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S)) :
    Finset (Physical M S h).Edge :=
  match c with
  | .inl i => {edgeEquiv M S (.inl i)}
  | .inr (.inl p) => {edgeEquiv M S (.inr (.inl (p, false))),
      edgeEquiv M S (.inr (.inl (p, true)))}
  | .inr (.inr l) => {edgeEquiv M S (.inr (.inr (l, 0))),
      edgeEquiv M S (.inr (.inr (l, 1))), edgeEquiv M S (.inr (.inr (l, 2)))}

/-- The finite physical edge support assigned to each original edge. -/
noncomputable def edgeRouteSupport (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge) : Finset (Physical M S h).Edge :=
  tagRouteSupport M S h (edgeClass M S h e)

theorem edgeRouteSupport_endpoint (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge) :
    (Physical M S h).boundary (edgeSetWord (Physical M S h)
      (edgeRouteSupport M S h e)) =
      endpointDemand M (Physical M S h) (oldVertex M S) e := by
  classical
  rw [boundary_edgeSetWord_eq_endpoint_sum]
  have howner := classOwner_edgeClass M S h e
  cases hc : edgeClass M S h e with
  | inl ie =>
      have hev : ie.1 = e := by simpa [classOwner, hc] using howner
      ext v
      simp [edgeRouteSupport, tagRouteSupport, hc, endpointDemand,
        src_internalEdge, dst_internalEdge, hev]
  | inr c =>
    cases c with
    | inl p =>
        have hev : p.1 = e := by simpa [classOwner, hc] using howner
        have hne : edgeEquiv M S (.inr (.inl (p, false))) ≠
            edgeEquiv M S (.inr (.inl (p, true))) := by
          intro hEq
          have htag := (edgeEquiv M S).injective hEq
          cases htag
        ext v
        simp only [edgeRouteSupport, tagRouteSupport, hc, Finset.sum_apply,
          endpointDemand, id_eq]
        change (∑ x ∈ {edgeEquiv M S (.inr (.inl (p, false))),
          edgeEquiv M S (.inr (.inl (p, true)))},
          ((if (graph M S h).src x = v then (1 : F₂) else 0) +
            if (graph M S h).dst x = v then 1 else 0)) = _
        rw [Finset.sum_pair hne]
        rw [src_portEdge_false, dst_portEdge, src_portEdge_true, dst_portEdge]
        rw [← hev]
        split_ifs <;> norm_num [F₂] <;> decide
    | inr l =>
        have hev : l.1 = e := by simpa [classOwner, hc] using howner
        ext v
        let a := edgeEquiv M S (.inr (.inr (l, 0)))
        let b := edgeEquiv M S (.inr (.inr (l, 1)))
        let c := edgeEquiv M S (.inr (.inr (l, 2)))
        have hab : a ≠ b := by
          intro hEq
          have ht := (edgeEquiv M S).injective hEq
          cases ht
        have hac : a ≠ c := by
          intro hEq
          have ht := (edgeEquiv M S).injective hEq
          cases ht
        have hbc : b ≠ c := by
          intro hEq
          have ht := (edgeEquiv M S).injective hEq
          cases ht
        have hnot : a ∉ ({b, c} : Finset (Physical M S h).Edge) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact fun hn => Or.elim hn hab hac
        simp only [edgeRouteSupport, tagRouteSupport, hc, Finset.sum_apply,
          endpointDemand, id_eq]
        change (∑ x ∈ {a, b, c},
          ((if (graph M S h).src x = v then (1 : F₂) else 0) +
            if (graph M S h).dst x = v then 1 else 0)) = _
        rw [Finset.sum_insert hnot, Finset.sum_pair hbc]
        dsimp [a, b, c]
        rw [src_exteriorLoop_zero, dst_exteriorLoop_zero,
          src_exteriorLoop_one, dst_exteriorLoop_one,
          src_exteriorLoop_two, dst_exteriorLoop_two]
        rw [← hev]
        split_ifs <;> norm_num [F₂] <;> decide

/-- Every edge in one tag support decodes to a tag with the same original
auxiliary edge. -/
theorem tagRouteSupport_owner (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S)
    (c : InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S))
    {i : (Physical M S h).Edge} (hi : i ∈ tagRouteSupport M S h c) :
    classOwner M S c = edgeTagOwner M S ((edgeEquiv M S).symm i) := by
  cases c with
  | inl ie =>
      simp only [tagRouteSupport, Finset.mem_singleton] at hi
      subst i
      simp [edgeTagOwner, routeClassOfTag, classOwner]
  | inr c =>
      cases c with
      | inl p =>
          simp only [tagRouteSupport, Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with hi | hi <;> subst i <;>
            simp [edgeTagOwner, routeClassOfTag, classOwner]
      | inr l =>
          simp only [tagRouteSupport, Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with hi | hi | hi <;> subst i <;>
            simp [edgeTagOwner, routeClassOfTag, classOwner]

theorem edgeRouteSupport_owner (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge)
    {i : (Physical M S h).Edge} (hi : i ∈ edgeRouteSupport M S h e) :
    e = edgeTagOwner M S ((edgeEquiv M S).symm i) := by
  unfold edgeRouteSupport at hi
  have ho := tagRouteSupport_owner M S h _ hi
  rw [classOwner_edgeClass] at ho
  exact ho

theorem edgeClass_classOwner (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S)
    (c : InternalEdge M S ⊕ (PortEdge M S ⊕ ExteriorLoop M S)) :
    edgeClass M S h (classOwner M S c) = c := by
  cases c with
  | inl ie =>
      have hnl := h.2.1 ie.1 ie.2.1 ie.2.2
      simp [edgeClass, classOwner, ie.2, hnl]
  | inr c =>
      cases c with
      | inl p =>
          have hnot : ¬ (M.src p.1 ∈ S ∧ M.dst p.1 ∈ S) := p.2.2
          have hnl : M.src p.1 ≠ M.dst p.1 := p.2.1
          simp [edgeClass, classOwner, hnot, hnl]
      | inr l =>
          have hnot : ¬ (M.src l.1 ∈ S ∧ M.dst l.1 ∈ S) := by
            intro hboth
            exact l.2.2 hboth.1
          have houtDst : M.dst l.1 ∉ S := by simpa [l.2.1] using l.2.2
          simp [edgeClass, classOwner, hnot, l.2.1, l.2.2, houtDst]

/-- The route supports are pairwise disjoint. -/
theorem edgeRouteSupport_disjoint (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) {e f : M.Edge} (hef : e ≠ f) :
    Disjoint (edgeRouteSupport M S h e) (edgeRouteSupport M S h f) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have he := edgeRouteSupport_owner M S h e hi
  have hf := edgeRouteSupport_owner M S h f hj
  exact hef (he.trans hf.symm)

theorem edgeRouteSupport_nonempty (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : M.Edge) :
    (edgeRouteSupport M S h e).Nonempty := by
  cases hc : edgeClass M S h e with
  | inl ie => exact ⟨edgeEquiv M S (.inl ie), by simp [edgeRouteSupport, tagRouteSupport, hc]⟩
  | inr c =>
    cases c with
    | inl p =>
        exact ⟨edgeEquiv M S (.inr (.inl (p, false))), by
          simp [edgeRouteSupport, tagRouteSupport, hc]⟩
    | inr l =>
        exact ⟨edgeEquiv M S (.inr (.inr (l, 0))), by
          simp [edgeRouteSupport, tagRouteSupport, hc]⟩

theorem edgeRouteSupport_cover (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) :
    ∀ i : (Physical M S h).Edge, ∃ e : M.Edge, i ∈ edgeRouteSupport M S h e := by
  intro i
  let t := (edgeEquiv M S).symm i
  let c := routeClassOfTag M S t
  let e := edgeTagOwner M S t
  have hiTag : i = edgeEquiv M S t := by
    dsimp [t]
    exact (Equiv.apply_symm_apply (edgeEquiv M S) i).symm
  have hc : edgeClass M S h e = c := by
    dsimp [e, edgeTagOwner, c]
    exact edgeClass_classOwner M S h (routeClassOfTag M S t)
  refine ⟨e, ?_⟩
  change i ∈ tagRouteSupport M S h (edgeClass M S h e)
  rw [hc]
  rw [hiTag]
  cases ht : t with
  | inl ie => simp [c, ht, routeClassOfTag, tagRouteSupport]
  | inr c =>
    cases c with
      | inl pb =>
        rcases pb with ⟨p, b⟩
        cases b <;> simp [c, ht, routeClassOfTag, tagRouteSupport]
      | inr lk =>
        rcases lk with ⟨l, k⟩
        fin_cases k <;> simp [c, ht, routeClassOfTag, tagRouteSupport]

/-- The direct/port/triangle routes form an edge-disjoint route system from
the auxiliary graph into its root-preserving physical expansion. -/
noncomputable def rootPortRouteSystem (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) :
    EdgeDisjointRouteSystem M (Physical M S h) where
  vertexMap := oldVertex M S
  support := edgeRouteSupport M S h
  endpoint := edgeRouteSupport_endpoint M S h
  disjoint := fun {_ _} hn => edgeRouteSupport_disjoint M S h hn
  nonempty := edgeRouteSupport_nonempty M S h

theorem oldVertex_injective (M : FiniteMultiGraph) (S : Finset M.Vertex) :
    Function.Injective (oldVertex M S) := by
  intro u v huv
  have htag := (vertexEquiv M S).injective huv
  exact Sum.inl.inj htag

private theorem equal_of_f2_add_eq_zero {a b : F₂} (hab : a + b = 0) : a = b := by
  have hneg : -b = b := by
    fin_cases b <;> decide
  have h' := eq_neg_of_add_eq_zero_left hab
  rw [hneg] at h'
  exact h'

/-- Cycle words are constant on each direct, two-edge, or private-triangle
route. The nontrivial equalities are read from the exact private-vertex
boundary formulas proved above. -/
theorem cycle_word_constant_on_rootPortRoute
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S)
    (y : (Physical M S h).EdgeWord) (hy : y ∈ (Physical M S h).CycleSpace) :
    ∀ e i j, i ∈ edgeRouteSupport M S h e → j ∈ edgeRouteSupport M S h e →
      y i = y j := by
  classical
  intro e i j hi hj
  cases hc : edgeClass M S h e with
  | inl ie =>
      have hit : i = edgeEquiv M S (.inl ie) := by
        simpa [edgeRouteSupport, tagRouteSupport, hc] using hi
      have hjt : j = edgeEquiv M S (.inl ie) := by
        simpa [edgeRouteSupport, tagRouteSupport, hc] using hj
      rw [hit, hjt]
  | inr c =>
    cases c with
    | inl p =>
        have hit : i = edgeEquiv M S (.inr (.inl (p, false))) ∨
            i = edgeEquiv M S (.inr (.inl (p, true))) := by
          simpa [edgeRouteSupport, tagRouteSupport, hc] using hi
        have hjt : j = edgeEquiv M S (.inr (.inl (p, false))) ∨
            j = edgeEquiv M S (.inr (.inl (p, true))) := by
          simpa [edgeRouteSupport, tagRouteSupport, hc] using hj
        have hzero : (Physical M S h).boundary y (portVertex M S p) = 0 :=
          congrFun hy (portVertex M S p)
        rw [boundary_at_portVertex] at hzero
        have heq := equal_of_f2_add_eq_zero hzero
        rcases hit with hi0 | hi1
        · rcases hjt with hj0 | hj1
          · rw [hi0, hj0]
          · rw [hi0, hj1]
            exact heq
        · rcases hjt with hj0 | hj1
          · rw [hi1, hj0]
            exact heq.symm
          · rw [hi1, hj1]
    | inr l =>
        have hit : i = edgeEquiv M S (.inr (.inr (l, 0))) ∨
            i = edgeEquiv M S (.inr (.inr (l, 1))) ∨
            i = edgeEquiv M S (.inr (.inr (l, 2))) := by
          simpa [edgeRouteSupport, tagRouteSupport, hc] using hi
        have hjt : j = edgeEquiv M S (.inr (.inr (l, 0))) ∨
            j = edgeEquiv M S (.inr (.inr (l, 1))) ∨
            j = edgeEquiv M S (.inr (.inr (l, 2))) := by
          simpa [edgeRouteSupport, tagRouteSupport, hc] using hj
        have hz0 : (Physical M S h).boundary y (loopVertex M S l 0) = 0 :=
          congrFun hy (loopVertex M S l 0)
        have hz1 : (Physical M S h).boundary y (loopVertex M S l 1) = 0 :=
          congrFun hy (loopVertex M S l 1)
        rw [boundary_at_loopVertex0] at hz0
        rw [boundary_at_loopVertex1] at hz1
        have h01 := equal_of_f2_add_eq_zero hz0
        have h12 := equal_of_f2_add_eq_zero hz1
        have h02 := h01.trans h12
        rcases hit with hi0 | hi1 | hi2
        · rcases hjt with hj0 | hj1 | hj2
          · rw [hi0, hj0]
          · rw [hi0, hj1]
            exact h01
          · rw [hi0, hj2]
            exact h02
        · rcases hjt with hj0 | hj1 | hj2
          · rw [hi1, hj0]
            exact h01.symm
          · rw [hi1, hj1]
          · rw [hi1, hj2]
            exact h12
        · rcases hjt with hj0 | hj1 | hj2
          · rw [hi2, hj0]
            exact h02.symm
          · rw [hi2, hj1]
            exact h12.symm
          · rw [hi2, hj2]

theorem rootPort_cycleExpandMap_bijective
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S) :
    Function.Bijective
      (FiniteMultiGraph.cycleExpandMap (rootPortRouteSystem M S h)) := by
  apply FiniteMultiGraph.cycleExpandMap_bijective_of_injective
    (rootPortRouteSystem M S h)
  · exact oldVertex_injective M S
  · exact edgeRouteSupport_cover M S h
  · exact cycle_word_constant_on_rootPortRoute M S h

/-- The route expansion gives a genuine linear equivalence of cycle spaces. -/
noncomputable def rootPortCycleEquiv
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S) :
    M.CycleSpace ≃ₗ[F₂] (Physical M S h).CycleSpace :=
  LinearEquiv.ofBijective
    (FiniteMultiGraph.cycleExpandMap (rootPortRouteSystem M S h))
    (rootPort_cycleExpandMap_bijective M S h)

/-- On an edge internal to the auxiliary root, expansion reads exactly the
original edge coefficient at the corresponding direct physical edge. -/
theorem rootPortCycleEquiv_apply_internal
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S)
    (x : M.CycleSpace) (e : M.Edge)
    (hs : M.src e ∈ S) (hd : M.dst e ∈ S) :
    (rootPortCycleEquiv M S h x).1
      (edgeEquiv M S (.inl ⟨e, hs, hd⟩)) = x.1 e := by
  let p := edgeEquiv M S (.inl ⟨e, hs, hd⟩)
  have hp : p ∈ (rootPortRouteSystem M S h).support e := by
    simp [p, rootPortRouteSystem, edgeRouteSupport, tagRouteSupport,
      edgeClass, hs, hd]
  change FiniteMultiGraph.expand M (Physical M S h)
    (rootPortRouteSystem M S h) x.1 p = x.1 e
  exact FiniteMultiGraph.expand_apply_of_mem_support M (Physical M S h)
    (rootPortRouteSystem M S h) x.1 e p hp

/-- The direct physical label of an auxiliary edge internal to `K`. -/
noncomputable def internalDirectEdge (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) (e : {e : M.Edge //
      e ∈ CleanupSpecification.internalEdges M K}) :
    (Physical M S h).Edge := by
  have he : M.src e.1 ∈ K ∧ M.dst e.1 ∈ K := by
    have hm := e.2
    change e.1 ∈ Finset.univ.filter (fun f => M.src f ∈ K ∧ M.dst f ∈ K) at hm
    exact (Finset.mem_filter.mp hm).2
  exact edgeEquiv M S (.inl ⟨e.1, hKS he.1, hKS he.2⟩)

def oldVertexImage (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (K : Finset M.Vertex) : Finset (Physical M S h).Vertex :=
  K.image (oldVertex M S)

private theorem portVertex_not_oldVertexImage (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (K : Finset M.Vertex) (p : PortEdge M S) :
    portVertex M S p ∉ oldVertexImage M S h K := by
  intro hp
  rcases Finset.mem_image.mp hp with ⟨u, hu, heq⟩
  exact oldVertex_ne_portVertex M S u p heq

private theorem loopVertex_not_oldVertexImage (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (h : IsCleanupRoot M S) (K : Finset M.Vertex) (l : ExteriorLoop M S) (j : Fin 2) :
    loopVertex M S l j ∉ oldVertexImage M S h K := by
  intro hp
  rcases Finset.mem_image.mp hp with ⟨u, hu, heq⟩
  exact oldVertex_ne_loopVertex M S u l j heq

/-- On every auxiliary edge internal to `K ⊆ S`, the cycle equivalence reads
the original coefficient at the corresponding direct physical edge. -/
theorem rootPortCycleEquiv_internalEdges_word
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace)
    (e : {e : M.Edge // e ∈ CleanupSpecification.internalEdges M K}) :
    (rootPortCycleEquiv M S h x).1 (internalDirectEdge M S K h hKS e) = x.1 e.1 := by
  have he : M.src e.1 ∈ K ∧ M.dst e.1 ∈ K := by
    have hm := e.2
    change e.1 ∈ Finset.univ.filter (fun f => M.src f ∈ K ∧ M.dst f ∈ K) at hm
    exact (Finset.mem_filter.mp hm).2
  unfold internalDirectEdge
  dsimp
  exact rootPortCycleEquiv_apply_internal M S h x e.1
    (hKS he.1) (hKS he.2)

/-- The edges induced on an old-vertex image contain exactly the direct
physical copies of the auxiliary edges induced on the original set. Private
port and triangle vertices are excluded from the image by construction. -/
theorem rootPort_internalEdges_image_eq
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) :
    CleanupSpecification.internalEdges (Physical M S h)
      (oldVertexImage M S h K) =
    (CleanupSpecification.internalEdges M K).attach.image
      (fun e => internalDirectEdge M S K h hKS e) := by
  classical
  ext i
  constructor
  · intro hi
    have hends : (Physical M S h).src i ∈ oldVertexImage M S h K ∧
        (Physical M S h).dst i ∈ oldVertexImage M S h K := by
      simpa [CleanupSpecification.internalEdges] using hi
    cases ht : (edgeEquiv M S).symm i with
    | inl ie =>
        have htag := edge_eq_tag M S ht
        rw [htag] at hends
        have hsrcImage : oldVertex M S (M.src ie.1) ∈ oldVertexImage M S h K := by
          simpa [src_internalEdge] using hends.1
        have hdstImage : oldVertex M S (M.dst ie.1) ∈ oldVertexImage M S h K := by
          simpa [dst_internalEdge] using hends.2
        have hs : M.src ie.1 ∈ K := by
          rcases Finset.mem_image.mp (by simpa [oldVertexImage] using hsrcImage) with
            ⟨u, hu, huv⟩
          exact oldVertex_injective M S huv ▸ hu
        have hd : M.dst ie.1 ∈ K := by
          rcases Finset.mem_image.mp (by simpa [oldVertexImage] using hdstImage) with
            ⟨u, hu, huv⟩
          exact oldVertex_injective M S huv ▸ hu
        have he : ie.1 ∈ CleanupSpecification.internalEdges M K := by
          change ie.1 ∈ Finset.univ.filter
            (fun e => M.src e ∈ K ∧ M.dst e ∈ K)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hd⟩
        refine Finset.mem_image.mpr ⟨⟨ie.1, he⟩, Finset.mem_attach _ _, ?_⟩
        simp [internalDirectEdge, htag]
    | inr c =>
      cases c with
      | inl p =>
          rcases p with ⟨p, b⟩
          have htag := edge_eq_tag M S ht
          rw [htag] at hends
          have hpriv : portVertex M S p ∈ oldVertexImage M S h K := by
            simpa [dst_portEdge] using hends.2
          exact (portVertex_not_oldVertexImage M S h K p hpriv).elim
      | inr l =>
          rcases l with ⟨l, k⟩
          have htag := edge_eq_tag M S ht
          rw [htag] at hends
          fin_cases k
          · have hpriv : loopVertex M S l 0 ∈ oldVertexImage M S h K := by
              simpa [dst_exteriorLoop_zero] using hends.2
            exact (loopVertex_not_oldVertexImage M S h K l 0 hpriv).elim
          · have hpriv : loopVertex M S l 1 ∈ oldVertexImage M S h K := by
              simpa [dst_exteriorLoop_one] using hends.2
            exact (loopVertex_not_oldVertexImage M S h K l 1 hpriv).elim
          · have hpriv : loopVertex M S l 1 ∈ oldVertexImage M S h K := by
              simpa [src_exteriorLoop_two] using hends.1
            exact (loopVertex_not_oldVertexImage M S h K l 1 hpriv).elim
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, rfl⟩
    have hend : M.src e.1 ∈ K ∧ M.dst e.1 ∈ K := by
      have hm := e.2
      change e.1 ∈ Finset.univ.filter
        (fun f => M.src f ∈ K ∧ M.dst f ∈ K) at hm
      exact (Finset.mem_filter.mp hm).2
    change internalDirectEdge M S K h hKS e ∈ Finset.univ.filter
      (fun i => (Physical M S h).src i ∈ oldVertexImage M S h K ∧
        (Physical M S h).dst i ∈ oldVertexImage M S h K)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · simp only [internalDirectEdge, src_internalEdge, dst_internalEdge]
      change oldVertex M S (M.src e.1) ∈ K.image (oldVertex M S) ∧
        oldVertex M S (M.dst e.1) ∈ K.image (oldVertex M S)
      exact ⟨Finset.mem_image.mpr ⟨M.src e.1, hend.1, rfl⟩,
        Finset.mem_image.mpr ⟨M.dst e.1, hend.2, rfl⟩⟩

/-- Every physical edge tested by the old-image restriction decodes uniquely
to an auxiliary edge tested by `K`; its expanded coefficient is the same. -/
theorem rootPortCycleEquiv_internalEdges_lookup
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace)
    {i : (Physical M S h).Edge}
    (hi : i ∈ CleanupSpecification.internalEdges
      (Physical M S h) (oldVertexImage M S h K)) :
    ∃ e : {e : M.Edge // e ∈ CleanupSpecification.internalEdges M K},
      internalDirectEdge M S K h hKS e = i ∧
        (rootPortCycleEquiv M S h x).1 i = x.1 e.1 := by
  rw [rootPort_internalEdges_image_eq M S K h hKS] at hi
  rcases Finset.mem_image.mp hi with ⟨e, _, heq⟩
  refine ⟨e, heq, ?_⟩
  rw [← heq]
  exact rootPortCycleEquiv_internalEdges_word M S K h hKS x e

/-- The physical port expansion is globally loopless and has no parallel
labelled edges, so the first two linear-forest clauses hold for every word. -/
theorem rootPort_word_loopless_parallel
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S)
    (y : (Physical M S h).EdgeWord) :
    (∀ e, y e ≠ 0 → (Physical M S h).src e ≠ (Physical M S h).dst e) ∧
    (∀ e f, e ≠ f → y e ≠ 0 → y f ≠ 0 →
      (( (Physical M S h).src e = (Physical M S h).src f ∧
          (Physical M S h).dst e = (Physical M S h).dst f) ∨
       ( (Physical M S h).src e = (Physical M S h).dst f ∧
          (Physical M S h).dst e = (Physical M S h).src f)) → False) := by
  constructor
  · intro e _
    change (graph M S h).src e ≠ (graph M S h).dst e
    exact (graph M S h).noLoops e
  · intro e f hef _ _ hends
    have heq : e = f := by
      apply (graph M S h).simple
      exact hends
    exact hef heq

/-- A selected adjacency in the physical restriction has both endpoints in
the old-vertex image. In particular every expanded vertex outside that image
is isolated in the selected graph. -/
theorem rootPort_restricted_selected_adj_supported
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (x : M.CycleSpace) {u v : (Physical M S h).Vertex}
    (hadj : (CleanupSpecification.selectedGraph (Physical M S h)
      (fun e => if e ∈ CleanupSpecification.internalEdges
        (Physical M S h) (oldVertexImage M S h K)
        then (rootPortCycleEquiv M S h x).1 e else 0)).Adj u v) :
    u ∈ oldVertexImage M S h K ∧ v ∈ oldVertexImage M S h K := by
  rcases hadj with ⟨_, e, he, hends⟩
  have heInternal : e ∈ CleanupSpecification.internalEdges
      (Physical M S h) (oldVertexImage M S h K) := by
    by_contra hn
    simp [hn] at he
  have hend := (Finset.mem_filter.mp heInternal).2
  rcases hends with hends | hends
  · exact ⟨(congrArg (fun z => z ∈ oldVertexImage M S h K) hends.1).mp hend.1,
      (congrArg (fun z => z ∈ oldVertexImage M S h K) hends.2).mp hend.2⟩
  · exact ⟨(congrArg (fun z => z ∈ oldVertexImage M S h K) hends.2).mp hend.2,
      (congrArg (fun z => z ∈ oldVertexImage M S h K) hends.1).mp hend.1⟩

/-- A walk in a graph whose support lies in `U` can be regarded as a walk in
the induced graph on `U`, with its support unchanged after forgetting the
subtype. -/
private theorem liftSimpleWalkToInduce {V : Type*} (G : SimpleGraph V)
    {U : Finset V} {u v : V} (p : G.Walk u v)
    (hU : ∀ x ∈ p.support, x ∈ U) :
    ∃ q : (G.induce (U : Set V)).Walk
      ⟨u, hU u (Walk.start_mem_support p)⟩
      ⟨v, hU v (Walk.end_mem_support p)⟩,
      List.map Subtype.val q.support = p.support ∧
        List.map (Sym2.map Subtype.val) q.edges = p.edges := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl, rfl⟩
  | @cons a b c hab p ih =>
      have ha : a ∈ U := hU a (by simp)
      have hb : b ∈ U := hU b (by simp)
      have hc : c ∈ U := hU c (by simp)
      have htail : ∀ x ∈ p.support, x ∈ U := by
        intro x hx
        exact hU x (by simp [hx])
      obtain ⟨q, hq, heq⟩ := ih htail
      let x : {z : V // z ∈ U} := ⟨a, ha⟩
      let y : {z : V // z ∈ U} := ⟨b, hb⟩
      have hab' : (G.induce (U : Set V)).Adj x y := hab
      refine ⟨Walk.cons hab' q, ?_⟩
      constructor
      · simp only [Walk.support_cons, List.map_cons, Subtype.coe_mk]
        simpa [Walk.support_cons] using congrArg (List.cons b) hq
      · simp only [Walk.edges_cons, List.map_cons, Sym2.map_pair_eq]
        simpa [x, y] using congrArg (List.cons s(b, c)) heq

private theorem walk_support_mem_of_adj_supported {V : Type*} (G : SimpleGraph V)
    (U : Finset V) (hsupported : ∀ a b, G.Adj a b → a ∈ U ∧ b ∈ U)
    {a b : V} (p : G.Walk a b) (ha : a ∈ U) :
    ∀ x ∈ p.support, x ∈ U := by
  induction p with
  | nil =>
      intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact ha
  | @cons a b c hab p ih =>
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with hxa | hx
      · exact hxa ▸ (hsupported a b hab).1
      · exact ih (hsupported a b hab).2 x hx

/-- Acyclicity of the induced graph suffices when the ambient graph has no
edges leaving the induced vertex set. -/
theorem isAcyclic_of_supported_induce {V : Type*} (G : SimpleGraph V)
    (U : Finset V)
    (hsupported : ∀ a b, G.Adj a b → a ∈ U ∧ b ∈ U)
    (hacyclic : (G.induce (U : Set V)).IsAcyclic) : G.IsAcyclic := by
  intro u p hp
  cases p with
  | nil => exact hp.ne_nil rfl
  | cons hab tail =>
      have hu : u ∈ U := (hsupported _ _ hab).1
      have hU := walk_support_mem_of_adj_supported G U hsupported
        (Walk.cons hab tail) hu
      obtain ⟨q, hsupport, hedges⟩ :=
        liftSimpleWalkToInduce G (Walk.cons hab tail) hU
      have hqEdgesNodup : q.edges.Nodup := by
        apply List.Nodup.of_map (Sym2.map Subtype.val)
        simpa [hedges] using hp.toIsCircuit.toIsTrail.edges_nodup
      have hqNeNil : q ≠ Walk.nil := by
        intro hq
        have hlen := congrArg List.length hedges
        simp [hq] at hlen
      have hqTailNodup : q.support.tail.Nodup := by
        apply List.Nodup.of_map Subtype.val
        have htail : List.map Subtype.val q.support.tail =
            (Walk.cons hab tail).support.tail := by
          calc
            List.map Subtype.val q.support.tail = (List.map Subtype.val q.support).tail := by simp
            _ = (Walk.cons hab tail).support.tail := congrArg List.tail hsupport
        rw [htail]
        exact hp.support_nodup
      have hqCycle : q.IsCycle :=
        ⟨⟨⟨hqEdgesNodup⟩, hqNeNil⟩, hqTailNodup⟩
      exact hacyclic q hqCycle

theorem isAcyclic_induce_of_isAcyclic {V : Type*} (G : SimpleGraph V)
    (U : Finset V) (hacyclic : G.IsAcyclic) :
    (G.induce (U : Set V)).IsAcyclic := by
  intro u p hp
  let f : G.induce (U : Set V) →g G :=
    { toFun := Subtype.val, map_rel' := by intro a b hab; exact hab }
  have hc : (p.map f).IsCycle :=
    (Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
  exact hacyclic (p.map f) hc

def rootPortAuxRestriction (M : FiniteMultiGraph) (K : Finset M.Vertex)
    (x : M.CycleSpace) : M.EdgeWord :=
  fun e => if e ∈ CleanupSpecification.internalEdges M K then x.1 e else 0

def rootPortPhysicalRestriction (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) (x : M.CycleSpace) :
    (Physical M S h).EdgeWord :=
  fun e => if e ∈ CleanupSpecification.internalEdges (Physical M S h)
      (oldVertexImage M S h K)
    then (rootPortCycleEquiv M S h x).1 e else 0

/-- Selected adjacency on the old-vertex images is exactly the adjacency
selected by the auxiliary restriction. This is the graph-level core of the
acyclicity transfer; private expansion vertices cannot occur in this
restriction. -/
theorem rootPort_selectedAdj_iff
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace) (u v : M.Vertex)
    (hu : u ∈ K) (hv : v ∈ K) :
    (CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)).Adj u v ↔
      (CleanupSpecification.selectedGraph (Physical M S h)
        (rootPortPhysicalRestriction M S K h hKS x)).Adj
          (oldVertex M S u) (oldVertex M S v) := by
  classical
  constructor
  · rintro ⟨hne, e, he, hends⟩
    have heK : e ∈ CleanupSpecification.internalEdges M K := by
      by_contra hn
      simp [rootPortAuxRestriction, hn] at he
    have heprops := (Finset.mem_filter.mp heK).2
    let eK : {e : M.Edge // e ∈ CleanupSpecification.internalEdges M K} := ⟨e, heK⟩
    let j := internalDirectEdge M S K h hKS eK
    have hmem : j ∈ CleanupSpecification.internalEdges (Physical M S h)
        (oldVertexImage M S h K) := by
      rw [rootPort_internalEdges_image_eq M S K h hKS]
      exact Finset.mem_image.mpr ⟨eK, Finset.mem_attach _ _, rfl⟩
    have hvalue : (rootPortCycleEquiv M S h x).1 j = x.1 e := by
      exact rootPortCycleEquiv_internalEdges_word M S K h hKS x eK
    have hcoeff : (rootPortPhysicalRestriction M S K h hKS x) j ≠ 0 := by
      simpa [rootPortPhysicalRestriction, hmem, hvalue,
        rootPortAuxRestriction, heK] using he
    have hne' : oldVertex M S u ≠ oldVertex M S v := by
      intro huv
      exact hne (oldVertex_injective M S huv)
    have hends' :
        ((Physical M S h).src j = oldVertex M S u ∧
          (Physical M S h).dst j = oldVertex M S v) ∨
        ((Physical M S h).src j = oldVertex M S v ∧
          (Physical M S h).dst j = oldVertex M S u) := by
      rcases hends with hends | hends
      · left
        constructor
        · simpa [j, internalDirectEdge, src_internalEdge] using
            congrArg (oldVertex M S) hends.1
        · simpa [j, internalDirectEdge, dst_internalEdge] using
            congrArg (oldVertex M S) hends.2
      · right
        constructor
        · simpa [j, internalDirectEdge, src_internalEdge] using
            congrArg (oldVertex M S) hends.1
        · simpa [j, internalDirectEdge, dst_internalEdge] using
            congrArg (oldVertex M S) hends.2
    exact ⟨hne', j, hcoeff, hends'⟩
  · rintro ⟨hne, i, hi, hends⟩
    have hiK : i ∈ CleanupSpecification.internalEdges (Physical M S h)
        (oldVertexImage M S h K) := by
      by_contra hn
      simp [rootPortPhysicalRestriction, hn] at hi
    obtain ⟨e, heq, hvalue⟩ := rootPortCycleEquiv_internalEdges_lookup
      M S K h hKS x hiK
    have heK := e.2
    have heprops := (Finset.mem_filter.mp heK).2
    have hauxCoeff : (rootPortAuxRestriction M K x) e.1 ≠ 0 := by
      have hx : x.1 e.1 ≠ 0 := by
        intro hz
        apply hi
        rw [← heq]
        simp [rootPortPhysicalRestriction,
          rootPort_internalEdges_image_eq M S K h hKS, heq, hvalue, hz]
      simpa [rootPortAuxRestriction, heK] using hx
    have hends' :
        (M.src e.1 = u ∧ M.dst e.1 = v) ∨
        (M.src e.1 = v ∧ M.dst e.1 = u) := by
      rcases hends with hends | hends
      · left
        constructor
        · apply oldVertex_injective M S
          have hs : (Physical M S h).src (internalDirectEdge M S K h hKS e) =
              oldVertex M S u := by rw [heq]; exact hends.1
          simpa [internalDirectEdge, src_internalEdge] using hs
        · apply oldVertex_injective M S
          have hd : (Physical M S h).dst (internalDirectEdge M S K h hKS e) =
              oldVertex M S v := by rw [heq]; exact hends.2
          simpa [internalDirectEdge, dst_internalEdge] using hd
      · right
        constructor
        · apply oldVertex_injective M S
          have hs : (Physical M S h).src (internalDirectEdge M S K h hKS e) =
              oldVertex M S v := by rw [heq]; exact hends.1
          simpa [internalDirectEdge, src_internalEdge] using hs
        · apply oldVertex_injective M S
          have hd : (Physical M S h).dst (internalDirectEdge M S K h hKS e) =
              oldVertex M S u := by rw [heq]; exact hends.2
          simpa [internalDirectEdge, dst_internalEdge] using hd
    have hne' : u ≠ v := by
      intro huv
      apply hne
      exact congrArg (oldVertex M S) huv
    exact ⟨hne', e.1, hauxCoeff, hends'⟩

noncomputable def rootPortOldVertexEquiv
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S) :
    {u : M.Vertex // u ∈ K} ≃
      {v : (Physical M S h).Vertex // v ∈ oldVertexImage M S h K} := by
  classical
  let f : {u : M.Vertex // u ∈ K} →
      {v : (Physical M S h).Vertex // v ∈ oldVertexImage M S h K} := fun u =>
    ⟨oldVertex M S u.1, Finset.mem_image.mpr ⟨u.1, u.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact oldVertex_injective M S (congrArg Subtype.val huv)
    · intro v
      rcases Finset.mem_image.mp v.2 with ⟨u, hu, huv⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      exact huv
  exact Equiv.ofBijective f hf

/-- The old-vertex image identifies the two induced selected graphs. -/
noncomputable def rootPortSelectedGraphIso
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace) :
    (CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)).induce
        (↑K : Set M.Vertex) ≃g
      (CleanupSpecification.selectedGraph (Physical M S h)
        (rootPortPhysicalRestriction M S K h hKS x)).induce
        (↑(oldVertexImage M S h K) : Set (Physical M S h).Vertex) := by
  refine ⟨rootPortOldVertexEquiv M S K h, ?_⟩
  intro a b
  exact (rootPort_selectedAdj_iff M S K h hKS x a.1 b.1 a.2 b.2).symm

theorem rootPortSelectedGraphIso_isAcyclic_iff
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace) :
    ((CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)).induce
      (↑K : Set M.Vertex)).IsAcyclic ↔
    ((CleanupSpecification.selectedGraph (Physical M S h)
      (rootPortPhysicalRestriction M S K h hKS x)).induce
      (↑(oldVertexImage M S h K) : Set (Physical M S h).Vertex)).IsAcyclic := by
  let f := rootPortSelectedGraphIso M S K h hKS x
  constructor
  · intro ha v p hp
    have hm : (p.map f.symm.toHom).IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective f.symm.injective).2 hp
    exact ha (p.map f.symm.toHom) hm
  · intro hb v p hp
    have hm : (p.map f.toHom).IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective f.injective).2 hp
    exact hb (p.map f.toHom) hm

private theorem rootPort_aux_selected_adj_supported
    (M : FiniteMultiGraph) (K : Finset M.Vertex) (x : M.CycleSpace)
    {u v : M.Vertex}
    (hadj : (CleanupSpecification.selectedGraph M
      (rootPortAuxRestriction M K x)).Adj u v) : u ∈ K ∧ v ∈ K := by
  rcases hadj with ⟨_, e, he, hend⟩
  have heK : e ∈ CleanupSpecification.internalEdges M K := by
    by_contra hn
    simp [rootPortAuxRestriction, hn] at he
  have hendK := (Finset.mem_filter.mp heK).2
  rcases hend with h | h
  · exact ⟨h.1 ▸ hendK.1, h.2 ▸ hendK.2⟩
  · exact ⟨h.2 ▸ hendK.2, h.1 ▸ hendK.1⟩

/-- Full selected-graph acyclicity is equivalent across the root-port
expansion: all selected physical edges are induced on the old vertices, and
those induced graphs are isomorphic to the auxiliary restriction. -/
theorem rootPort_restriction_isAcyclic_iff
    (M : FiniteMultiGraph) (S K : Finset M.Vertex) (h : IsCleanupRoot M S)
    (hKS : K ⊆ S) (x : M.CycleSpace) :
    (CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)).IsAcyclic ↔
    (CleanupSpecification.selectedGraph (Physical M S h)
      (rootPortPhysicalRestriction M S K h hKS x)).IsAcyclic := by
  constructor
  · intro ha
    apply isAcyclic_of_supported_induce
      (CleanupSpecification.selectedGraph (Physical M S h)
        (rootPortPhysicalRestriction M S K h hKS x))
      (oldVertexImage M S h K)
    · exact fun a b hab => rootPort_restricted_selected_adj_supported M S K h x hab
    · apply (rootPortSelectedGraphIso_isAcyclic_iff M S K h hKS x).mp
      exact isAcyclic_induce_of_isAcyclic
        (CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)) K ha
  · intro hb
    apply isAcyclic_of_supported_induce
      (CleanupSpecification.selectedGraph M (rootPortAuxRestriction M K x)) K
    · exact fun a b hab => rootPort_aux_selected_adj_supported M K x hab
    · apply (rootPortSelectedGraphIso_isAcyclic_iff M S K h hKS x).mpr
      exact isAcyclic_induce_of_isAcyclic
        (CleanupSpecification.selectedGraph (Physical M S h)
          (rootPortPhysicalRestriction M S K h hKS x))
        (oldVertexImage M S h K) hb














end Erdos1016.Proof.PortExpansionCycleSpace
end

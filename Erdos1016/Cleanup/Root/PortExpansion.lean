import Erdos1016.Cleanup.CleanupSpecification
import Erdos1016.Graph.PathExpansion.InjectiveCycleEquivalence
import Erdos1016.Graph.CutPacking

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpansion

open Erdos1016
open Erdos1016.Proof.CleanupSpecification

/-!
Root-preserving expansion of a finite labelled multigraph. Edges internal to
the root remain direct, other nonloop edges receive a private midpoint, and
each exterior loop receives a private triangle. All new vertices are outside
the root.
-/

abbrev InternalEdge (M : FiniteMultiGraph) (S : Finset M.Vertex) :=
  {e : M.Edge // M.src e ∈ S ∧ M.dst e ∈ S}

abbrev PortEdge (M : FiniteMultiGraph) (S : Finset M.Vertex) :=
  {e : M.Edge // M.src e ≠ M.dst e ∧ ¬ (M.src e ∈ S ∧ M.dst e ∈ S)}

abbrev ExteriorLoop (M : FiniteMultiGraph) (S : Finset M.Vertex) :=
  {e : M.Edge // M.src e = M.dst e ∧ M.src e ∉ S}

abbrev PortVertexType (M : FiniteMultiGraph) (S : Finset M.Vertex) :=
  M.Vertex ⊕ (PortEdge M S ⊕ (ExteriorLoop M S × Fin 2))

abbrev PortEdgeType (M : FiniteMultiGraph) (S : Finset M.Vertex) :=
  InternalEdge M S ⊕ ((PortEdge M S × Bool) ⊕ (ExteriorLoop M S × Fin 3))

def vertexCount (M : FiniteMultiGraph) (S : Finset M.Vertex) : ℕ :=
  Fintype.card (PortVertexType M S)

def edgeCount (M : FiniteMultiGraph) (S : Finset M.Vertex) : ℕ :=
  Fintype.card (PortEdgeType M S)

noncomputable def vertexEquiv (M : FiniteMultiGraph) (S : Finset M.Vertex) :
    PortVertexType M S ≃ Fin (vertexCount M S) := Fintype.equivFin _

noncomputable def edgeEquiv (M : FiniteMultiGraph) (S : Finset M.Vertex) :
    PortEdgeType M S ≃ Fin (edgeCount M S) := Fintype.equivFin _

private def edgeSrc (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (e : PortEdgeType M S) : PortVertexType M S :=
  match e with
  | .inl i => .inl (M.src i.1)
  | .inr (.inl (p, side)) => .inl (if side then M.dst p.1 else M.src p.1)
  | .inr (.inr (l, k)) =>
      if k = 0 then .inl (M.src l.1)
      else if k = 1 then .inr (.inr (l, 0))
      else .inr (.inr (l, 1))

private def edgeDst (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (e : PortEdgeType M S) : PortVertexType M S :=
  match e with
  | .inl i => .inl (M.dst i.1)
  | .inr (.inl (p, _)) => .inr (.inl p)
  | .inr (.inr (l, k)) =>
      if k = 0 then .inr (.inr (l, 0))
      else if k = 1 then .inr (.inr (l, 1))
      else .inl (M.dst l.1)

private theorem edgeTag_injective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {e f : PortEdgeType M S}
    (hpair : (edgeSrc M S e = edgeSrc M S f ∧ edgeDst M S e = edgeDst M S f) ∨
      (edgeSrc M S e = edgeDst M S f ∧ edgeDst M S e = edgeSrc M S f)) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have he : e.1 = f.1 := by
        apply hroot.2.2 e.1 f.1 e.2.1 e.2.2 f.2.1 f.2.2
        rcases hpair with h | h
        · exact Or.inl ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
        · exact Or.inr ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
      have he' : e = f := Subtype.ext he
      cases he'
      rfl
    | inr f =>
      cases f with
      | inl f =>
        cases f.2 <;> simp_all [edgeSrc, edgeDst]
      | inr f =>
        rcases f with ⟨l, k⟩
        fin_cases k <;> simp_all [edgeSrc, edgeDst]
  | inr e =>
    cases e with
    | inl e =>
      cases f with
      | inl f => cases e.2 <;> simp_all [edgeSrc, edgeDst]
      | inr f =>
        cases f with
        | inl f =>
          rcases hpair with h | h
          · have hm : e.1 = f.1 := by
              have hd : (Sum.inr (Sum.inl e.1) : PortVertexType M S) =
                  Sum.inr (Sum.inl f.1) := by
                simpa [edgeDst] using h.2
              exact Sum.inl.inj (Sum.inr.inj hd)
            have hb : e.2 = f.2 := by
              cases he : e.2 <;> cases hf : f.2
              · rfl
              · have hbad : M.src e.1.1 = M.dst e.1.1 := by
                  simpa [edgeSrc, he, hf, hm] using h.1
                exact (e.1.2.1 hbad).elim
              · have hbad : M.dst e.1.1 = M.src e.1.1 := by
                  simpa [edgeSrc, he, hf, hm] using h.1
                exact (e.1.2.1 hbad.symm).elim
              · rfl
            have he' : e = f := Prod.ext hm hb
            cases he'
            rfl
          · simp_all [edgeSrc, edgeDst]
        | inr f =>
          rcases f with ⟨l, k⟩
          cases e.2 <;> fin_cases k <;> simp_all [edgeSrc, edgeDst]
    | inr e =>
      cases f with
      | inl f =>
        rcases e with ⟨l, k⟩
        fin_cases k <;> simp_all [edgeSrc, edgeDst]
      | inr f =>
        cases f with
        | inl f =>
          rcases e with ⟨l, k⟩
          cases f.2 <;> fin_cases k <;> simp_all [edgeSrc, edgeDst]
        | inr f =>
          rcases e with ⟨l, k⟩
          rcases f with ⟨l', k'⟩
          fin_cases k <;> fin_cases k' <;> simp_all [edgeSrc, edgeDst]

private theorem edge_noLoop (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (e : PortEdgeType M S) :
    edgeSrc M S e ≠ edgeDst M S e := by
  cases e with
  | inl e =>
      intro h
      have hs : (Sum.inl (M.src e.1) : PortVertexType M S) = Sum.inl (M.dst e.1) := by
        simpa [edgeSrc, edgeDst] using h
      have hv : M.src e.1 = M.dst e.1 := Sum.inl.inj hs
      exact hroot.2.1 e.1 e.2.1 e.2.2 hv
  | inr e =>
      cases e with
      | inl e => simp [edgeSrc, edgeDst]
      | inr e =>
          rcases e with ⟨l, k⟩
          fin_cases k <;> simp [edgeSrc, edgeDst]

private def portSrc (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (i : Fin (edgeCount M S)) : Fin (vertexCount M S) :=
  vertexEquiv M S (edgeSrc M S ((edgeEquiv M S).symm i))

private def portDst (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (i : Fin (edgeCount M S)) : Fin (vertexCount M S) :=
  vertexEquiv M S (edgeDst M S ((edgeEquiv M S).symm i))

noncomputable def graph (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) : PhysicalGraph where
  vertexCount := vertexCount M S
  edgeCount := edgeCount M S
  src := portSrc M S
  dst := portDst M S
  noLoops := by
    intro i h
    have hv := (vertexEquiv M S).injective h
    exact edge_noLoop M S hroot ((edgeEquiv M S).symm i) hv
  simple := by
    intro i j hij
    let e := (edgeEquiv M S).symm i
    let f := (edgeEquiv M S).symm j
    have hp : (edgeSrc M S e = edgeSrc M S f ∧ edgeDst M S e = edgeDst M S f) ∨
        (edgeSrc M S e = edgeDst M S f ∧ edgeDst M S e = edgeSrc M S f) := by
      rcases hij with h | h
      · exact Or.inl ⟨(vertexEquiv M S).injective (by simpa [portSrc, e, f] using h.1),
          (vertexEquiv M S).injective (by simpa [portDst, e, f] using h.2)⟩
      · exact Or.inr ⟨(vertexEquiv M S).injective (by simpa [portSrc, portDst, e, f] using h.1),
          (vertexEquiv M S).injective (by simpa [portDst, portSrc, e, f] using h.2)⟩
    have hef := edgeTag_injective M S hroot hp
    have hdec : (edgeEquiv M S).symm i = (edgeEquiv M S).symm j := by simpa [e, f] using hef
    simpa using congrArg (edgeEquiv M S) hdec

def oldVertex (M : FiniteMultiGraph) (S : Finset M.Vertex) (v : M.Vertex) :
    Fin (vertexCount M S) := vertexEquiv M S (.inl v)

def portVertex (M : FiniteMultiGraph) (S : Finset M.Vertex) (e : PortEdge M S) :
    Fin (vertexCount M S) := vertexEquiv M S (.inr (.inl e))

def loopVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (e : ExteriorLoop M S) (i : Fin 2) : Fin (vertexCount M S) :=
  vertexEquiv M S (.inr (.inr (e, i)))

/-- Public endpoint formulas for the edge tags of the port expansion. These
allow external route constructions to use the typed tags without unfolding the
private endpoint implementation. -/
@[simp] theorem src_internalEdge (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (i : InternalEdge M S) :
    (graph M S hroot).src (edgeEquiv M S (.inl i)) = oldVertex M S (M.src i.1) := by
  simp [graph, portSrc, oldVertex, edgeSrc]

@[simp] theorem dst_internalEdge (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (i : InternalEdge M S) :
    (graph M S hroot).dst (edgeEquiv M S (.inl i)) = oldVertex M S (M.dst i.1) := by
  simp [graph, portDst, oldVertex, edgeDst]

@[simp] theorem src_portEdge_false (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (p : PortEdge M S) :
    (graph M S hroot).src (edgeEquiv M S (.inr (.inl (p, false)))) =
      oldVertex M S (M.src p.1) := by
  simp [graph, portSrc, oldVertex, edgeSrc]

@[simp] theorem src_portEdge_true (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (p : PortEdge M S) :
    (graph M S hroot).src (edgeEquiv M S (.inr (.inl (p, true)))) =
      oldVertex M S (M.dst p.1) := by
  simp [graph, portSrc, oldVertex, edgeSrc]

@[simp] theorem dst_portEdge (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (p : PortEdge M S) (b : Bool) :
    (graph M S hroot).dst (edgeEquiv M S (.inr (.inl (p, b)))) =
      portVertex M S p := by
  simp [graph, portDst, portVertex, edgeDst]

@[simp] theorem src_exteriorLoop_zero (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).src (edgeEquiv M S (.inr (.inr (l, 0)))) =
      oldVertex M S (M.src l.1) := by
  simp [graph, portSrc, oldVertex, edgeSrc]

@[simp] theorem src_exteriorLoop_one (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).src (edgeEquiv M S (.inr (.inr (l, 1)))) =
      loopVertex M S l 0 := by
  simp [graph, portSrc, loopVertex, edgeSrc]

@[simp] theorem src_exteriorLoop_two (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).src (edgeEquiv M S (.inr (.inr (l, 2)))) =
      loopVertex M S l 1 := by
  simp [graph, portSrc, loopVertex, edgeSrc]

@[simp] theorem dst_exteriorLoop_zero (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).dst (edgeEquiv M S (.inr (.inr (l, 0)))) =
      loopVertex M S l 0 := by
  simp [graph, portDst, loopVertex, edgeDst]

@[simp] theorem dst_exteriorLoop_one (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).dst (edgeEquiv M S (.inr (.inr (l, 1)))) =
      loopVertex M S l 1 := by
  simp [graph, portDst, loopVertex, edgeDst]

@[simp] theorem dst_exteriorLoop_two (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    (graph M S hroot).dst (edgeEquiv M S (.inr (.inr (l, 2)))) =
      oldVertex M S (M.dst l.1) := by
  simp [graph, portDst, oldVertex, edgeDst]

def rootRegion (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) : Finset (graph M S hroot).Vertex := by
  classical
  exact Finset.univ.filter fun v => ∃ u ∈ S, oldVertex M S u = v

private theorem oldVertex_injective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    {u v : M.Vertex} (h : oldVertex M S u = oldVertex M S v) : u = v := by
  have hv := (vertexEquiv M S).injective h
  exact Sum.inl.inj hv

theorem mem_rootRegion_oldVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (u : M.Vertex) :
    oldVertex M S u ∈ rootRegion M S hroot ↔ u ∈ S := by
  classical
  simp only [rootRegion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hvS, hv⟩
    exact (oldVertex_injective M S hv.symm) ▸ hvS
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem rootRegion_card_eq (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) : (rootRegion M S hroot).card = S.card := by
  classical
  symm
  apply Finset.card_bij (fun u _ => oldVertex M S u)
  · intro u hu
    exact (mem_rootRegion_oldVertex M S hroot u).2 hu
  · intro u hu v hv huv
    exact oldVertex_injective M S huv
  · intro v hv
    simp only [rootRegion, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simpa using hv





private theorem rootRegion_vertex_iff (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (v : PortVertexType M S) :
    vertexEquiv M S v ∈ rootRegion M S hroot ↔ ∃ u ∈ S, Sum.inl u = v := by
  classical
  simp only [rootRegion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, hu, (vertexEquiv M S).injective (by simpa [oldVertex] using hv)⟩
  · rintro ⟨u, hu, hv⟩
    subst v
    exact ⟨u, hu, rfl⟩

private def underlyingEdge (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (e : PortEdgeType M S) : M.Edge :=
  match e with
  | .inl i => i.1
  | .inr (.inl (p, _)) => p.1
  | .inr (.inr (l, _)) => l.1

private theorem edge_cut_iff (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) (e : PortEdgeType M S) :
    edgeEquiv M S e ∈ SafeCore.ownerCut (graph M S hroot) (rootRegion M S hroot) ↔
      match e with
      | .inl _ => False
      | .inr (.inl (p, side)) =>
          if side then M.dst p.1 ∈ S else M.src p.1 ∈ S
      | .inr (.inr _) => False := by
  rw [SafeCore.mem_ownerCut]
  simp only [graph, portSrc, portDst, Equiv.symm_apply_apply]
  rw [rootRegion_vertex_iff M S hroot (edgeSrc M S e),
    rootRegion_vertex_iff M S hroot (edgeDst M S e)]
  cases e with
  | inl i => simp [edgeSrc, edgeDst, i.2.1, i.2.2]
  | inr e =>
    cases e with
    | inl e =>
      by_cases hb : e.2 <;> simp [edgeSrc, edgeDst, hb]
    | inr e =>
      rcases e with ⟨l, k⟩
      have hdst : M.dst l.1 ∉ S := by rw [← l.2.1]; exact l.2.2
      fin_cases k <;> simp [edgeSrc, edgeDst, l.2.2, hdst]

private theorem physicalCut_implies_multicut (M : FiniteMultiGraph)
    (S : Finset M.Vertex) (hroot : IsCleanupRoot M S) (i : (graph M S hroot).Edge)
    (hi : i ∈ SafeCore.ownerCut (graph M S hroot) (rootRegion M S hroot)) :
    underlyingEdge M S ((edgeEquiv M S).symm i) ∈ cutEdges M S := by
  have hc : (edgeEquiv M S) ((edgeEquiv M S).symm i) ∈
      SafeCore.ownerCut (graph M S hroot) (rootRegion M S hroot) := by
    simpa only [Equiv.apply_symm_apply] using hi
  have hc' := (edge_cut_iff M S hroot ((edgeEquiv M S).symm i)).mp hc
  cases ht : (edgeEquiv M S).symm i with
  | inl e => simp [ht] at hc'
  | inr e =>
    cases e with
    | inl e =>
      rcases e with ⟨p, side⟩
      cases side with
      | false =>
        have hs : M.src p.1 ∈ S := by simpa [ht] using hc'
        rcases p.2 with ⟨hne, hnot⟩
        have hout : M.dst p.1 ∉ S := by
          intro hd
          exact hnot ⟨hs, hd⟩
        simp [cutEdges]
        exact Or.inl ⟨hs, hout⟩
      | true =>
        have hd : M.dst p.1 ∈ S := by simpa [ht] using hc'
        rcases p.2 with ⟨hne, hnot⟩
        have hout : M.src p.1 ∉ S := by
          intro hs
          exact hnot ⟨hs, hd⟩
        simp [cutEdges]
        exact Or.inr ⟨hout, hd⟩
    | inr e => simp [ht] at hc'

/-- The actual edge cut of the old-vertex root is in bijection with the
labelled auxiliary cut. Each crossing auxiliary edge contributes exactly its
single port half incident with the root. -/
theorem root_cut_card_eq (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) :
    SafeCore.cutSize (graph M S hroot) (rootRegion M S hroot) =
      (cutEdges M S).card := by
  classical
  unfold SafeCore.cutSize
  apply Finset.card_bij (fun i _ => underlyingEdge M S ((edgeEquiv M S).symm i))
  · intro i hi
    exact physicalCut_implies_multicut M S hroot i hi
  · intro i hi j hj he
    have hci := (edge_cut_iff M S hroot ((edgeEquiv M S).symm i)).mp (by
      simpa only [Equiv.apply_symm_apply] using hi)
    have hcj := (edge_cut_iff M S hroot ((edgeEquiv M S).symm j)).mp (by
      simpa only [Equiv.apply_symm_apply] using hj)
    cases ti : (edgeEquiv M S).symm i with
    | inl a => simp [ti] at hci
    | inr a =>
      cases a with
      | inl a =>
        rcases a with ⟨p, sp⟩
        cases tj : (edgeEquiv M S).symm j with
        | inl b => simp [tj] at hcj
        | inr b =>
          cases b with
          | inl b =>
            rcases b with ⟨q, sq⟩
            have hval : p.1 = q.1 := by
              simpa [underlyingEdge, ti, tj] using he
            have hpq : p = q := Subtype.ext hval
            have hside : sp = sq := by
              cases sp <;> cases sq
              · rfl
              · have hsrc : M.src p.1 ∈ S := by simpa [ti] using hci
                have hdst : M.dst p.1 ∈ S := by simpa [tj, hpq] using hcj
                exact False.elim (p.2.2 ⟨hsrc, hdst⟩)
              · have hdst : M.dst p.1 ∈ S := by simpa [ti] using hci
                have hsrc : M.src p.1 ∈ S := by simpa [tj, hpq] using hcj
                exact False.elim (p.2.2 ⟨hsrc, hdst⟩)
              · rfl
            have htag : (edgeEquiv M S).symm i = (edgeEquiv M S).symm j := by
              rw [ti, tj]
              simp [hpq, hside]
            simpa using congrArg (edgeEquiv M S) htag
          | inr b => simp [tj] at hcj
      | inr a => simp [ti] at hci
  · intro e he
    rcases (Finset.mem_filter.mp he).2 with h | h
    · have hne : M.src e ≠ M.dst e := by
        intro hEq
        exact h.2 (hEq ▸ h.1)
      have hnot : ¬ (M.src e ∈ S ∧ M.dst e ∈ S) := by
        intro hboth
        exact h.2 hboth.2
      let p : PortEdge M S := ⟨e, hne, hnot⟩
      let t : PortEdgeType M S := .inr (.inl (p, false))
      refine ⟨edgeEquiv M S t, ?_, ?_⟩
      · apply (edge_cut_iff M S hroot t).2
        simpa [t] using h.1
      · simp [underlyingEdge, t]
        change e = e
        rfl
    · have hne : M.src e ≠ M.dst e := by
        intro hEq
        exact h.1 (hEq ▸ h.2)
      have hnot : ¬ (M.src e ∈ S ∧ M.dst e ∈ S) := by
        intro hboth
        exact h.1 hboth.1
      let p : PortEdge M S := ⟨e, hne, hnot⟩
      let t : PortEdgeType M S := .inr (.inl (p, true))
      refine ⟨edgeEquiv M S t, ?_, ?_⟩
      · apply (edge_cut_iff M S hroot t).2
        simpa [t] using h.2
      · simp [underlyingEdge, t]
        change e = e
        rfl

theorem physical_actualCut_rootRegion_eq (M : FiniteMultiGraph)
    (S : Finset M.Vertex) (hroot : IsCleanupRoot M S) :
    (graph M S hroot).actualCut (rootRegion M S hroot) =
      (cutEdges M S).card := by
  calc
    (graph M S hroot).actualCut (rootRegion M S hroot) =
        SafeCore.cutSize (graph M S hroot) (rootRegion M S hroot) := by
      unfold PhysicalGraph.actualCut SafeCore.cutSize
      congr 1
      ext e
      simp [PhysicalGraph.cutEdges, SafeCore.ownerCut, SafeCore.crossing]
    _ = (cutEdges M S).card := root_cut_card_eq M S hroot

/-- Every adjacency of the original induced root is represented by the direct
internal-edge tag in the port expansion. -/
theorem old_adjacency_lifts (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {u v : M.Vertex}
    (hu : u ∈ S) (hv : v ∈ S) (hadj : M.toSimpleGraph.Adj u v) :
    (graph M S hroot).toSimpleGraph.Adj (oldVertex M S u) (oldVertex M S v) := by
  rcases hadj with ⟨hne, e, hendpoints⟩
  have hinternal : M.src e ∈ S ∧ M.dst e ∈ S := by
    rcases hendpoints with h | h
    · exact ⟨h.1 ▸ hu, h.2 ▸ hv⟩
    · exact ⟨h.1 ▸ hv, h.2 ▸ hu⟩
  let ie : InternalEdge M S := ⟨e, hinternal⟩
  let i := edgeEquiv M S (.inl ie)
  have hsrc : (graph M S hroot).src i = oldVertex M S (M.src e) := by
    simp [graph, portSrc, i, oldVertex, edgeSrc, ie]
  have hdst : (graph M S hroot).dst i = oldVertex M S (M.dst e) := by
    simp [graph, portDst, i, oldVertex, edgeDst, ie]
  rcases hendpoints with h | h
  · refine ⟨i, one_ne_zero, Or.inl ?_⟩
    exact ⟨hsrc.trans (congrArg (oldVertex M S) h.1),
      hdst.trans (congrArg (oldVertex M S) h.2)⟩
  · refine ⟨i, one_ne_zero, Or.inr ?_⟩
    exact ⟨hsrc.trans (congrArg (oldVertex M S) h.1),
      hdst.trans (congrArg (oldVertex M S) h.2)⟩

/-- Connectedness of the original induced root transfers to the old-vertex
induced subgraph of the root-preserving port expansion. -/
theorem rootRegion_induce_connected (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) :
    ((graph M S hroot).toSimpleGraph.induce
      (↑(rootRegion M S hroot) : Set (graph M S hroot).Vertex)).Connected := by
  let H := M.toSimpleGraph.induce (↑S : Set M.Vertex)
  let K := (graph M S hroot).toSimpleGraph.induce
    (↑(rootRegion M S hroot) : Set (graph M S hroot).Vertex)
  let f : H →g K := {
    toFun := fun u => ⟨oldVertex M S u.1,
      (mem_rootRegion_oldVertex M S hroot u.1).2 u.2⟩
    map_rel' := by
      intro u v hadj
      exact old_adjacency_lifts M S hroot u.2 v.2 hadj
  }
  letI : Nonempty {x : (graph M S hroot).Vertex // x ∈ (↑(rootRegion M S hroot) : Set (graph M S hroot).Vertex)} :=
    (hroot.1).nonempty.map f
  refine ⟨?_⟩
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  have ha' : ∃ u ∈ S, oldVertex M S u = a := by
    simpa [rootRegion] using ha
  have hb' : ∃ v ∈ S, oldVertex M S v = b := by
    simpa [rootRegion] using hb
  obtain ⟨u, hu, hau⟩ := ha'
  obtain ⟨v, hv, hbv⟩ := hb'
  let u' : {x : M.Vertex // x ∈ S} := ⟨u, hu⟩
  let v' : {x : M.Vertex // x ∈ S} := ⟨v, hv⟩
  obtain ⟨p⟩ := hroot.1 u' v'
  have hfa : f u' = ⟨a, ha⟩ := by
    apply Subtype.ext
    exact hau
  have hfb : f v' = ⟨b, hb⟩ := by
    apply Subtype.ext
    exact hbv
  change K.Reachable ⟨a, ha⟩ ⟨b, hb⟩
  rw [← hfa, ← hfb]
  exact (p.map f).reachable


end Erdos1016.Proof.PortExpansion

namespace Erdos1016.Proof.CleanupSpecification.CleanupOutput

open Erdos1016.Proof.PortExpansion

variable {G : PhysicalGraph} {I : CleanupInput G}











end Erdos1016.Proof.CleanupSpecification.CleanupOutput
end

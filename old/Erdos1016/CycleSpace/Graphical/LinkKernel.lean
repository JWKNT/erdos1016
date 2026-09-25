import Erdos1016.CycleSpace.Graphical.ComponentCutParity
import Erdos1016.CycleSpace.Graphical.LinkPairWitnesses

set_option autoImplicit false
set_option maxHeartbeats 80000

/-!
# Kernel decomposition for the two-vertex link map

The forward inclusion is already available in `GraphicalLinkMap`. The reverse
inclusion reduces to a local construction inside each component of the graph
after deleting the two marked vertices: pair an even set of selected
attachments at the first marked vertex with paths inside that component.
This file currently isolates and verifies the path-word part of that
construction.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalLinkKernelDecomposition

open Erdos1016
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalCommonInformation

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private def vertexUnit (G : PhysicalGraph) (v : G.Vertex) : G.Demand :=
  fun z => if z = v then 1 else 0

private def edgeUnit (G : PhysicalGraph) (e : G.Edge) : G.Word :=
  fun f => if f = e then 1 else 0

private theorem double_zero (a : F₂) : a + a = 0 := by
  have htwo : (2 : F₂) = 0 := ZMod.natCast_self 2
  calc
    a + a = (2 : F₂) * a := by ring
    _ = 0 := by rw [htwo]; simp

private theorem boundary_edgeUnit (G : PhysicalGraph) (e : G.Edge) :
    G.boundary (edgeUnit G e) =
      vertexUnit G (G.src e) + vertexUnit G (G.dst e) := by
  classical
  ext v
  change (∑ f, ((if G.src f = v then edgeUnit G e f else 0) +
    (if G.dst f = v then edgeUnit G e f else 0))) = _
  rw [Finset.sum_add_distrib]
  have hs : (∑ f, if G.src f = v then edgeUnit G e f else 0) =
      if G.src e = v then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp [edgeUnit]
    · intro f _ hfe
      simp [edgeUnit, hfe]
    · simp
  have hd : (∑ f, if G.dst f = v then edgeUnit G e f else 0) =
      if G.dst e = v then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp [edgeUnit]
    · intro f _ hfe
      simp [edgeUnit, hfe]
    · simp
  rw [hs, hd]
  simp [vertexUnit, eq_comm]

private noncomputable def physicalEdgeOfAdj (G : PhysicalGraph) {a b : G.Vertex}
    (h : G.toSimpleGraph.Adj a b) : G.Edge :=
  Classical.choose (by
    simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h)

private theorem physicalEdgeOfAdj_spec (G : PhysicalGraph) {a b : G.Vertex}
    (h : G.toSimpleGraph.Adj a b) :
    (G.src (physicalEdgeOfAdj G h) = a ∧ G.dst (physicalEdgeOfAdj G h) = b) ∨
      (G.src (physicalEdgeOfAdj G h) = b ∧ G.dst (physicalEdgeOfAdj G h) = a) := by
  have hs := Classical.choose_spec (by
    simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h)
  simpa [physicalEdgeOfAdj] using hs

private noncomputable def deletedEdgeOfAdj (G : PhysicalGraph) (u v : G.Vertex)
    {a b : DeletedVertex G u v} (h : (deletedGraph G u v).Adj a b) : G.Edge :=
  physicalEdgeOfAdj G (show G.toSimpleGraph.Adj a.1 b.1 from h)

private theorem deletedEdgeOfAdj_spec (G : PhysicalGraph) (u v : G.Vertex)
    {a b : DeletedVertex G u v} (h : (deletedGraph G u v).Adj a b) :
    (G.src (deletedEdgeOfAdj G u v h) = a.1 ∧
      G.dst (deletedEdgeOfAdj G u v h) = b.1) ∨
    (G.src (deletedEdgeOfAdj G u v h) = b.1 ∧
      G.dst (deletedEdgeOfAdj G u v h) = a.1) :=
  physicalEdgeOfAdj_spec G (show G.toSimpleGraph.Adj a.1 b.1 from h)

private def deletedWalkWord (G : PhysicalGraph) (u v : G.Vertex) :
    {a b : DeletedVertex G u v} →
      (deletedGraph G u v).Walk a b → G.Word
  | _, _, .nil => 0
  | _, _, .cons h p =>
      edgeUnit G (deletedEdgeOfAdj G u v h) + deletedWalkWord G u v p

private theorem deletedWalkWord_boundary (G : PhysicalGraph) (u v : G.Vertex)
    {a b : DeletedVertex G u v} (p : (deletedGraph G u v).Walk a b) :
    G.boundary (deletedWalkWord G u v p) = vertexUnit G a.1 + vertexUnit G b.1 := by
  induction p with
  | nil =>
      simp [deletedWalkWord]
      ext z
      by_cases hz : z = a.1 <;> simp [vertexUnit, hz, double_zero]
  | @cons a b c hab p ih =>
      change G.boundary
          (edgeUnit G (deletedEdgeOfAdj G u v hab) + deletedWalkWord G u v p) = _
      rw [map_add, boundary_edgeUnit, ih]
      have hedge := deletedEdgeOfAdj_spec G u v hab
      rcases hedge with h | h
      · rw [h.1, h.2]
        ext z
        by_cases hz : z = b.1
        · subst z
          have hba : b.1 ≠ a.1 := by
            intro h
            exact hab.ne (Subtype.ext h.symm)
          dsimp [vertexUnit]
          simp only [if_neg hba, if_pos]
          simp only [zero_add, add_zero]
          rw [← add_assoc, double_zero 1, zero_add]
        · simp [vertexUnit, hz]
      · rw [h.1, h.2]
        ext z
        by_cases hz : z = b.1
        · subst z
          have hba : b.1 ≠ a.1 := by
            intro h
            exact hab.ne (Subtype.ext h.symm)
          dsimp [vertexUnit]
          simp only [if_neg hba, if_pos]
          simp only [zero_add, add_zero]
          rw [← add_assoc, double_zero 1, zero_add]
        · simp [vertexUnit, hz]

/-- A path inside the two-vertex-deleted graph uses no edge incident to either
marked endpoint. -/
private theorem deletedWalkWord_zero_of_incident (G : PhysicalGraph)
    (u v : G.Vertex) {a b : DeletedVertex G u v}
    (p : (deletedGraph G u v).Walk a b) (m : G.Vertex)
    (hm : m = u ∨ m = v) (e : G.Edge) (he : G.incident e m) :
    deletedWalkWord G u v p e = 0 := by
  induction p with
  | nil => simp [deletedWalkWord]
  | @cons a b c hab p ih =>
      simp only [deletedWalkWord]
      have hed := deletedEdgeOfAdj_spec G u v hab
      have hunit : edgeUnit G (deletedEdgeOfAdj G u v hab) e = 0 := by
        rcases hed with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · have hnot : ¬ G.incident (deletedEdgeOfAdj G u v hab) m := by
            intro hi
            rcases hi with hi | hi
            · have haNot : a.1 ≠ m := by
                rcases hm with hmu | hmv
                · simpa [hmu] using a.2.1
                · simpa [hmv] using a.2.2
              exact haNot (hs.symm.trans hi)
            · have hbNot : b.1 ≠ m := by
                rcases hm with hmu | hmv
                · simpa [hmu] using b.2.1
                · simpa [hmv] using b.2.2
              exact hbNot (ht.symm.trans hi)
          have heq : e ≠ deletedEdgeOfAdj G u v hab := by
            intro heq
            subst e
            exact hnot he
          simp [edgeUnit, heq]
        · have hnot : ¬ G.incident (deletedEdgeOfAdj G u v hab) m := by
            intro hi
            rcases hi with hi | hi
            · have hbNot : b.1 ≠ m := by
                rcases hm with hmu | hmv
                · simpa [hmu] using b.2.1
                · simpa [hmv] using b.2.2
              exact hbNot (hs.symm.trans hi)
            · have haNot : a.1 ≠ m := by
                rcases hm with hmu | hmv
                · simpa [hmu] using a.2.1
                · simpa [hmv] using a.2.2
              exact haNot (ht.symm.trans hi)
          have heq : e ≠ deletedEdgeOfAdj G u v hab := by
            intro heq
            subst e
            exact hnot he
          simp [edgeUnit, heq]
      change edgeUnit G (deletedEdgeOfAdj G u v hab) e +
        deletedWalkWord G u v p e = 0
      rw [hunit, ih]
      simp

private theorem edgeUnit_zero_of_not_incident (G : PhysicalGraph)
    (e f : G.Edge) (v : G.Vertex) (h : ¬ G.incident e v)
    (hf : G.incident f v) : edgeUnit G e f = 0 := by
  have hne : f ≠ e := by
    intro hfe
    subst f
    exact h hf
  simp [edgeUnit, hne]

private theorem physicalEdge_adj (G : PhysicalGraph) (e : G.Edge) :
    G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
  change ∃ f, (fun _ : G.Edge => (1 : F₂)) f ≠ 0 ∧
    ((G.src f = G.src e ∧ G.dst f = G.dst e) ∨
      (G.src f = G.dst e ∧ G.dst f = G.src e))
  exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

/-- An edge incident to `u` and not incident to `v` has its other endpoint in
exactly one component of the `{u,v}`-deleted graph. -/
private theorem existsUnique_cutComponent_of_incident_other (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (f : G.Edge)
    (hf : G.incident f u) (hfv : ¬ G.incident f v) :
    ∃! c : (deletedGraph G u v).ConnectedComponent,
      componentCutCondition G u v c f := by
  have hloop : G.src f ≠ G.dst f := (physicalEdge_adj G f).ne
  rcases hf with hsrc | hdst
  · have hdU : G.dst f ≠ u := by
      intro h
      exact hloop (hsrc.trans h.symm)
    have hdV : G.dst f ≠ v := by
      intro h
      exact hfv (Or.inr h)
    let a : DeletedVertex G u v := ⟨G.dst f, ⟨hdU, hdV⟩⟩
    let c₀ := (deletedGraph G u v).connectedComponentMk a
    have hc₀ : componentCutCondition G u v c₀ f := by
      change (G.src f = u ∧ G.dst f ∈ componentVertices G u v c₀) ∨ _
      left
      refine ⟨hsrc, ?_⟩
      simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.2,
        congrArg (deletedGraph G u v).connectedComponentMk (Subtype.ext rfl)⟩
    refine ⟨c₀, hc₀, ?_⟩
    intro c hc
    change (G.src f = u ∧ G.dst f ∈ componentVertices G u v c) ∨
      (G.dst f = u ∧ G.src f ∈ componentVertices G u v c) at hc
    rcases hc with ⟨_, hmem⟩ | ⟨hd, _⟩
    · obtain ⟨ha, hcomp⟩ := componentVertices_spec G u v c hmem
      have hcomp₀ : (deletedGraph G u v).connectedComponentMk
          ⟨G.dst f, ha⟩ = c₀ := by
        dsimp [c₀]
      exact hcomp.symm.trans hcomp₀
    · exact (hloop (hsrc.trans hd.symm)).elim
  · have hsU : G.src f ≠ u := by
      intro h
      exact hloop (h.trans hdst.symm)
    have hsV : G.src f ≠ v := by
      intro h
      exact hfv (Or.inl h)
    let a : DeletedVertex G u v := ⟨G.src f, ⟨hsU, hsV⟩⟩
    let c₀ := (deletedGraph G u v).connectedComponentMk a
    have hc₀ : componentCutCondition G u v c₀ f := by
      change (G.src f = u ∧ G.dst f ∈ componentVertices G u v c₀) ∨ _
      right
      refine ⟨hdst, ?_⟩
      simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.2,
        congrArg (deletedGraph G u v).connectedComponentMk (Subtype.ext rfl)⟩
    refine ⟨c₀, hc₀, ?_⟩
    intro c hc
    change (G.src f = u ∧ G.dst f ∈ componentVertices G u v c) ∨
      (G.dst f = u ∧ G.src f ∈ componentVertices G u v c) at hc
    rcases hc with ⟨hs, _⟩ | ⟨_, hmem⟩
    · exact (hloop (hs.trans hdst.symm)).elim
    · obtain ⟨ha, hcomp⟩ := componentVertices_spec G u v c hmem
      have hcomp₀ : (deletedGraph G u v).connectedComponentMk
          ⟨G.src f, ha⟩ = c₀ := by
        dsimp [c₀]
      exact hcomp.symm.trans hcomp₀

private theorem attachmentEdge_not_incident_other (G : PhysicalGraph)
    (u v : G.Vertex) {e : G.Edge} {a : DeletedVertex G u v}
    (he : (G.src e = u ∧ G.dst e = a.1) ∨
      (G.dst e = u ∧ G.src e = a.1)) (hne : u ≠ v) :
    ¬ G.incident e v := by
  intro hi
  rcases he with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · rcases hi with hi | hi
    · exact hne (hs.symm.trans hi)
    · exact a.2.2 (ht.symm.trans hi)
  · rcases hi with hi | hi
    · exact a.2.2 (hs.symm.trans hi)
    · exact hne (ht.symm.trans hi)

/-- A cut edge at `u` into a deleted component carries its endpoint as a
vertex of that component. -/
private theorem componentCut_attachmentData (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (he : componentCutCondition G u v c e) :
    ∃ a : DeletedVertex G u v,
      ((G.src e = u ∧ G.dst e = a.1) ∨ (G.dst e = u ∧ G.src e = a.1)) ∧
        (deletedGraph G u v).connectedComponentMk a = c := by
  rcases he with ⟨hs, hd⟩ | ⟨ht, hs⟩
  · obtain ⟨ha, hcomp⟩ := componentVertices_spec G u v c hd
    exact ⟨⟨G.dst e, ha⟩, Or.inl ⟨hs, rfl⟩, hcomp⟩
  · obtain ⟨ha, hcomp⟩ := componentVertices_spec G u v c hs
    exact ⟨⟨G.src e, ha⟩, Or.inr ⟨ht, rfl⟩, hcomp⟩

/-- Any two attachment endpoints into one deleted component are joined by a
walk using only vertices outside the two marked vertices. -/
private theorem attachment_endpoints_connected (G : PhysicalGraph)
    (u v : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent)
    {e e₀ : G.Edge}
    (he : componentCutCondition G u v c e)
    (he₀ : componentCutCondition G u v c e₀) :
    ∃ a r : DeletedVertex G u v,
      Nonempty ((deletedGraph G u v).Walk a r) ∧
        ((G.src e = u ∧ G.dst e = a.1) ∨ (G.dst e = u ∧ G.src e = a.1)) ∧
        ((G.src e₀ = u ∧ G.dst e₀ = r.1) ∨ (G.dst e₀ = u ∧ G.src e₀ = r.1)) := by
  obtain ⟨a, ha, hac⟩ := componentCut_attachmentData G u v c e he
  obtain ⟨r, hr, hrc⟩ := componentCut_attachmentData G u v c e₀ he₀
  have hreach : (deletedGraph G u v).Reachable a r :=
    SimpleGraph.ConnectedComponent.exact (hac.trans hrc.symm)
  rcases hreach with ⟨p⟩
  exact ⟨a, r, ⟨p⟩, ha, hr⟩

private noncomputable def attachmentEndpointsData (G : PhysicalGraph)
    (u v : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent)
    {e e₀ : G.Edge} (he : componentCutCondition G u v c e)
    (he₀ : componentCutCondition G u v c e₀) :
    Σ a : DeletedVertex G u v, Σ r : DeletedVertex G u v,
      (deletedGraph G u v).Walk a r × PLift
        (((G.src e = u ∧ G.dst e = a.1) ∨ (G.dst e = u ∧ G.src e = a.1)) ∧
        ((G.src e₀ = u ∧ G.dst e₀ = r.1) ∨ (G.dst e₀ = u ∧ G.src e₀ = r.1))) := by
  classical
  have h := attachment_endpoints_connected G u v c he he₀
  let a := Classical.choose h
  have h₁ : ∃ r, Nonempty ((deletedGraph G u v).Walk a r) ∧
      ((G.src e = u ∧ G.dst e = a.1) ∨ (G.dst e = u ∧ G.src e = a.1)) ∧
      ((G.src e₀ = u ∧ G.dst e₀ = r.1) ∨ (G.dst e₀ = u ∧ G.src e₀ = r.1)) :=
    Classical.choose_spec h
  let r := Classical.choose h₁
  have h₂ := Classical.choose_spec h₁
  exact ⟨a, r, Classical.choice h₂.1, ⟨h₂.2.1, h₂.2.2⟩⟩

/-- The closed word made from two attachments at `u` and a walk within the
deleted component is a cycle avoiding `v`. -/
private theorem attachment_connector_mem_avoiding (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v)
    {e e₀ : G.Edge} {a r : DeletedVertex G u v}
    (he : (G.src e = u ∧ G.dst e = a.1) ∨
      (G.dst e = u ∧ G.src e = a.1))
    (he₀ : (G.src e₀ = u ∧ G.dst e₀ = r.1) ∨
      (G.dst e₀ = u ∧ G.src e₀ = r.1))
    (p : (deletedGraph G u v).Walk a r) :
    edgeUnit G e + deletedWalkWord G u v p + edgeUnit G e₀ ∈
      G.CycleSpace ∧
      ∃ hcycle : edgeUnit G e + deletedWalkWord G u v p + edgeUnit G e₀ ∈
        G.CycleSpace,
        (⟨edgeUnit G e + deletedWalkWord G u v p + edgeUnit G e₀,
          hcycle⟩ : G.CycleSpace) ∈ cyclesAvoidingVertex G v := by
  let W := edgeUnit G e + deletedWalkWord G u v p + edgeUnit G e₀
  have hbe : G.boundary (edgeUnit G e) = vertexUnit G u + vertexUnit G a.1 := by
    rw [boundary_edgeUnit]
    rcases he with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> rw [hs, ht] <;> abel
  have hbe₀ : G.boundary (edgeUnit G e₀) = vertexUnit G u + vertexUnit G r.1 := by
    rw [boundary_edgeUnit]
    rcases he₀ with ⟨hs, ht⟩ | ⟨ht, hs⟩ <;> rw [hs, ht] <;> abel
  have hcycle : W ∈ G.CycleSpace := by
    change G.boundary W = 0
    dsimp [W]
    rw [map_add, map_add, hbe, deletedWalkWord_boundary, hbe₀]
    ext z
    change (vertexUnit G u z + vertexUnit G a.1 z) +
        (vertexUnit G a.1 z + vertexUnit G r.1 z) +
        (vertexUnit G u z + vertexUnit G r.1 z) = 0
    ring_nf
    have htwo : (2 : F₂) = 0 := ZMod.natCast_self 2
    simp [htwo]
  have havoids : (⟨W, hcycle⟩ : G.CycleSpace) ∈ cyclesAvoidingVertex G v := by
    change vertexStarRestriction G v ⟨W, hcycle⟩ = 0
    ext f
    change W f.1 = 0
    dsimp [W]
    have hfirst := edgeUnit_zero_of_not_incident G e f.1 v
      (attachmentEdge_not_incident_other G u v he hne) f.2
    have hlast := edgeUnit_zero_of_not_incident G e₀ f.1 v
      (attachmentEdge_not_incident_other G u v he₀ hne) f.2
    rw [hfirst, deletedWalkWord_zero_of_incident G u v p v (Or.inr rfl) f.1 f.2,
      hlast]
    simp
  exact ⟨hcycle, ⟨hcycle, havoids⟩⟩

/-- Edges selected by a cycle that attach `u` to one fixed component of the
two-vertex deletion. -/
def SelectedComponentAttachments (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) (c : (deletedGraph G u v).ConnectedComponent) :=
  {e : G.Edge // componentCutCondition G u v c e ∧ x.1 e = 1}

noncomputable instance selectedComponentAttachmentsFintype (G : PhysicalGraph)
    (u v : G.Vertex) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent) :
    Fintype (SelectedComponentAttachments G u v x c) := by
  letI : Finite G.Edge := inferInstance
  letI : Finite (SelectedComponentAttachments G u v x c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private theorem componentCutCondition_iff_componentCutAt (G : PhysicalGraph)
    (u v : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge) :
    componentCutCondition G u v c e ↔
      Erdos1016.Proof.GraphicalComponentCutParity.componentCutAt G u v c u e := Iff.rfl

/-- The number of selected attachment edges, viewed in `F₂`, is exactly the
component cut parity. -/
theorem selectedAttachments_sum_eq_cutParity (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) (c : (deletedGraph G u v).ConnectedComponent) :
    (∑ e : SelectedComponentAttachments G u v x c, (1 : F₂)) =
      Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity
        G u v c u x.1 := by
  classical
  let A := SelectedComponentAttachments G u v x c
  let S : Finset G.Edge := Finset.univ.filter fun e =>
    componentCutCondition G u v c e ∧ x.1 e = 1
  let E : SelectedComponentAttachments G u v x c ≃ {e : G.Edge // e ∈ S} := {
    toFun := fun e => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
    invFun := fun e => ⟨e.1, (Finset.mem_filter.mp e.2).2⟩
    left_inv := by intro e; exact Subtype.ext rfl
    right_inv := by intro e; exact Subtype.ext rfl }
  have hcard : Fintype.card A = S.card := by
    calc
      Fintype.card A = Fintype.card {e : G.Edge // e ∈ S} := Fintype.card_congr E
      _ = S.card := Fintype.card_coe S
  have hcount : (∑ e : A, (1 : F₂)) = (S.card : F₂) := by
    calc
      (∑ e : A, (1 : F₂)) = (Fintype.card A : F₂) := by
        have hc := congrArg (fun n : ℕ => (n : F₂))
          (Fintype.card_eq_sum_ones (α := A))
        simpa using hc.symm
      _ = (S.card : F₂) := by rw [hcard]
  have hcut :
      Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity
          G u v c u x.1 = (S.card : F₂) := by
    unfold Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity
    have hcutEq (e : G.Edge) :
        componentCutCondition G u v c e ↔
          Erdos1016.Proof.GraphicalComponentCutParity.componentCutAt G u v c u e := Iff.rfl
    calc
      (∑ e : G.Edge,
          if Erdos1016.Proof.GraphicalComponentCutParity.componentCutAt
            G u v c u e then x.1 e else 0) =
        ∑ e : G.Edge, if e ∈ S then (1 : F₂) else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          by_cases hc : componentCutCondition G u v c e
          · have hc' := hcutEq e |>.mp hc
            by_cases hx : x.1 e = 1
            · rw [if_pos hc']
              simp [S, hc, hx]
            · have hx0 : x.1 e = 0 := by
                have binary (a : F₂) : a = 0 ∨ a = 1 := by
                  fin_cases a <;> simp
                rcases binary (x.1 e) with h0 | h1
                · exact h0
                · exact (hx h1).elim
              rw [if_pos hc']
              simp [S, hc, hx, hx0]
          · have hc' : ¬ Erdos1016.Proof.GraphicalComponentCutParity.componentCutAt
                G u v c u e := fun hp => hc ((hcutEq e).mpr hp)
            rw [if_neg hc']
            simp [S, hc]
      _ = S.card := by
        rw [Finset.sum_ite_mem Finset.univ S]
        simp only [Finset.univ_inter]
        have hs := congrArg (fun n : ℕ => (n : F₂)) (Finset.card_eq_sum_ones S)
        simpa using hs.symm
  exact hcount.trans hcut.symm

/-- A cycle in the link-map kernel has an even selected attachment family in
each component: either the component has no `v` attachment and cycle cut
parity forces this, or it is a link coordinate and the kernel forces it. -/
theorem selectedAttachments_even_of_linkMap_eq_zero (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (hx : GraphicalLinkMap.linkMap G u v x = 0)
    (c : (deletedGraph G u v).ConnectedComponent) :
    Even (Fintype.card (SelectedComponentAttachments G u v x c)) := by
  classical
  let A := SelectedComponentAttachments G u v x c
  by_cases hA : Nonempty A
  · let root : A := Classical.choice hA
    obtain ⟨a, ha, hcomp⟩ := componentCut_attachmentData G u v c root.1 root.2.1
    have hu : Erdos1016.Proof.GraphicalComponentCutParity.componentAttachedAt
        G u v u c := ⟨root.1, a, ha, hcomp⟩
    by_cases hv : Erdos1016.Proof.GraphicalComponentCutParity.componentAttachedAt
        G u v v c
    · let d : ComponentLink G u v := ⟨c, by
        change Erdos1016.Proof.GraphicalComponentCutParity.componentAttachedAt
            G u v u c ∧
          Erdos1016.Proof.GraphicalComponentCutParity.componentAttachedAt
            G u v v c
        exact ⟨hu, hv⟩⟩
      have hcoord := congrArg (fun y : LinkIndex G u v → F₂ => y (Sum.inr d)) hx
      have hparity :
          Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity
            G u v c u x.1 = 0 := by
        change GraphicalLinkMap.linkCoordinate G u v x (Sum.inr d) = 0 at hcoord
        simpa [GraphicalLinkMap.linkCoordinate,
          Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity,
          componentCutCondition_iff_componentCutAt] using hcoord
      have hsum : (∑ e : A, (1 : F₂)) = 0 := by
        rw [selectedAttachments_sum_eq_cutParity]
        exact hparity
      have hcast : (Fintype.card A : F₂) = ∑ e : A, (1 : F₂) := by
        have h := congrArg (fun n : ℕ => (n : F₂))
          (Fintype.card_eq_sum_ones (α := A))
        simpa using h
      have hcard : (Fintype.card A : F₂) = 0 := hcast.trans hsum
      exact (ZMod.eq_zero_iff_even).mp hcard
    · have hparity :
          Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity
            G u v c u x.1 = 0 :=
        Erdos1016.Proof.GraphicalComponentCutParity.componentCutParity_zero_of_no_v_attachment
          G u v hne c x hv
      have hsum : (∑ e : A, (1 : F₂)) = 0 := by
        rw [selectedAttachments_sum_eq_cutParity]
        exact hparity
      have hcast : (Fintype.card A : F₂) = ∑ e : A, (1 : F₂) := by
        have h := congrArg (fun n : ℕ => (n : F₂))
          (Fintype.card_eq_sum_ones (α := A))
        simpa using h
      have hcard : (Fintype.card A : F₂) = 0 := hcast.trans hsum
      exact (ZMod.eq_zero_iff_even).mp hcard
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    have hzero : Fintype.card A = 0 := Fintype.card_eq_zero
    simpa [hzero]

/-- Choose a fixed root attachment in a nonempty component-attachment family
and connect every other attachment to it inside the deleted component. -/
noncomputable def attachmentConnectorWord (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) (c : (deletedGraph G u v).ConnectedComponent)
    (e e₀ : SelectedComponentAttachments G u v x c) : G.Word := by
  classical
  let d := attachmentEndpointsData G u v c e.2.1 e₀.2.1
  exact edgeUnit G e.1 + deletedWalkWord G u v d.2.2.1 + edgeUnit G e₀.1

/-- At the first marked vertex, a connector has precisely its two
attachment-edge coordinates: its interior walk avoids both marked vertices. -/
theorem attachmentConnectorWord_starCoordinate (G : PhysicalGraph)
    (u v : G.Vertex) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent)
    (e e₀ : SelectedComponentAttachments G u v x c)
    (f : G.Edge) (hf : G.incident f u) :
    attachmentConnectorWord G u v x c e e₀ f =
      (if f = e.1 then 1 else 0) + (if f = e₀.1 then 1 else 0) := by
  classical
  let d := attachmentEndpointsData G u v c e.2.1 e₀.2.1
  change (edgeUnit G e.1 + deletedWalkWord G u v d.2.2.1 +
    edgeUnit G e₀.1) f = _
  have hw : deletedWalkWord G u v d.2.2.1 f = 0 :=
    deletedWalkWord_zero_of_incident G u v d.2.2.1 u (Or.inl rfl) f hf
  simp only [Pi.add_apply, hw]
  simp [edgeUnit]

/-- Summing root connectors over an even attachment family leaves exactly
the incidence word of the family at `u`. -/
theorem attachmentConnectorSum_starCoordinate (G : PhysicalGraph)
    (u v : G.Vertex) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent)
    (root : SelectedComponentAttachments G u v x c)
    (f : G.Edge) (hf : G.incident f u)
    (heven : Even (Fintype.card (SelectedComponentAttachments G u v x c))) :
    (∑ e : SelectedComponentAttachments G u v x c,
      attachmentConnectorWord G u v x c e root f) =
      if ∃ e : SelectedComponentAttachments G u v x c, e.1 = f then 1 else 0 := by
  classical
  let A := SelectedComponentAttachments G u v x c
  have hcard0 : (Fintype.card A : F₂) = 0 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    rw [Nat.cast_add]
    exact double_zero (k : F₂)
  calc
    (∑ e : A, attachmentConnectorWord G u v x c e root f) =
      (∑ e : A, if f = e.1 then (1 : F₂) else 0) +
        (∑ e : A, if f = root.1 then (1 : F₂) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      exact attachmentConnectorWord_starCoordinate G u v x c e root f hf
    _ = (if ∃ e : A, e.1 = f then 1 else 0) := by
      have hfirst : (∑ e : A, if f = e.1 then (1 : F₂) else 0) =
          if ∃ e : A, e.1 = f then 1 else 0 := by
        by_cases hex : ∃ e : A, e.1 = f
        · obtain ⟨e, he⟩ := hex
          rw [if_pos ⟨e, he⟩]
          rw [Finset.sum_eq_single e]
          · simp [he]
          · intro z hz hze
            have hzf : f ≠ z.1 := by
              intro h
              apply hze
              exact Subtype.ext (he.trans h).symm
            simp [hzf]
          · simp
        · rw [if_neg hex]
          apply Finset.sum_eq_zero
          intro z hz
          have hzf : f ≠ z.1 := by
            intro h
            exact hex ⟨z, h.symm⟩
          simp [hzf]
      have hroot : (∑ e : A, if f = root.1 then (1 : F₂) else 0) = 0 := by
        by_cases hrf : f = root.1
        · simp [hrf, hcard0]
        · simp [hrf]
      rw [hfirst, hroot]
      simp

/-- Each selected attachment connector is a cycle avoiding the opposite
marked vertex. -/
private theorem attachmentConnectorWord_spec (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent)
    (e e₀ : SelectedComponentAttachments G u v x c) :
    attachmentConnectorWord G u v x c e e₀ ∈ G.CycleSpace ∧
      ∃ hcycle : attachmentConnectorWord G u v x c e e₀ ∈ G.CycleSpace,
        (⟨attachmentConnectorWord G u v x c e e₀, hcycle⟩ : G.CycleSpace) ∈
          cyclesAvoidingVertex G v := by
  classical
  let d := attachmentEndpointsData G u v c e.2.1 e₀.2.1
  change (edgeUnit G e.1 + deletedWalkWord G u v d.2.2.1 + edgeUnit G e₀.1 ∈
      G.CycleSpace) ∧ _
  exact attachment_connector_mem_avoiding G u v hne d.2.2.2.down.1
    d.2.2.2.down.2 d.2.2.1

/-- Sum the connector cycles for all selected attachments in one component.
The result is itself a cycle avoiding `v`; the even-parity condition will be
used separately to show it cancels precisely those `u`-attachment coordinates. -/
noncomputable def componentCorrectionCycle (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent) : cyclesAvoidingVertex G v := by
  classical
  let A := SelectedComponentAttachments G u v x c
  letI : Finite A := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype A := Fintype.ofFinite A
  let connector (e root : A) : cyclesAvoidingVertex G v := by
    let s := attachmentConnectorWord_spec G u v hne x c e root
    let hc := Classical.choose s.2
    exact ⟨⟨attachmentConnectorWord G u v x c e root, hc⟩,
      Classical.choose_spec s.2⟩
  exact if h : Nonempty A then
    let root : A := Classical.choice h
    ∑ e : A, connector e root
  else 0

/-- The word underlying the component correction cycle. -/
noncomputable def componentCorrectionWord (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent) : G.Word :=
  ((componentCorrectionCycle G u v hne x c).1).1



/-- When attachments exist, the correction word is the sum of the rooted
connector words before taking the cycle-space subtype. -/
theorem componentCorrectionWord_eq_connectorSum (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (c : (deletedGraph G u v).ConnectedComponent)
    (hA : Nonempty (SelectedComponentAttachments G u v x c)) :
    componentCorrectionWord G u v hne x c =
      ∑ e : SelectedComponentAttachments G u v x c,
        attachmentConnectorWord G u v x c e (Classical.choice hA) := by
  classical
  simp [componentCorrectionWord, componentCorrectionCycle, hA]

/-- The aggregate component correction has the same `u`-incident edge
coordinates as the original cycle on this component's selected attachments. -/
theorem componentCorrectionWord_starCoordinate (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (hx : GraphicalLinkMap.linkMap G u v x = 0)
    (c : (deletedGraph G u v).ConnectedComponent) (f : G.Edge)
    (hf : G.incident f u) :
    componentCorrectionWord G u v hne x c f =
      if ∃ e : SelectedComponentAttachments G u v x c, e.1 = f then 1 else 0 := by
  classical
  let A := SelectedComponentAttachments G u v x c
  by_cases hA : Nonempty A
  · rw [componentCorrectionWord_eq_connectorSum G u v hne x c hA]
    have hstar := attachmentConnectorSum_starCoordinate G u v x c
      (Classical.choice hA) f hf
      (selectedAttachments_even_of_linkMap_eq_zero G u v hne x hx c)
    simpa only [Fintype.sum_apply] using hstar
  · have hnot : ¬ ∃ e : A, e.1 = f := by
      intro h
      exact hA ⟨Classical.choose h⟩
    have hA' : ¬ Nonempty (SelectedComponentAttachments G u v x c) := by
      simpa [A] using hA
    have hnot' : ¬ ∃ e : SelectedComponentAttachments G u v x c, e.1 = f := by
      simpa [A] using hnot
    simp [componentCorrectionWord, componentCorrectionCycle, hA', hnot']

/-- Aggregate the component corrections into one cycle avoiding `v`. -/
noncomputable def globalCorrectionCycle (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace) : cyclesAvoidingVertex G v :=
  ∑ c : (deletedGraph G u v).ConnectedComponent,
    componentCorrectionCycle G u v hne x c

noncomputable def globalCorrectionWord (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace) : G.Word :=
  ((globalCorrectionCycle G u v hne x).1).1

theorem globalCorrectionWord_eq_componentSum (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace) :
    globalCorrectionWord G u v hne x =
      ∑ c : (deletedGraph G u v).ConnectedComponent,
        componentCorrectionWord G u v hne x c := by
  simp [globalCorrectionWord, globalCorrectionCycle, componentCorrectionWord]

/-- The global correction agrees with `x` on every `u`-incident edge whose
other endpoint survives the two-vertex deletion. -/
theorem globalCorrectionWord_starCoordinate (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (hx : GraphicalLinkMap.linkMap G u v x = 0)
    (f : G.Edge) (hf : G.incident f u) (hfv : ¬ G.incident f v) :
    globalCorrectionWord G u v hne x f = x.1 f := by
  classical
  obtain ⟨c₀, hc₀, huniq⟩ :=
    existsUnique_cutComponent_of_incident_other G u v hne f hf hfv
  have hsel (c : (deletedGraph G u v).ConnectedComponent) :
      (∃ e : SelectedComponentAttachments G u v x c, e.1 = f) ↔
        componentCutCondition G u v c f ∧ x.1 f = 1 := by
    constructor
    · rintro ⟨e, rfl⟩
      exact e.2
    · rintro ⟨hcut, hxbit⟩
      exact ⟨⟨f, hcut, hxbit⟩, rfl⟩
  have hsumRewrite :
      (∑ c : (deletedGraph G u v).ConnectedComponent,
        componentCorrectionWord G u v hne x c f) =
        ∑ c : (deletedGraph G u v).ConnectedComponent,
          if ∃ e : SelectedComponentAttachments G u v x c, e.1 = f then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro c hc
    exact componentCorrectionWord_starCoordinate G u v hne x hx c f hf
  have hsumRewrite' :
      (∑ c : (deletedGraph G u v).ConnectedComponent,
        if ∃ e : SelectedComponentAttachments G u v x c, e.1 = f then (1 : F₂) else 0) =
        ∑ c : (deletedGraph G u v).ConnectedComponent,
      if componentCutCondition G u v c f ∧ x.1 f = 1 then (1 : F₂) else 0 := by
    apply Finset.sum_congr rfl
    intro c hc
    exact if_congr (hsel c) rfl rfl
  have binary : x.1 f = 0 ∨ x.1 f = 1 := by
    have hb (a : F₂) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    exact hb (x.1 f)
  calc
    globalCorrectionWord G u v hne x f =
        ∑ c : (deletedGraph G u v).ConnectedComponent,
          componentCorrectionWord G u v hne x c f := by
            rw [globalCorrectionWord_eq_componentSum]
            simp only [Fintype.sum_apply]
    _ = ∑ c : (deletedGraph G u v).ConnectedComponent,
          if ∃ e : SelectedComponentAttachments G u v x c, e.1 = f then 1 else 0 :=
      hsumRewrite
    _ = ∑ c : (deletedGraph G u v).ConnectedComponent,
          if componentCutCondition G u v c f ∧ x.1 f = 1 then 1 else 0 :=
      hsumRewrite'
    _ = x.1 f := by
      rcases binary with hx0 | hx1
      · have hsum :
            (∑ c : (deletedGraph G u v).ConnectedComponent,
              if componentCutCondition G u v c f ∧ x.1 f = 1 then (1 : F₂) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro c hc
          simp [hx0]
        simpa only [hx0] using hsum
      · have hsum :
            (∑ c : (deletedGraph G u v).ConnectedComponent,
              if componentCutCondition G u v c f ∧ x.1 f = 1 then (1 : F₂) else 0) = 1 := by
          have hciff (c : (deletedGraph G u v).ConnectedComponent) :
              componentCutCondition G u v c f ↔ c = c₀ := by
            constructor
            · exact huniq c
            · intro h
              cases h
              exact hc₀
          simp_rw [hx1, hciff]
          simp
        simpa only [hx1] using hsum

private theorem kernel_zero_of_incident_both (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace)
    (hx : GraphicalLinkMap.linkMap G u v x = 0) (f : G.Edge)
    (hu : G.incident f u) (hv : G.incident f v) : x.1 f = 0 := by
  rcases hu with hsu | hdu
  · rcases hv with hsv | hdv
    · exact (hne (hsu.symm.trans hsv)).elim
    · let d : DirectLink G u v := ⟨f, Or.inl ⟨hsu, hdv⟩⟩
      have hcoord := congrArg (fun y : LinkIndex G u v → F₂ => y (Sum.inl d)) hx
      change GraphicalLinkMap.linkCoordinate G u v x (Sum.inl d) = 0 at hcoord
      simpa [GraphicalLinkMap.linkCoordinate] using hcoord
  · rcases hv with hsv | hdv
    · let d : DirectLink G u v := ⟨f, Or.inr ⟨hsv, hdu⟩⟩
      have hcoord := congrArg (fun y : LinkIndex G u v → F₂ => y (Sum.inl d)) hx
      change GraphicalLinkMap.linkCoordinate G u v x (Sum.inl d) = 0 at hcoord
      simpa [GraphicalLinkMap.linkCoordinate] using hcoord
    · exact (hne (hdu.symm.trans hdv)).elim

/-- The kernel of the two-vertex link map is the sum of the two vertex-
avoiding cycle spaces. -/
theorem linkMap_ker_eq_avoiding_sup (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) :
    LinearMap.ker (GraphicalLinkMap.linkMap G u v) =
      cyclesAvoidingVertex G u ⊔ cyclesAvoidingVertex G v := by
  apply le_antisymm
  · intro x hx
    change GraphicalLinkMap.linkMap G u v x = 0 at hx
    let y : G.CycleSpace := (globalCorrectionCycle G u v hne x).1
    have hy : y ∈ cyclesAvoidingVertex G v := (globalCorrectionCycle G u v hne x).2
    let z : G.CycleSpace := x + y
    have hz : z ∈ cyclesAvoidingVertex G u := by
      change vertexStarRestriction G u z = 0
      ext f
      change x.1 f.1 + y.1 f.1 = 0
      by_cases hv : G.incident f.1 v
      · have hx0 := kernel_zero_of_incident_both G u v hne x hx f.1 f.2 hv
        have hy0 : y.1 f.1 = 0 := by
          have hres : vertexStarRestriction G v y = 0 := by
            simpa [cyclesAvoidingVertex] using hy
          have hbit := congrArg
            (fun g : VertexStarEdges G v → F₂ => g ⟨f.1, hv⟩) hres
          simpa [vertexStarRestriction] using hbit
        rw [hx0, hy0]
        simp
      · have hglobal := globalCorrectionWord_starCoordinate G u v hne x hx f.1 f.2 hv
        have hyx : y.1 f.1 = x.1 f.1 := hglobal
        rw [hyx]
        exact double_zero (x.1 f.1)
    have hsum : y + z = x := by
      ext f
      change y.1 f + (x.1 f + y.1 f) = x.1 f
      calc
        y.1 f + (x.1 f + y.1 f) =
            (y.1 f + y.1 f) + x.1 f := by abel
        _ = x.1 f := by rw [double_zero (y.1 f), zero_add]
    apply Submodule.mem_sup.mpr
    exact ⟨z, hz, y, hy, by simpa [hsum, add_comm]⟩
  · exact GraphicalLinkMap.avoiding_sum_le_linkMap_ker G u v hne

end Erdos1016.Proof.GraphicalLinkKernelDecomposition

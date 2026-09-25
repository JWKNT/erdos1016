import Erdos1016.Graph.Basic
import Erdos1016.Graph.Multigraph.Components

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalFiberQuotientConnected

open Erdos1016

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The edge labels retained by a quotient that discards edges internal to
fibers. -/
abbrev CrossingEdge (G : PhysicalGraph) (Q : Type*) (fiber : G.Vertex → Q) :=
  {e : G.Edge // fiber (G.src e) ≠ fiber (G.dst e)}

noncomputable def quotientVertexEquiv (Q : Type*) [Fintype Q] :
    Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

noncomputable def quotientEdgeEquiv (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) :
    CrossingEdge G Q fiber ≃ Fin (Fintype.card (CrossingEdge G Q fiber)) :=
  Fintype.equivFin _

/-- Finite multigraph consisting of all physical edges whose endpoints lie
in different fibers. Parallel edges retain their physical labels. -/
noncomputable def crossingQuotient (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) : FiniteMultiGraph where
  vertexCount := Fintype.card Q
  edgeCount := Fintype.card (CrossingEdge G Q fiber)
  src e := quotientVertexEquiv Q
    (fiber (G.src ((quotientEdgeEquiv G Q fiber).symm e).1))
  dst e := quotientVertexEquiv Q
    (fiber (G.dst ((quotientEdgeEquiv G Q fiber).symm e).1))

def quotientClassOf (G : PhysicalGraph) (Q : Type*) [Fintype Q]
    (fiber : G.Vertex → Q) : G.Vertex → (crossingQuotient G Q fiber).Vertex :=
  fun v => quotientVertexEquiv Q (fiber v)

def crossingQuotientEdgeMap (G : PhysicalGraph) (Q : Type*) [Fintype Q]
    (fiber : G.Vertex → Q) :
    (crossingQuotient G Q fiber).Edge → G.Edge := fun e =>
  ((quotientEdgeEquiv G Q fiber).symm e).1

theorem quotient_edge_source (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) (e : CrossingEdge G Q fiber) :
    (crossingQuotient G Q fiber).src (quotientEdgeEquiv G Q fiber e) =
      quotientVertexEquiv Q (fiber (G.src e.1)) := by
  simp [crossingQuotient, quotientEdgeEquiv]

theorem quotient_edge_target (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) (e : CrossingEdge G Q fiber) :
    (crossingQuotient G Q fiber).dst (quotientEdgeEquiv G Q fiber e) =
      quotientVertexEquiv Q (fiber (G.dst e.1)) := by
  simp [crossingQuotient, quotientEdgeEquiv]

@[simp] theorem crossingQuotient_src_edgeMap (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q)
    (e : (crossingQuotient G Q fiber).Edge) :
    (crossingQuotient G Q fiber).src e =
      quotientClassOf G Q fiber (G.src (crossingQuotientEdgeMap G Q fiber e)) := by
  rfl

@[simp] theorem crossingQuotient_dst_edgeMap (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q)
    (e : (crossingQuotient G Q fiber).Edge) :
    (crossingQuotient G Q fiber).dst e =
      quotientClassOf G Q fiber (G.dst (crossingQuotientEdgeMap G Q fiber e)) := by
  rfl

theorem crossingQuotientEdgeMap_injective (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) :
  Function.Injective (crossingQuotientEdgeMap G Q fiber) := by
  intro e f h
  have hs : (quotientEdgeEquiv G Q fiber).symm e =
      (quotientEdgeEquiv G Q fiber).symm f := by
    apply Subtype.ext
    exact h
  exact (quotientEdgeEquiv G Q fiber).symm.injective hs

theorem crossingQuotient_edge_coverage (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) (a : G.Edge) :
    (∃ e, crossingQuotientEdgeMap G Q fiber e = a) ∨
      fiber (G.src a) = fiber (G.dst a) := by
  by_cases hcross : fiber (G.src a) ≠ fiber (G.dst a)
  · let e' : CrossingEdge G Q fiber := ⟨a, hcross⟩
    refine Or.inl ⟨quotientEdgeEquiv G Q fiber e', ?_⟩
    simp [crossingQuotientEdgeMap, e']
  · exact Or.inr (not_not.mp hcross)

theorem crossingQuotient_loopless (G : PhysicalGraph) (Q : Type*)
    [Fintype Q] (fiber : G.Vertex → Q) :
    ∀ e : (crossingQuotient G Q fiber).Edge,
      (crossingQuotient G Q fiber).src e ≠ (crossingQuotient G Q fiber).dst e := by
  intro e heq
  let p := (quotientEdgeEquiv G Q fiber).symm e
  have hclass : quotientVertexEquiv Q (fiber (G.src p.1)) =
      quotientVertexEquiv Q (fiber (G.dst p.1)) := by
    simpa [p, crossingQuotient] using heq
  exact p.2 ((quotientVertexEquiv Q).injective hclass)

private theorem physical_adj_has_edge (G : PhysicalGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) :
    ∃ e : G.Edge,
      (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u) := by
  simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h

private theorem crossingQuotient_reachable_of_walk
    (G : PhysicalGraph) (Q : Type*) [Fintype Q] [DecidableEq Q]
    (fiber : G.Vertex → Q) {a b : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) :
    (crossingQuotient G Q fiber).toSimpleGraph.Reachable
      (quotientVertexEquiv Q (fiber a))
      (quotientVertexEquiv Q (fiber b)) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab tail ih =>
      have hhead : (crossingQuotient G Q fiber).toSimpleGraph.Reachable
          (quotientVertexEquiv Q (fiber a))
          (quotientVertexEquiv Q (fiber b)) := by
        by_cases hsame : fiber a = fiber b
        · have hq : quotientVertexEquiv Q (fiber a) =
              quotientVertexEquiv Q (fiber b) := congrArg _ hsame
          rw [hq]
        · obtain ⟨e, he⟩ := physical_adj_has_edge G hab
          have hedge : fiber (G.src e) ≠ fiber (G.dst e) := by
            rcases he with ⟨hs, ht⟩ | ⟨ht, hs⟩
            · intro h
              apply hsame
              simpa [hs, ht] using h
            · intro h
              have hba : fiber b = fiber a := by simpa [hs, ht] using h
              exact hsame hba.symm
          let qe : (crossingQuotient G Q fiber).Edge :=
            quotientEdgeEquiv G Q fiber ⟨e, hedge⟩
          have hneq : quotientVertexEquiv Q (fiber a) ≠
              quotientVertexEquiv Q (fiber b) := by
            intro h
            apply hsame
            exact (quotientVertexEquiv Q).injective h
          have hqadj : (crossingQuotient G Q fiber).toSimpleGraph.Adj
              (quotientVertexEquiv Q (fiber a))
              (quotientVertexEquiv Q (fiber b)) := by
            refine ⟨hneq, qe, ?_⟩
            rcases he with ⟨hs, ht⟩ | ⟨ht, hs⟩
            · refine Or.inl ⟨?_, ?_⟩
              · simpa [qe, hs, ht] using (quotient_edge_source G Q fiber ⟨e, hedge⟩)
              · simpa [qe, hs, ht] using (quotient_edge_target G Q fiber ⟨e, hedge⟩)
            · refine Or.inr ⟨?_, ?_⟩
              · simpa [qe, hs, ht] using (quotient_edge_source G Q fiber ⟨e, hedge⟩)
              · simpa [qe, hs, ht] using (quotient_edge_target G Q fiber ⟨e, hedge⟩)
          exact hqadj.reachable
      exact hhead.trans ih

/-- Contracting fibers in a connected physical graph and dropping internal
edges preserves connectedness, provided every quotient vertex is represented
by a physical vertex. -/
theorem crossingQuotient_connected
    (G : PhysicalGraph) (Q : Type*) [Fintype Q] [DecidableEq Q]
    (fiber : G.Vertex → Q) (hsurj : Function.Surjective fiber)
    (hconn : G.IsConnected) :
    (crossingQuotient G Q fiber).toSimpleGraph.Connected := by
  classical
  letI : Nonempty (crossingQuotient G Q fiber).Vertex := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨quotientVertexEquiv Q (fiber v)⟩
  refine ⟨?_⟩
  intro u v
  let q₁ := (quotientVertexEquiv Q).symm u
  let q₂ := (quotientVertexEquiv Q).symm v
  obtain ⟨a, ha⟩ := hsurj q₁
  obtain ⟨b, hb⟩ := hsurj q₂
  have hwalk : G.toSimpleGraph.Reachable a b := hconn.preconnected a b
  obtain ⟨p⟩ := hwalk
  have hq := crossingQuotient_reachable_of_walk G Q fiber p
  have hleft : quotientVertexEquiv Q (fiber a) = u := by
    rw [ha]
    dsimp [q₁]
    exact (quotientVertexEquiv Q).apply_symm_apply u
  have hright : quotientVertexEquiv Q (fiber b) = v := by
    rw [hb]
    dsimp [q₂]
    exact (quotientVertexEquiv Q).apply_symm_apply v
  rwa [hleft, hright] at hq

end Erdos1016.Proof.PhysicalFiberQuotientConnected

end

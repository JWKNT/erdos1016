import Erdos1016.Cleanup.Paths.WalkEdgeLift

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.AttachedPathConstruction

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.WalkEdgeLift
open SimpleGraph

theorem lifted_walk_step (G : PhysicalGraph) : ∀ {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (i : Fin p.length),
      let e := (liftedEdges G p).get ⟨i.val, by
        rw [liftedEdges_length]
        exact i.isLt⟩
      let a := p.support.get ⟨i.val, by rw [Walk.length_support]; omega⟩
      let b := p.support.get ⟨i.val + 1, by rw [Walk.length_support]; omega⟩
      (G.src e = a ∧ G.dst e = b) ∨ (G.dst e = a ∧ G.src e = b) := by
  intro u v p
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @cons a b c h p ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftedEdges, Walk.support_cons]
        have hhead : p.support[0]'(by simp) = b := by
          cases p <;> rfl
        simpa [Walk.support_cons, hhead] using liftedEdges_head_spec G h p
      · have hj := ih j
        simpa [liftedEdges, Walk.support_cons, List.getElem_cons_succ] using hj

/-- Turn any walk with distinct lifted physical labels into the certificate
shape used for a corridor. -/
def corridorOfWalk (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v)
    (hnodup : (liftedEdges G p).Nodup) : PhysicalCorridor G := by
  refine ⟨liftedEdges G p, p.support, ?_, hnodup, ?_⟩
  · rw [liftedEdges_length, Walk.length_support]
  · intro i
    have hi : i.val < p.length := by
      simpa only [liftedEdges_length] using i.isLt
    let j : Fin p.length := ⟨i.val, hi⟩
    exact lifted_walk_step G p j



private theorem liftedEdges_append_adj (G : PhysicalGraph) {a b c : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) (h : G.toSimpleGraph.Adj b c) :
    liftedEdges G (p.append (.cons h .nil)) =
      liftedEdges G p ++ [Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G h] := by
  induction p with
  | nil => rfl
  | @cons a b d hab p ih => simp [liftedEdges, ih]

/-- Attach one physical edge at each end of a spanning path and obtain a
single `PhysicalCorridor`. The hypotheses explicitly state the label
disjointness needed when the two attachments return to the same retained
vertex. -/
theorem corridor_from_path_and_two_attachments
    (G : PhysicalGraph) {x a b y : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hleft : G.toSimpleGraph.Adj x a) (hright : G.toSimpleGraph.Adj b y)
    (hleft_not :
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft ∉ liftedEdges G p)
    (hright_not :
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hright ∉ liftedEdges G p)
    (hattach_ne :
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft ≠
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hright) :
    ∃ C : PhysicalCorridor G,
      C.edges = Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft ::
        (liftedEdges G p ++
          [Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hright]) ∧
      C.vertices = x :: p.support ++ [y] ∧
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft ∈ C.support ∧
      Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hright ∈ C.support ∧
      (∀ e ∈ liftedEdges G p, e ∈ C.support) := by
  classical
  let e₀ := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft
  let e₁ := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hright
  let r : G.toSimpleGraph.Walk x y := .cons hleft (p.append (.cons hright .nil))
  have hlift : liftedEdges G r = e₀ :: (liftedEdges G p ++ [e₁]) := by
    change Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hleft ::
      liftedEdges G (p.append (.cons hright .nil)) = _
    rw [liftedEdges_append_adj]
  have hbody : (liftedEdges G p ++ [e₁]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨liftedEdges_nodup_of_isPath G p hp, by simp, ?_⟩
    apply List.disjoint_left.mpr
    intro e heP he1
    simp only [List.mem_singleton] at he1
    subst e
    exact hright_not heP
  have hnodup : (liftedEdges G r).Nodup := by
    rw [hlift]
    apply List.nodup_cons.mpr
    refine ⟨?_, hbody⟩
    intro he
    rcases List.mem_append.mp he with hmem | hmem
    · exact hleft_not hmem
    · simp only [List.mem_singleton] at hmem
      exact hattach_ne (by simpa [e₀, e₁] using hmem)
  let C := corridorOfWalk G r hnodup
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · change liftedEdges G r = _
    exact hlift
  · change r.support = x :: p.support ++ [y]
    simp [r, Walk.support_cons, Walk.support_append]
  · change e₀ ∈ (liftedEdges G r).toFinset
    rw [hlift]
    simp
  · change e₁ ∈ (liftedEdges G r).toFinset
    rw [hlift]
    simp
  · intro e he
    change e ∈ (liftedEdges G r).toFinset
    rw [hlift]
    simp [he]

end Erdos1016.Proof.AttachedPathConstruction

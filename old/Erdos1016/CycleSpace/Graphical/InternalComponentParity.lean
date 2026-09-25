import Erdos1016.CycleSpace.InternalBoundaryRepair
import Erdos1016.CycleSpace.Graphical.LinkPairWitnesses

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.QuotientCycleInternalComponentParity

open Erdos1016
open Erdos1016.Proof.GraphicalActualCutMultigraphBridge
open Erdos1016.Proof.GraphicalActualCutMultigraphSurjective
open Erdos1016.Proof.InternalRegionBoundaryRepair

local notation "𝔽" => ZMod 2

private abbrev fiber (G : PhysicalGraph) (M : FiniteMultiGraph)
    (classOf : G.Vertex → M.Vertex) (q : M.Vertex) :=
  {v : G.Vertex // classOf v = q}

private noncomputable instance fiberFintype (G : PhysicalGraph)
    (M : FiniteMultiGraph) (classOf : G.Vertex → M.Vertex) (q : M.Vertex) :
    Fintype (fiber G M classOf q) := Fintype.ofFinite _



private theorem internalAdj_iff_ambientAdj_on_fiber
    (G : PhysicalGraph) (M : FiniteMultiGraph) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e))
    (q : M.Vertex) {u v : G.Vertex}
    (hu : classOf u = q) (hv : classOf v = q) :
    (internalMultiGraph G I).toSimpleGraph.Adj u v ↔
      G.toSimpleGraph.Adj u v := by
  constructor
  · rintro ⟨huv, e, hedge | hedge⟩
    · have heI : e ∈ I := by
        by_contra hnot
        have hdst : G.src e = v := by simpa [internalMultiGraph, hnot] using hedge.2
        exact huv (hedge.1.symm.trans hdst)
      change ∃ e, (fun _ : G.Edge => (1 : 𝔽)) e ≠ 0 ∧
        ((G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u))
      refine ⟨e, by simp, ?_⟩
      left
      exact ⟨hedge.1, by simpa [internalMultiGraph, heI] using hedge.2⟩
    · have heI : e ∈ I := by
        by_contra hnot
        have hsrc : G.src e = u := by simpa [internalMultiGraph, hnot] using hedge.2
        have hsrcv : G.src e = v := hedge.1
        exact huv (hsrc.symm.trans hsrcv)
      change ∃ e, (fun _ : G.Edge => (1 : 𝔽)) e ≠ 0 ∧
        ((G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u))
      refine ⟨e, by simp, ?_⟩
      right
      exact ⟨by simpa [internalMultiGraph, heI] using hedge.1, by simpa [internalMultiGraph, heI] using hedge.2⟩
  · intro hadj
    let e := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj
    have he := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj_spec G hadj
    have hclasses : classOf (G.src (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) =
        classOf (G.dst (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) := by
      rcases he with h | h
      · calc
          classOf (G.src (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) = classOf u := congrArg classOf h.1
          _ = classOf v := hu.trans hv.symm
          _ = classOf (G.dst (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) := congrArg classOf h.2.symm
      · calc
          classOf (G.src (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) = classOf v := congrArg classOf h.1
          _ = classOf u := (hu.trans hv.symm).symm
          _ = classOf (G.dst (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)) := congrArg classOf h.2.symm
    have heI : Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj ∈ I :=
      (hI (Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj)).2 hclasses
    refine ⟨hadj.ne, Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj, ?_⟩
    rcases he with h | h
    · left
      exact ⟨h.1, by simpa [internalMultiGraph, heI] using h.2⟩
    · right
      refine ⟨h.1, ?_⟩
      change (if Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hadj ∈ I
        then G.dst _ else G.src _) = u
      rw [if_pos heI]
      exact h.2

private theorem internalAdj_classes_eq
    (G : PhysicalGraph) (M : FiniteMultiGraph) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e))
    {u v : G.Vertex} (h : (internalMultiGraph G I).toSimpleGraph.Adj u v) :
    classOf u = classOf v := by
  rcases h with ⟨huv, e, hedge | hedge⟩
  · have heI : e ∈ I := by
      by_contra hnot
      have hdst : G.src e = v := by simpa [internalMultiGraph, hnot] using hedge.2
      exact huv (hedge.1.symm.trans hdst)
    calc
      classOf u = classOf (G.src e) := congrArg classOf hedge.1.symm
      _ = classOf (G.dst e) := (hI e).mp heI
      _ = classOf v := by simpa [internalMultiGraph, heI] using congrArg classOf hedge.2
  · have heI : e ∈ I := by
      by_contra hnot
      have hsrc : G.src e = u := by simpa [internalMultiGraph, hnot] using hedge.2
      exact huv (hsrc.symm.trans hedge.1)
    calc
      classOf u = classOf (G.dst e) := by
        simpa [internalMultiGraph, heI] using congrArg classOf hedge.2.symm
      _ = classOf (G.src e) := ((hI e).mp heI).symm
      _ = classOf v := by
        simpa [internalMultiGraph] using congrArg classOf hedge.1

private theorem classes_eq_of_internalWalk
    (G : PhysicalGraph) (M : FiniteMultiGraph) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e))
    {u v : G.Vertex} (p : (internalMultiGraph G I).toSimpleGraph.Walk u v) :
    classOf u = classOf v := by
  induction p with
  | nil => rfl
  | @cons u v w hadj p ih =>
      exact (internalAdj_classes_eq G M I classOf hI hadj).trans ih

/-- If the retained internal edges are exactly the same-class edges and every
class induces a connected subgraph, then the internal multigraph components
are exactly the class fibers. This is the concrete fiber/component bridge
needed by the raw-lift boundary repair argument. -/
theorem internalComponent_iff_class_eq
    (G : PhysicalGraph) (M : FiniteMultiGraph) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e))
    (hfiberConnected : ∀ q : M.Vertex,
      (G.toSimpleGraph.induce {v | classOf v = q}).Connected)
    (c : (internalMultiGraph G I).ConnectedComponent) (v : G.Vertex) :
    (internalMultiGraph G I).componentOf v = c ↔
      classOf v = classOf (c.out) := by
  constructor
  · intro hcomp
    have hEq : (internalMultiGraph G I).toSimpleGraph.connectedComponentMk (c.out) =
        (internalMultiGraph G I).toSimpleGraph.connectedComponentMk v := by
      calc
        _ = c := c.out_eq
        _ = (internalMultiGraph G I).componentOf v := hcomp.symm
        _ = _ := rfl
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hEq
    exact (classes_eq_of_internalWalk G M I classOf hI p).symm
  · intro hclass
    let q := classOf (c.out)
    have hroot : classOf (c.out) = q := rfl
    have hv : classOf v = q := hclass
    have hreach : (G.toSimpleGraph.induce {u | classOf u = q}).Reachable
        ⟨c.out, hroot⟩ ⟨v, hv⟩ := by
      exact hfiberConnected q ⟨c.out, hroot⟩ ⟨v, hv⟩
    obtain ⟨p⟩ := hreach
    let φ : (G.toSimpleGraph.induce {u | classOf u = q}) →g
        (internalMultiGraph G I).toSimpleGraph := {
      toFun := fun x => x.1
      map_rel' := by
        intro a b hadj
        have hAdjG : G.toSimpleGraph.Adj a.1 b.1 := hadj
        exact (internalAdj_iff_ambientAdj_on_fiber
          G M I classOf hI q a.2 b.2).2 hAdjG }
    have hreachH : (internalMultiGraph G I).toSimpleGraph.Reachable (c.out) v := by
      exact (p.map φ).reachable
    have hEq : (internalMultiGraph G I).toSimpleGraph.connectedComponentMk (c.out) =
        (internalMultiGraph G I).toSimpleGraph.connectedComponentMk v :=
          SimpleGraph.ConnectedComponent.sound hreachH
    calc
      (internalMultiGraph G I).componentOf v =
          (internalMultiGraph G I).toSimpleGraph.connectedComponentMk v := rfl
      _ = (internalMultiGraph G I).toSimpleGraph.connectedComponentMk (c.out) := hEq.symm
      _ = c := c.out_eq

/-- Package the preceding pointwise equivalence in the existential form used
by the boundary-parity transfer theorem. -/
theorem internalComponents_are_fibers
    (G : PhysicalGraph) (M : FiniteMultiGraph) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e))
    (hfiberConnected : ∀ q : M.Vertex,
      (G.toSimpleGraph.induce {v | classOf v = q}).Connected) :
    ∀ c : (internalMultiGraph G I).ConnectedComponent,
      ∃ q : M.Vertex, ∀ v : G.Vertex,
        (internalMultiGraph G I).componentOf v = c ↔ classOf v = q := by
  intro c
  refine ⟨classOf (c.out), ?_⟩
  intro v
  exact internalComponent_iff_class_eq G M I classOf hI hfiberConnected c v

private theorem fiber_endpoint_sum
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (classOf : G.Vertex → M.Vertex) (q : M.Vertex)
    (a : G.Vertex) (x : 𝔽) :
    (∑ v : fiber G M classOf q, if a = v.1 then x else 0) =
      if classOf a = q then x else 0 := by
  classical
  by_cases hq : classOf a = q
  · let w : fiber G M classOf q := ⟨a, hq⟩
    have hiff : ∀ v : fiber G M classOf q, a = v.1 ↔ v = w := by
      intro v
      constructor
      · intro hav
        apply Subtype.ext
        exact hav.symm
      · intro hvw
        have := congrArg Subtype.val hvw
        exact this.symm
    simp [hq, hiff, w]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : a ≠ v.1 := by
      intro hav
      exact hq (hav ▸ v.2)
    simp [hne]

/-- Aggregate the original boundary over one quotient fiber. The quotient
edge labels inject into the original labels with endpoint classes preserved;
every omitted original edge is internal to a fiber. Thus omitted labels
contribute zero to the raw lift, and mapped labels aggregate exactly as their
quotient incidences. -/
theorem fiberBoundarySum_eq_quotientBoundary_of_crossEdgeCorrespondence
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge)
    (hinj : Function.Injective edgeMap)
    (classOf : G.Vertex → M.Vertex)
    (hsrc : ∀ e, M.src e = classOf (G.src (edgeMap e)))
    (hdst : ∀ e, M.dst e = classOf (G.dst (edgeMap e)))
    (hcoverage : ∀ a : G.Edge,
      (∃ e, edgeMap e = a) ∨ classOf (G.src a) = classOf (G.dst a))
    (y : M.EdgeWord) (q : M.Vertex) :
    (∑ v : fiber G M classOf q,
      G.boundary (rawLiftWord M edgeMap y) v.1) =
      M.boundary (restrictWord M edgeMap (rawLiftWord M edgeMap y)) q := by
  classical
  have hfiber (a : G.Edge) :
      (∑ v : fiber G M classOf q,
        ((if G.src a = v.1 then rawLiftWord M edgeMap y a else 0) +
         (if G.dst a = v.1 then rawLiftWord M edgeMap y a else 0))) =
      (if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
      (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0) := by
    rw [Finset.sum_add_distrib]
    rw [fiber_endpoint_sum G M classOf q (G.src a) (rawLiftWord M edgeMap y a)]
    rw [fiber_endpoint_sum G M classOf q (G.dst a) (rawLiftWord M edgeMap y a)]
  have houtside (a : G.Edge) (ha : a ∉ Finset.univ.image edgeMap) :
      rawLiftWord M edgeMap y a = 0 := by
    classical
    apply dif_neg
    intro hex
    apply ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact hex
  have hsumImage :
      (∑ a : G.Edge,
        ((if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
         (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0))) =
      ∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
         (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _) ?_
    intro a ha hna
    have hsame := (hcoverage a).resolve_left (by
      intro hex
      apply hna
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact hex)
    rw [houtside a hna]
    simp [hsame]
  have hedgeReindex :
      (∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
         (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0))) =
      ∑ e : M.Edge,
        ((if M.src e = q then y e else 0) + (if M.dst e = q then y e else 0)) := by
    rw [Finset.sum_image (fun x hx y hy hxy => hinj hxy)]
    apply Fintype.sum_congr
    intro e
    rw [rawLiftWord_on_edge M edgeMap hinj y e, hsrc e, hdst e]
  have hrestrict : restrictWord M edgeMap (rawLiftWord M edgeMap y) = y := by
    funext e
    exact rawLiftWord_on_edge M edgeMap hinj y e
  calc
    (∑ v : fiber G M classOf q,
        G.boundary (rawLiftWord M edgeMap y) v.1) =
      ∑ a : G.Edge,
        ((if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
         (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0)) := by
      change (∑ v : fiber G M classOf q, ∑ a : G.Edge,
        ((if G.src a = v.1 then rawLiftWord M edgeMap y a else 0) +
         (if G.dst a = v.1 then rawLiftWord M edgeMap y a else 0))) = _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact hfiber a
    _ = ∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then rawLiftWord M edgeMap y a else 0) +
         (if classOf (G.dst a) = q then rawLiftWord M edgeMap y a else 0)) := hsumImage
    _ = ∑ e : M.Edge,
        ((if M.src e = q then y e else 0) + (if M.dst e = q then y e else 0)) := hedgeReindex
    _ = M.boundary (restrictWord M edgeMap (rawLiftWord M edgeMap y)) q := by
      rw [hrestrict]
      rfl

/-- The aggregation identity immediately gives componentwise fiber parity
for the raw lift of a quotient cycle. -/
theorem fiberBoundarySum_eq_zero_of_quotientCycle_crossEdgeCorrespondence
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge)
    (hinj : Function.Injective edgeMap)
    (classOf : G.Vertex → M.Vertex)
    (hsrc : ∀ e, M.src e = classOf (G.src (edgeMap e)))
    (hdst : ∀ e, M.dst e = classOf (G.dst (edgeMap e)))
    (hcoverage : ∀ a : G.Edge,
      (∃ e, edgeMap e = a) ∨ classOf (G.src a) = classOf (G.dst a))
    (y : M.CycleSpace) (q : M.Vertex) :
    (∑ v : fiber G M classOf q,
      G.boundary (rawLiftWord M edgeMap y.1) v.1) = 0 := by
  rw [fiberBoundarySum_eq_quotientBoundary_of_crossEdgeCorrespondence
    G M edgeMap hinj classOf hsrc hdst hcoverage y.1 q]
  have hrestrict : restrictWord M edgeMap (rawLiftWord M edgeMap y.1) = y.1 := by
    funext e
    exact rawLiftWord_on_edge M edgeMap hinj y.1 e
  rw [hrestrict]
  exact congrFun y.2 q


/-- If every internal connected component is exactly one quotient fiber, and
the raw-lift boundary sums to zero on every quotient fiber, then that boundary
is componentwise even in the internal-edge multigraph. -/
theorem rawLiftBoundary_componentEven_of_fiberSums
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge) (I : Finset G.Edge)
    (classOf : G.Vertex → M.Vertex)
    (hcomponent : ∀ c : (internalMultiGraph G I).ConnectedComponent,
      ∃ q : M.Vertex, ∀ v : G.Vertex,
        (internalMultiGraph G I).componentOf v = c ↔ classOf v = q)
    (hfiberEven : ∀ y : M.CycleSpace, ∀ q : M.Vertex,
      (∑ v : fiber G M classOf q,
        G.boundary (rawLiftWord M edgeMap y.1) v.1) = 0)
    (y : M.CycleSpace) :
    (internalMultiGraph G I).ComponentEven
      (G.boundary (rawLiftWord M edgeMap y.1)) := by
  intro c
  obtain ⟨q, hq⟩ := hcomponent c
  let C := (internalMultiGraph G I).ComponentVertex c
  let e : C ≃ {v : G.Vertex // classOf v = q} := {
    toFun := fun v => (⟨v.1, (hq v.1).mp v.2⟩ : {v : G.Vertex // classOf v = q})
    invFun := fun v => (⟨v.1, (hq v.1).mpr v.2⟩ : C)
    left_inv := fun v => by cases v; rfl
    right_inv := fun v => by cases v; rfl }
  calc
    (internalMultiGraph G I).componentDemandSum
        (G.boundary (rawLiftWord M edgeMap y.1)) c =
      ∑ v : C, G.boundary (rawLiftWord M edgeMap y.1) v.1 := rfl
    _ = ∑ v : {v : G.Vertex // classOf v = q},
        G.boundary (rawLiftWord M edgeMap y.1) v.1 := by
      apply Fintype.sum_equiv e
      intro v
      rfl
    _ = 0 := hfiberEven y q



end Erdos1016.Proof.QuotientCycleInternalComponentParity

end

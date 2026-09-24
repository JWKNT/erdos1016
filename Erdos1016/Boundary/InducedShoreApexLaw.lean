import Erdos1016.Graph.InducedShore
import Erdos1016.Boundary.VertexAverage
import Erdos1016.Boundary.ApexLaw

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Erdos1016.BoundaryTrace Erdos1016.BoundaryDecay
open Erdos1016.Extremal

namespace Erdos1016.Extremal

local instance finiteProofDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem apexFraction_fintype_eq {A B E F P : Type*} [Fintype P]
    (f₁ f₂ : Fintype E) {I : Network A E} {O : Network B F}
    (L : Ported I O P) (Good : I.Word → Prop) :
    @Ported.apexFraction A B E F P f₁ inferInstance I O L Good =
      @Ported.apexFraction A B E F P f₂ inferInstance I O L Good := by
  cases Subsingleton.elim f₁ f₂
  rfl

/-- The shore's degree-two vertices are exactly the pins of its physical
induced graph. -/
def inducedShorePinEquiv (G : PhysicalGraph) (U : Finset G.Vertex)
    :
    G.TraceBoundaryVertex U ≃ CorePin (inducedShoreGraph G U) := by
  let V := inducedShoreVertexEquiv G U
  refine {
    toFun := fun v => ⟨V v.1, ?_⟩
    invFun := fun w => ⟨V.symm w.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [inducedShore_degree_eq_traceInsideDegree]
    exact v.2
  · rw [← inducedShore_degree_eq_traceInsideDegree, V.apply_symm_apply]
    exact w.2
  · intro v
    apply Subtype.ext
    exact V.symm_apply_apply v.1
  · intro w
    apply Subtype.ext
    exact V.apply_symm_apply w.1

/-- Reindex the one-apex completion of the actual induced shore to the
degree-two-pin apex graph, retaining each inside edge and each pin. -/
def inducedShoreApexReindex
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hc : ∀ v ∈ U, G.degree v = 3)
    (hmin : ∀ v ∈ U, 2 ≤ G.traceInsideDegree U v) :
    Network.Reindex
      (((Network.Shore.ported G.traceNetwork U).relabelPins
        ((G.cutPinEquivDegreeTwo U hc hmin).trans
          (inducedShorePinEquiv G U))).apex)
      (corePorts (inducedShoreGraph G U)).apex := by
  classical
  let H := inducedShoreGraph G U
  let N := Network.Shore.inside G.traceNetwork U
  let V := inducedShoreVertexEquiv G U
  let E := Fintype.equivFin (Network.Shore.InsideEdge G.traceNetwork U)
  let pin0 := G.cutPinEquivDegreeTwo U hc hmin
  let pin1 := inducedShorePinEquiv G U
  let p := pin0.trans pin1
  let r := BoundaryDecay.physicalReindex N (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)
  refine {
    vertices := Equiv.sumCongr V (Equiv.refl Unit)
    edges := Equiv.sumCongr E (Equiv.refl (CorePin H))
    endpoints := ?_ }
  intro e
  cases e with
  | inl e =>
      have he := r.endpoints e
      rcases he with he | he
      · have hs : V (N.src e) = H.traceNetwork.src (E e) := by
          change r.vertices (N.src e) = (physicalize N
            (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)).traceNetwork.src (r.edges e)
          exact he.1
        have ht : V (N.dst e) = H.traceNetwork.dst (E e) := by
          change r.vertices (N.dst e) = (physicalize N
            (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)).traceNetwork.dst (r.edges e)
          exact he.2
        exact Or.inl ⟨congrArg (Sum.inl : H.Vertex → H.Vertex ⊕ Unit) hs,
          congrArg (Sum.inl : H.Vertex → H.Vertex ⊕ Unit) ht⟩
      · have hs : V (N.src e) = H.traceNetwork.dst (E e) := by
          change r.vertices (N.src e) = (physicalize N
            (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)).traceNetwork.dst (r.edges e)
          exact he.1
        have ht : V (N.dst e) = H.traceNetwork.src (E e) := by
          change r.vertices (N.dst e) = (physicalize N
            (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)).traceNetwork.src (r.edges e)
          exact he.2
        exact Or.inr ⟨congrArg (Sum.inl : H.Vertex → H.Vertex ⊕ Unit) hs,
          congrArg (Sum.inl : H.Vertex → H.Vertex ⊕ Unit) ht⟩
  | inr q =>
      have hpin : p (p.symm q) = q := by simp [p]
      have h0 :
          Network.Shore.insidePin G.traceNetwork U (pin0.symm (pin1.symm q)) =
            (pin1.symm q).1 := by
        have h := congrArg Subtype.val (pin0.apply_symm_apply (pin1.symm q))
        exact h
      have h1 : V (pin1.symm q).1 = q.1 := by
        change V (V.symm q.1) = q.1
        exact V.apply_symm_apply q.1
      have hsrc : V (Network.Shore.insidePin G.traceNetwork U
          (pin0.symm (pin1.symm q))) = q.1 := by
        exact (congrArg V h0).trans h1
      left
      simp [H, p, pin0, pin1, Ported.apex, Ported.relabelPins, V, hpin, hsrc,
        Network.Shore.ported, corePorts]

/-- The original one-apex forest law is exactly the degree-two-pin apex law
on the physical induced shore. -/
theorem oneApexForestFraction_eq_coreBoundaryAverage
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hc : ∀ v ∈ U, G.degree v = 3)
    (hmin : ∀ v ∈ U, 2 ≤ G.traceInsideDegree U v) :
    G.oneApexForestFraction U = coreBoundaryAverage (inducedShoreGraph G U) := by
  classical
  let H := inducedShoreGraph G U
  let N := Network.Shore.inside G.traceNetwork U
  let p := (G.cutPinEquivDegreeTwo U hc hmin).trans (inducedShorePinEquiv G U)
  let L := (Network.Shore.ported G.traceNetwork U).relabelPins p
  let K := corePorts H
  let r := inducedShoreApexReindex G U hc hmin
  let rInner := BoundaryDecay.physicalReindex N
    (Erdos1016.Nonbacktracking.FiniteTwoCore.inducedNetworkSimple G U)
  have hleft : G.oneApexForestFraction U = L.apexFraction N.IsForest := by
    change Network.Shore.boundaryAverage G.traceNetwork U N.IsForest = _
    rw [Network.Shore.boundaryAverage_relabelPins G.traceNetwork U p N.IsForest]
    exact apexFraction_fintype_eq _ _ L N.IsForest
  have hright : coreBoundaryAverage H = K.apexFraction H.traceNetwork.IsForest := rfl
  have hevent : ∀ x : L.apex.CycleSpace,
      N.IsForest (L.apexWordEquiv x.1).1 ↔
        H.traceNetwork.IsForest (K.apexWordEquiv (r.cycleEquiv x).1).1 := by
    intro x
    have hword : rInner.wordEquiv (L.apexWordEquiv x.1).1 =
        (K.apexWordEquiv (r.cycleEquiv x).1).1 := by
      funext e
      have hedge : r.edges (Sum.inl (rInner.edges.symm e)) = Sum.inl e := by
        simp [r, rInner, inducedShoreApexReindex,
          BoundaryDecay.physicalReindex, H, N]
        convert (Fintype.equivFin (Network.Shore.InsideEdge G.traceNetwork U)).apply_symm_apply e
          using 1
      have hval : r.wordEquiv x.1 (Sum.inl e) =
          x.1 (Sum.inl (rInner.edges.symm e)) := by
        rw [← hedge]
        exact r.wordEquiv_apply_edge x.1 (Sum.inl (rInner.edges.symm e))
      change (L.apexWordEquiv x.1).1 (rInner.edges.symm e) =
        r.wordEquiv x.1 (Sum.inl e)
      simpa [rInner, L, Ported.apexWordEquiv] using hval.symm
    rw [← hword]
    change (N.selectedGraph (L.apexWordEquiv x.1).1).IsAcyclic ↔
      (H.traceNetwork.selectedGraph
        (rInner.wordEquiv (L.apexWordEquiv x.1).1)).IsAcyclic
    let iso : (N.selectedGraph (L.apexWordEquiv x.1).1) ≃g
        H.traceNetwork.selectedGraph (rInner.wordEquiv (L.apexWordEquiv x.1).1) := {
      toEquiv := rInner.vertices
      map_rel_iff' := by
        intro u v
        exact BoundaryDecay.selected_reindex_adj rInner
          (L.apexWordEquiv x.1).1 u v }
    exact (BoundaryDecay.acyclic_iff_of_iso iso)
  have hfrac : L.apexFraction N.IsForest = K.apexFraction H.traceNetwork.IsForest := by
    unfold Ported.apexFraction
    exact Finite.density_equiv r.cycleEquiv hevent
  rw [hleft, hright]
  exact hfrac

end Erdos1016.Extremal

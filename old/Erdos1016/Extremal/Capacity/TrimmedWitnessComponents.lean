import Erdos1016.Cleanup.Support.VertexSupportedWitness

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.TrimmedWitnessComponentBridge

open Erdos1016
open Erdos1016.Proof.VertexSupportedWitness

/-- Every adjacency in the literal support graph has endpoints in the
witness endpoint set. -/
theorem witnessSupport_adj_endpoints (G : PhysicalGraph)
    (F : Finset G.CycleWord) {u v : (witnessSupportGraph G F).Vertex}
    (h : (witnessSupportGraph G F).toSimpleGraph.Adj u v) :
    u ∈ (witnessSupportVertices G F : Set G.Vertex) ∧
      v ∈ (witnessSupportVertices G F : Set G.Vertex) := by
  classical
  let W := witnessSupportGraph G F
  let E := witnessSupportEdges G F
  change ∃ e : W.Edge, (1 : F₂) ≠ 0 ∧
    ((W.src e = u ∧ W.dst e = v) ∨ (W.src e = v ∧ W.dst e = u)) at h
  obtain ⟨e, _, hend | hend⟩ := h
  · let q := ((Finset.equivFin E).symm e).1
    have hq : q ∈ E := ((Finset.equivFin E).symm e).2
    have hsrc : G.src q = u := by simpa [W, witnessSupportGraph, q] using hend.1
    have hdst : G.dst q = v := by simpa [W, witnessSupportGraph, q] using hend.2
    constructor
    · change u ∈ witnessSupportVertices G F
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, hq, Or.inl hsrc⟩⟩
    · change v ∈ witnessSupportVertices G F
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, hq, Or.inr hdst⟩⟩
  · let q := ((Finset.equivFin E).symm e).1
    have hq : q ∈ E := ((Finset.equivFin E).symm e).2
    have hsrc : G.src q = v := by simpa [W, witnessSupportGraph, q] using hend.1
    have hdst : G.dst q = u := by simpa [W, witnessSupportGraph, q] using hend.2
    constructor
    · change u ∈ witnessSupportVertices G F
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, hq, Or.inr hdst⟩⟩
    · change v ∈ witnessSupportVertices G F
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, hq, Or.inl hsrc⟩⟩

/-- If every edge of a finite graph has both endpoints in `S`, its components
split into the components of the induced graph on `S` and one singleton for
each vertex outside `S`. -/
noncomputable def component_equiv_induce_sum_complement
    {V : Type*} [Fintype V]
    (J : SimpleGraph V) (S : Set V)
    (hends : ∀ ⦃u v⦄, J.Adj u v → u ∈ S ∧ v ∈ S) :
    J.ConnectedComponent ≃
      (J.induce S).ConnectedComponent ⊕ {v : V // v ∉ S} := by
  classical
  let I := J.induce S
  let splitVertex : V → I.ConnectedComponent ⊕ {v : V // v ∉ S} := fun v =>
    if hv : v ∈ S then Sum.inl (I.connectedComponentMk ⟨v, hv⟩)
    else Sum.inr ⟨v, hv⟩
  have hwalk : ∀ {u v : V} (p : J.Walk u v), splitVertex u = splitVertex v := by
    intro u v p
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
      have huv' := hends huv
      have hI : I.Adj ⟨u, huv'.1⟩ ⟨v, huv'.2⟩ := huv
      have heq : splitVertex u = splitVertex v := by
        simp only [splitVertex, dif_pos huv'.1, dif_pos huv'.2]
        exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.sound hI.reachable)
      exact heq.trans ih
  let toSum : J.ConnectedComponent →
      I.ConnectedComponent ⊕ {v : V // v ∉ S} :=
    SimpleGraph.ConnectedComponent.lift splitVertex (fun _ _ p _ => hwalk p)
  let fromSum : I.ConnectedComponent ⊕ {v : V // v ∉ S} → J.ConnectedComponent :=
    fun x => match x with
      | Sum.inl c => J.connectedComponentMk (Classical.choose c.nonempty_supp).1
      | Sum.inr v => J.connectedComponentMk v.1
  have hleft (c : I.ConnectedComponent) : toSum (fromSum (Sum.inl c)) = Sum.inl c := by
    let v := Classical.choose c.nonempty_supp
    have hv : v ∈ c.supp := Classical.choose_spec c.nonempty_supp
    have hvS : v.1 ∈ S := v.2
    have hcomp : I.connectedComponentMk v = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp hv
    change toSum (J.connectedComponentMk v.1) = Sum.inl c
    simp only [toSum, SimpleGraph.ConnectedComponent.lift_mk, splitVertex, dif_pos hvS]
    exact congrArg Sum.inl hcomp
  have hright (v : {v : V // v ∉ S}) : toSum (fromSum (Sum.inr v)) = Sum.inr v := by
    simp [toSum, fromSum, SimpleGraph.ConnectedComponent.lift_mk, splitVertex, v.2]
  have hfromto (c : J.ConnectedComponent) : fromSum (toSum c) = c := by
    refine SimpleGraph.ConnectedComponent.ind ?_ c
    intro v
    by_cases hv : v ∈ S
    · let vI : {x : V // x ∈ S} := ⟨v, hv⟩
      let cI := I.connectedComponentMk vI
      let u := Classical.choose cI.nonempty_supp
      have hu : u ∈ cI.supp := Classical.choose_spec cI.nonempty_supp
      have hcomp : I.connectedComponentMk vI = I.connectedComponentMk u := by
        have hu' : I.connectedComponentMk u = cI :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff cI u).mp hu
        simpa [cI] using hu'.symm
      have hreach : I.Reachable vI u := SimpleGraph.ConnectedComponent.exact hcomp
      obtain ⟨p⟩ := hreach
      let incl : I →g J := ⟨Subtype.val, fun {x y} h => h⟩
      have hreach' : J.Reachable v u.1 := by
        simpa [incl, vI] using (p.map incl).reachable
      have hcomp' : J.connectedComponentMk u.1 = J.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.sound hreach'.symm
      have hto : toSum (J.connectedComponentMk v) = Sum.inl cI := by
        change splitVertex v = Sum.inl cI
        simp only [splitVertex, dif_pos hv]
        rfl
      rw [hto]
      simpa [fromSum] using hcomp'
    · have hto : toSum (J.connectedComponentMk v) = Sum.inr ⟨v, hv⟩ := by
        simp [toSum, SimpleGraph.ConnectedComponent.lift_mk, splitVertex, hv]
      rw [hto]
  exact Equiv.ofBijective toSum ⟨
    (fun a b hab => by
      have := congrArg fromSum hab
      simpa only [hfromto] using this),
    (fun x => by
      cases x with
      | inl c => exact ⟨fromSum (Sum.inl c), hleft c⟩
      | inr v => exact ⟨fromSum (Sum.inr v), hright v⟩)⟩

/-- Exact component-count adjustment, once the induced graph on the nonisolated
vertices is identified with a target graph. -/
theorem component_card_adjustment_of_induced_iso
    {V W : Type*} [Fintype V] [Fintype W]
    (J : SimpleGraph V) (S : Set V)
    (hends : ∀ ⦃u v⦄, J.Adj u v → u ∈ S ∧ v ∈ S)
    (K : SimpleGraph W) (iso : (J.induce S) ≃g K)
    [Fintype J.ConnectedComponent] [Fintype (J.induce S).ConnectedComponent]
    [Fintype K.ConnectedComponent] [Fintype {v : V // v ∉ S}] :
    Fintype.card J.ConnectedComponent =
      Fintype.card K.ConnectedComponent + Fintype.card {v : V // v ∉ S} := by
  classical
  let e := component_equiv_induce_sum_complement J S hends
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_congr iso.connectedComponentEquiv] at hc
  exact hc



end Erdos1016.Proof.TrimmedWitnessComponentBridge

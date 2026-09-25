import Erdos1016.Cleanup.CleanupSpecification
import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

/-!
# Component counts after removing a cleanup root

If every connected component left outside a root meets the protected set,
then the actual exterior has no more components than the graph induced on the
protected set. This is the component-count step used to retain the quadratic
bound in the Section 10 reduction.
-/

noncomputable section

namespace Erdos1016.Proof.ProtectedExteriorComponents

open Erdos1016.Proof.CleanupSpecification
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem walk_first_entry
    (J : SimpleGraph V) (S : Finset V) {u v : V}
    (p : J.Walk u v) (hu : u ∉ S) (hv : v ∈ S) :
    ∃ (a b : V) (q : J.Walk u a), a ∉ S ∧ b ∈ S ∧ J.Adj a b ∧
      ∀ z ∈ q.support, z ∉ S := by
  induction p with
  | nil => exact (hu hv).elim
  | @cons a b c hab tail ih =>
      by_cases hb : b ∈ S
      · refine ⟨a, b, .nil, hu, hb, hab, ?_⟩
        intro z hz
        simp at hz
        subst z
        exact hu
      · obtain ⟨x, y, q, hx, hy, hxy, hq⟩ := ih hb hv
        refine ⟨x, y, .cons hab q, hx, hy, hxy, ?_⟩
        intro z hz
        simp only [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hu
        · exact hq z hz

private def walk_lift_to_induce
    (J : SimpleGraph V) (S : Set V) {u v : V}
    (p : J.Walk u v) (hu : u ∈ S) (hv : v ∈ S)
    (hsupport : ∀ z ∈ p.support, z ∈ S) :
    (J.induce S).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact .nil
  | @cons a b c hab tail ih =>
      have ha : a ∈ S := hsupport a (by simp)
      have hb : b ∈ S := hsupport b (by simp)
      have htail : ∀ z ∈ tail.support, z ∈ S := by
        intro z hz
        exact hsupport z (by simp [hz])
      have hadj : (J.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
      exact .cons hadj (ih hb hv htail)

/-- The original vertices represented by one component of the graph outside
the protected set. -/
noncomputable def componentVertexSet
    (J : SimpleGraph V) (P : Finset V)
    (c : (J.induce (↑(Pᶜ) : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter fun v : V =>
    ∃ x : {y : V // y ∈ (↑(Pᶜ) : Set V)}, x ∈ c.supp ∧ x.1 = v

/-- Removing one entire component of the graph outside a protected set leaves
no exterior component disjoint from that protected set. -/
theorem every_exterior_component_meets_protected
    (J : SimpleGraph V) (P : Finset V) (hconn : J.Connected)
    (c : (J.induce (↑(Pᶜ) : Set V)).ConnectedComponent) :
    ∀ d : (J.induce (↑((componentVertexSet J P c)ᶜ) : Set V)).ConnectedComponent,
      ∃ v : {x : V // x ∈ (↑((componentVertexSet J P c)ᶜ) : Set V)},
        v ∈ d.supp ∧ v.1 ∈ P := by
  classical
  let Q := J.induce (↑(Pᶜ) : Set V)
  let H := componentVertexSet J P c
  let Hcomp := J.induce (↑(Hᶜ) : Set V)
  let root := Classical.choose c.nonempty_supp
  have hroot : root ∈ c.supp := Classical.choose_spec c.nonempty_supp
  have hrootH : root.1 ∈ H := by
    change root.1 ∈ Finset.univ.filter fun v : V =>
      ∃ x : {y : V // y ∈ (↑(Pᶜ) : Set V)}, x ∈ c.supp ∧ x.1 = v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨root, hroot, rfl⟩
  have hHdisjoint : ∀ v, v ∈ H → v ∉ P := by
    intro v hv
    change v ∈ Finset.univ.filter fun v : V =>
      ∃ x : {y : V // y ∈ (↑(Pᶜ) : Set V)}, x ∈ c.supp ∧ x.1 = v at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    have hxP : x.1 ∉ P := Finset.mem_compl.mp x.2
    have : x.1 = v := hxv
    simpa [this] using hxP
  intro d
  obtain ⟨x, hx⟩ := d.nonempty_supp
  have hxH : x.1 ∉ H := by
    simpa using x.2
  have hxRoot : x.1 ∉ (↑H : Set V) := by simpa using hxH
  have hrootSet : root.1 ∈ (↑H : Set V) := hrootH
  obtain ⟨p⟩ := hconn x.1 root.1
  obtain ⟨a, b, q, ha, hb, hab, hq⟩ :=
    walk_first_entry J H p hxRoot hrootSet
  have hqSupport : ∀ z ∈ q.support, z ∈ (↑(Hᶜ) : Set V) := by
    intro z hz
    exact Finset.mem_compl.mpr (hq z hz)
  have haOutside : a ∈ (↑Hᶜ : Set V) := Finset.mem_compl.mpr ha
  have hxOutside : x.1 ∈ (↑Hᶜ : Set V) := x.2
  letI : DecidableRel Hcomp.Adj := Classical.decRel _
  have q' := walk_lift_to_induce J (↑Hᶜ : Set V) q hxOutside haOutside hqSupport
  have hda : Hcomp.connectedComponentMk ⟨a, haOutside⟩ = d := by
    have hdx : Hcomp.connectedComponentMk x = d :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff d x).mp hx
    have hrch : Hcomp.Reachable x ⟨a, haOutside⟩ := q'.reachable
    have hxa : Hcomp.connectedComponentMk x =
        Hcomp.connectedComponentMk ⟨a, haOutside⟩ :=
      SimpleGraph.ConnectedComponent.sound hrch
    exact hxa.symm.trans hdx
  have haD : (⟨a, haOutside⟩ : {z : V // z ∈ (↑Hᶜ : Set V)}) ∈ d.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff d ⟨a, haOutside⟩).mpr hda
  have haP : a ∈ P := by
    by_contra hnaP
    have hbP : b ∉ P := hHdisjoint b hb
    let aQ : {z : V // z ∈ (↑Pᶜ : Set V)} := ⟨a, Finset.mem_compl.mpr hnaP⟩
    let bQ : {z : V // z ∈ (↑Pᶜ : Set V)} := ⟨b, Finset.mem_compl.mpr hbP⟩
    have hQadj : Q.Adj aQ bQ := hab
    have hbC : Q.connectedComponentMk bQ = c := by
      have hbH : ∃ y : {z : V // z ∈ (↑(Pᶜ) : Set V)},
          y ∈ c.supp ∧ y.1 = b := by
        change b ∈ Finset.univ.filter fun v : V =>
          ∃ y : {z : V // z ∈ (↑(Pᶜ) : Set V)}, y ∈ c.supp ∧ y.1 = v at hb
        simpa using hb
      obtain ⟨y, hyC, hyb⟩ := hbH
      have hyEq : y.1 = b := hyb
      have hyQ : y = bQ := by
        apply Subtype.ext
        exact hyEq
      rw [hyQ] at hyC
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff c bQ).mp hyC
    have haC : Q.connectedComponentMk aQ = c := by
      have hsame : Q.connectedComponentMk aQ = Q.connectedComponentMk bQ :=
        SimpleGraph.ConnectedComponent.sound hQadj.reachable
      exact hsame.trans hbC
    have haH : a ∈ H := by
      change a ∈ Finset.univ.filter fun v : V =>
        ∃ y : {z : V // z ∈ (↑(Pᶜ) : Set V)}, y ∈ c.supp ∧ y.1 = v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨aQ, (SimpleGraph.ConnectedComponent.mem_supp_iff c aQ).mpr haC, rfl⟩
    exact ha (by simpa using haH)
  exact ⟨⟨a, haOutside⟩, haD, haP⟩

/-- The root vertex set is disjoint from the protected set. -/
theorem componentVertexSet_disjoint
    (J : SimpleGraph V) (P : Finset V)
    (c : (J.induce (↑(Pᶜ) : Set V)).ConnectedComponent) :
    Disjoint (componentVertexSet J P c) P := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvH hvP
  change v ∈ Finset.univ.filter fun v : V =>
    ∃ x : {y : V // y ∈ (↑(Pᶜ) : Set V)}, x ∈ c.supp ∧ x.1 = v at hvH
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvH
  obtain ⟨x, _, hxv⟩ := hvH
  have hxP : x.1 ∉ P := Finset.mem_compl.mp x.2
  exact hxP (hxv ▸ hvP)

/-- The number of components of the graph induced by `Hᶜ` is at most the
number induced by `S`, provided `S ⊆ Hᶜ` and every exterior component meets
`S`. -/
theorem component_card_le_of_every_component_meets
    (J : SimpleGraph V) (H S : Finset V)
    [Fintype (J.induce (↑(Hᶜ) : Set V)).ConnectedComponent]
    [Fintype (J.induce (↑S : Set V)).ConnectedComponent]
    (hS : ∀ v, v ∈ S → v ∉ H)
    (hmeets : ∀ c : (J.induce (↑(Hᶜ) : Set V)).ConnectedComponent,
      ∃ v : {x : V // x ∈ (↑(Hᶜ) : Set V)}, v ∈ c.supp ∧ v.1 ∈ S) :
    Fintype.card (J.induce (↑(Hᶜ) : Set V)).ConnectedComponent ≤
      Fintype.card (J.induce (↑S : Set V)).ConnectedComponent := by
  classical
  let E := J.induce (↑(Hᶜ) : Set V)
  let Sg := J.induce (↑S : Set V)
  let incl : Sg →g E := {
    toFun := fun v => ⟨v.1, Finset.mem_compl.mpr (hS v.1 v.2)⟩
    map_rel' := by intro _ _ hadj; exact hadj }
  let hit (c : E.ConnectedComponent) :
      {v : V // v ∈ (↑(Hᶜ) : Set V)} := Classical.choose (hmeets c)
  have hit_mem (c : E.ConnectedComponent) : hit c ∈ c.supp ∧ (hit c).1 ∈ S :=
    Classical.choose_spec (hmeets c)
  let f (c : E.ConnectedComponent) : Sg.ConnectedComponent :=
    Sg.connectedComponentMk ⟨(hit c).1, (hit_mem c).2⟩
  have hf : Function.Injective f := by
    intro c d hcd
    let vc : {x : V // x ∈ (↑S : Set V)} := ⟨(hit c).1, (hit_mem c).2⟩
    let vd : {x : V // x ∈ (↑S : Set V)} := ⟨(hit d).1, (hit_mem d).2⟩
    have hp : Sg.Reachable vc vd :=
      SimpleGraph.ConnectedComponent.exact (by simpa [f, vc, vd] using hcd)
    obtain ⟨p⟩ := hp
    have hext : E.Reachable (incl vc) (incl vd) := by
      simpa [incl, vc, vd, E, Sg] using (p.map incl).reachable
    have hcc : E.connectedComponentMk (incl vc) = E.connectedComponentMk (incl vd) :=
      SimpleGraph.ConnectedComponent.sound hext
    have hcv : E.connectedComponentMk (incl vc) = c := by
      have h := (SimpleGraph.ConnectedComponent.mem_supp_iff c (hit c)).mp
        (hit_mem c).1
      simpa [incl, vc] using h
    have hdv : E.connectedComponentMk (incl vd) = d := by
      have h := (SimpleGraph.ConnectedComponent.mem_supp_iff d (hit d)).mp
        (hit_mem d).1
      simpa [incl, vd] using h
    exact hcv.symm.trans (hcc.trans hdv)
  exact Fintype.card_le_of_injective f hf

/-- For a connected auxiliary graph, deleting one component of the outside
of a protected set leaves at most one exterior component per protected-set
component. -/
theorem exteriorComponentCount_le_protected_of_outside_component
    (Γ : Erdos1016.FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected)
    (c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent) :
    exteriorComponentCount Γ (componentVertexSet Γ.toSimpleGraph P c) ≤
      Fintype.card
        (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent := by
  classical
  let H := componentVertexSet Γ.toSimpleGraph P c
  letI : Fintype
      (Γ.toSimpleGraph.induce (↑(Hᶜ) : Set Γ.Vertex)).ConnectedComponent :=
        SimpleGraph.instFintypeConnectedComponent _
  letI : Fintype
      (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent :=
        SetLike.instFintype
  unfold exteriorComponentCount
  apply component_card_le_of_every_component_meets
    Γ.toSimpleGraph H P ?_ ?_
  · intro v hvP
    intro hvH
    exact (Finset.disjoint_left.mp
      (componentVertexSet_disjoint Γ.toSimpleGraph P c) hvH) hvP
  · exact every_exterior_component_meets_protected
      Γ.toSimpleGraph P hconn c







end Erdos1016.Proof.ProtectedExteriorComponents

end

import Erdos1016.Cleanup.Root.ComponentExtraction

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.OutsideBoundaryCharging

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.ProtectedExteriorComponents
open SimpleGraph

variable {Γ : FiniteMultiGraph} {P : Finset Γ.Vertex}

private theorem walk_first_entry
    (J : SimpleGraph Γ.Vertex) (S : Finset Γ.Vertex) {u v : Γ.Vertex}
    (p : J.Walk u v) (hu : u ∉ S) (hv : v ∈ S) :
    ∃ (a b : Γ.Vertex) (q : J.Walk u a), a ∉ S ∧ b ∈ S ∧ J.Adj a b ∧
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
    (J : SimpleGraph Γ.Vertex) (S : Set Γ.Vertex) {u v : Γ.Vertex}
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
      have hadj : (J.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
        simpa using hab
      exact .cons hadj (ih hb hv htail)

/-- Every component outside a proper protected set has at least one boundary
edge back to that set. -/
theorem exists_boundary_edge_for_outside_component
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (c : OutsideComponent Γ P) :
    ∃ e ∈ cutEdges Γ P, ∃ v ∈ outsideComponentVertices Γ P c,
      ((Γ.src e = v ∧ Γ.dst e ∈ P) ∨ (Γ.dst e = v ∧ Γ.src e ∈ P)) := by
  classical
  obtain ⟨x, hx⟩ := c.nonempty_supp
  obtain ⟨pV, hpV⟩ := hP
  have hxP : x.1 ∉ P := Finset.mem_compl.mp x.2
  obtain ⟨path⟩ := hconn x.1 pV
  obtain ⟨a, b, q, haP, hbP, hab, hqP⟩ :=
    walk_first_entry Γ.toSimpleGraph P path hxP hpV
  let aQ : {z : Γ.Vertex // z ∈ (↑(Pᶜ) : Set Γ.Vertex)} :=
    ⟨a, Finset.mem_compl.mpr haP⟩
  have hqSupport : ∀ z ∈ q.support, z ∈ (↑(Pᶜ) : Set Γ.Vertex) := by
    intro z hz
    exact Finset.mem_compl.mpr (hqP z hz)
  have q' := walk_lift_to_induce Γ.toSimpleGraph (↑(Pᶜ) : Set Γ.Vertex)
    q x.2 aQ.2 hqSupport
  have haC : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk aQ = c := by
    have hxC : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk x = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
    have hxa : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk x =
        (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk aQ :=
      SimpleGraph.ConnectedComponent.sound q'.reachable
    exact hxa.symm.trans hxC
  have hav : a ∈ outsideComponentVertices Γ P c := by
    change a ∈ Finset.univ.filter fun z =>
      ∃ y : {w : Γ.Vertex // w ∈ (↑(Pᶜ) : Set Γ.Vertex)}, y ∈ c.supp ∧ y.1 = z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨aQ, (SimpleGraph.ConnectedComponent.mem_supp_iff c aQ).mpr haC, rfl⟩
  rcases hab with ⟨hne, e, horient⟩
  rcases horient with ⟨hsa, hdb⟩ | ⟨hsb, hda⟩
  · have hsrcP : Γ.src e ∉ P := by
      intro hs
      exact haP (hsa ▸ hs)
    have hdstP : Γ.dst e ∈ P := hdb ▸ hbP
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hsrcP, hdstP⟩⟩,
      a, hav, Or.inl ⟨hsa, hdstP⟩⟩
  · have hsrcP : Γ.src e ∈ P := hsb ▸ hbP
    have hdstP : Γ.dst e ∉ P := by
      intro ht
      exact haP (hda ▸ ht)
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hsrcP, hdstP⟩⟩,
      a, hav, Or.inr ⟨hda, hsrcP⟩⟩

/-- Membership in the flattened outside-component vertex set recovers the
corresponding connected-component class. -/
private theorem outside_vertex_component
    (c : OutsideComponent Γ P) {v : Γ.Vertex}
    (hvNotP : v ∉ P)
    (hv : v ∈ outsideComponentVertices Γ P c) :
    (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk
      ⟨v, Finset.mem_compl.mpr hvNotP⟩ = c := by
  classical
  unfold outsideComponentVertices componentVertexSet at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  have hEq : y = ⟨v, Finset.mem_compl.mpr hvNotP⟩ := by
    apply Subtype.ext
    exact hyv
  rw [← hEq]
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mp hy

/-- An edge leaving one component of the induced complement cannot reach a
different complement component; its other endpoint must lie in P. -/
theorem outside_component_cut_subset_protected_cut
    (c : OutsideComponent Γ P) :
    cutEdges Γ (outsideComponentVertices Γ P c) ⊆ cutEdges Γ P := by
  classical
  intro e he
  have he' := Finset.mem_filter.mp he
  rcases he'.2 with ⟨hsH, htH⟩ | ⟨hsH, htH⟩
  · have hsNotP : Γ.src e ∉ P := by
      intro h
      exact (Finset.disjoint_left.mp
        (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hsH h
    have htP : Γ.dst e ∈ P := by
      by_contra htNotP
      have hne : Γ.src e ≠ Γ.dst e := by
        intro hEq
        apply htH
        simpa [hEq] using hsH
      let u : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)} :=
        ⟨Γ.src e, Finset.mem_compl.mpr hsNotP⟩
      let v : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)} :=
        ⟨Γ.dst e, Finset.mem_compl.mpr htNotP⟩
      have hadj : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).Adj u v := by
        refine ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
      have hcc := SimpleGraph.ConnectedComponent.sound hadj.reachable
      have hucc := outside_vertex_component c hsNotP hsH
      have hvcc : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk v = c :=
        hcc.symm.trans hucc
      have hvSupp := (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr hvcc
      have hdstH : Γ.dst e ∈ outsideComponentVertices Γ P c := by
        change Γ.dst e ∈ Finset.univ.filter _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨v, hvSupp, rfl⟩
      exact htH hdstH
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hsNotP, htP⟩⟩
  · have htNotP : Γ.dst e ∉ P := by
      intro h
      exact (Finset.disjoint_left.mp
        (componentVertexSet_disjoint Γ.toSimpleGraph P c)) htH h
    have hsP : Γ.src e ∈ P := by
      by_contra hsNotP
      have hne : Γ.src e ≠ Γ.dst e := by
        intro hEq
        apply hsH
        simpa [hEq] using htH
      let u : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)} :=
        ⟨Γ.src e, Finset.mem_compl.mpr hsNotP⟩
      let v : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)} :=
        ⟨Γ.dst e, Finset.mem_compl.mpr htNotP⟩
      have hadj : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).Adj u v := by
        refine ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
      have hcc := SimpleGraph.ConnectedComponent.sound hadj.reachable
      have hvcc := outside_vertex_component c htNotP htH
      have hucc : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk u = c :=
        hcc.trans hvcc
      have huSupp := (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr hucc
      have hsrcH : Γ.src e ∈ outsideComponentVertices Γ P c := by
        change Γ.src e ∈ Finset.univ.filter _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u, huSupp, rfl⟩
      exact hsH hsrcH
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hsP, htNotP⟩⟩

/-- The boundary of an outside component is bounded by the protected cut. -/
theorem outside_component_cut_card_le_protected_cut
    (c : OutsideComponent Γ P) :
    (cutEdges Γ (outsideComponentVertices Γ P c)).card ≤ (cutEdges Γ P).card :=
  Finset.card_le_card (outside_component_cut_subset_protected_cut c)

/-- The number of components outside P is bounded by the number of cut
edges. Components choose distinct crossing labels, since each cut edge has
only one endpoint outside P. -/
theorem outside_component_count_le_cut
    [Fintype (OutsideComponent Γ P)]
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty) :
    Fintype.card (OutsideComponent Γ P) ≤ (cutEdges Γ P).card := by
  classical
  let chooseEdge (c : OutsideComponent Γ P) :=
    Classical.choose (exists_boundary_edge_for_outside_component hconn hP c)
  let f : OutsideComponent Γ P → {e : Γ.Edge // e ∈ cutEdges Γ P} := fun c =>
    ⟨chooseEdge c,
      (Classical.choose_spec (exists_boundary_edge_for_outside_component hconn hP c)).1⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hE : chooseEdge c = chooseEdge d := congrArg Subtype.val hcd
    have hfc := (Classical.choose_spec
      (exists_boundary_edge_for_outside_component hconn hP c)).2
    have hfd := (Classical.choose_spec
      (exists_boundary_edge_for_outside_component hconn hP d)).2
    rcases hfc with ⟨v, hv, hvc⟩
    rcases hfd with ⟨w, hw, hwd⟩
    change (Γ.src (chooseEdge d) = w ∧ Γ.dst (chooseEdge d) ∈ P) ∨
      (Γ.dst (chooseEdge d) = w ∧ Γ.src (chooseEdge d) ∈ P) at hwd
    change (Γ.src (chooseEdge c) = v ∧ Γ.dst (chooseEdge c) ∈ P) ∨
      (Γ.dst (chooseEdge c) = v ∧ Γ.src (chooseEdge c) ∈ P) at hvc
    have hvP : v ∉ P := by
      intro hp
      exact (Finset.disjoint_left.mp
        (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hv hp
    have hwP : w ∉ P := by
      intro hp
      exact (Finset.disjoint_left.mp
        (componentVertexSet_disjoint Γ.toSimpleGraph P d)) hw hp
    rw [← hE] at hwd
    have hvw : v = w := by
      rcases hvc with ⟨hsv, hdt⟩ | ⟨hsb, hda⟩
      · rcases hwd with ⟨hsw, hdt'⟩ | ⟨hdb, hwa⟩
        · exact hsv.symm.trans hsw
        · have hsrcOut : Γ.src (chooseEdge c) ∉ P := by
            intro hs
            exact hvP (hsv ▸ hs)
          exact (hsrcOut hwa).elim
      · rcases hwd with ⟨hsw, hdt'⟩ | ⟨hdb, hwa⟩
        · have hsrcOut : Γ.src (chooseEdge c) ∉ P := by
            intro hs
            exact hwP (hsw ▸ hs)
          exact (hsrcOut hda).elim
        · exact hsb.symm.trans hdb
    have hvcComp := outside_vertex_component c hvP hv
    have hwdComp := outside_vertex_component d hwP hw
    have hsub : (⟨v, Finset.mem_compl.mpr hvP⟩ :
        {z : Γ.Vertex // z ∈ (↑(Pᶜ) : Set Γ.Vertex)}) =
      ⟨w, Finset.mem_compl.mpr hwP⟩ := Subtype.ext hvw
    have hcc := congrArg
      (fun z : {z : Γ.Vertex // z ∈ (↑(Pᶜ) : Set Γ.Vertex)} =>
        (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).connectedComponentMk z) hsub
    exact hvcComp.symm.trans (hcc.trans hwdComp)
  calc
    Fintype.card (OutsideComponent Γ P) ≤ Fintype.card {e : Γ.Edge // e ∈ cutEdges Γ P} :=
      Fintype.card_le_of_injective f hf
    _ = (cutEdges Γ P).card := Fintype.card_coe (cutEdges Γ P)

end Erdos1016.Proof.OutsideBoundaryCharging

end

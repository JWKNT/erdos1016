import Erdos1016.CycleSpace.Support.ActiveRestriction
import Erdos1016.Extremal.Capacity.CompositionProbability

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016

/-- The original edges outside `E` that remain after deleting inactive
coordinates. -/
def originalActiveEdge (G : PhysicalGraph) (e : (activeSubgraph G).Edge) : G.Edge :=
  (G.restrictedEdgeEquiv (activeEdges G) e).1

def activeOutsideEdges (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset (activeSubgraph G).Edge := by
  classical
  exact Finset.univ.filter fun e => originalActiveEdge G e ∉ E

/-- The active-subgraph word corresponding to a host cycle state. -/
def activeWordOfCycle (G : PhysicalGraph) (x : G.CycleSpace) :
    (activeSubgraph G).Word := (cycleSpaceActiveSubgraphEquiv G x).1

theorem activeWordOfCycle_apply (G : PhysicalGraph) (x : G.CycleSpace)
    (e : (activeSubgraph G).Edge) :
    activeWordOfCycle G x e = x.1 (originalActiveEdge G e) := by
  change (((G.restrictPhysicalWordEquiv (activeEdges G)).symm
    (G.restrictWord (activeEdges G) x.1)) e) = x.1 (originalActiveEdge G e)
  rfl

theorem restrictedSelectedGraph_outside_eq_active (G : PhysicalGraph)
    (E : Finset G.Edge) (x : G.CycleSpace) :
    G.restrictedSelectedGraph Eᶜ (G.restrictWord Eᶜ x.1) =
      (activeSubgraph G).restrictedSelectedGraph (activeOutsideEdges G E)
        ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
          (activeWordOfCycle G x)) := by
  classical
  ext u v
  constructor
  · intro h
    change ∃ e : G.RestrictedEdge Eᶜ,
      (G.restrictWord Eᶜ x.1) e ≠ 0 ∧
        ((G.src e.1 = u ∧ G.dst e.1 = v) ∨ (G.src e.1 = v ∧ G.dst e.1 = u)) at h
    rcases h with ⟨e, hx, hed⟩
    have ha : ActiveEdgeUniform.ActiveEdge G e.1 :=
      active_of_cycle_coordinate_ne_zero G x e.1 (by simpa [PhysicalGraph.restrictWord] using hx)
    have hem : e.1 ∈ activeEdges G := (mem_activeEdges_iff G e.1).2 ha
    let ea : (activeSubgraph G).Edge :=
      (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨e.1, hem⟩
    have hea : originalActiveEdge G ea = e.1 := by
      simp [originalActiveEdge, ea, PhysicalGraph.restrictedEdgeEquiv]
    have hout : ea ∈ activeOutsideEdges G E := by
      change ea ∈ Finset.univ.filter (fun z => originalActiveEdge G z ∉ E)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [hea]
        exact Finset.mem_compl.mp e.2⟩
    change ∃ e' : (activeSubgraph G).RestrictedEdge (activeOutsideEdges G E),
      ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
        (activeWordOfCycle G x)) e' ≠ 0 ∧
        (((activeSubgraph G).src e'.1 = u ∧ (activeSubgraph G).dst e'.1 = v) ∨
         ((activeSubgraph G).src e'.1 = v ∧ (activeSubgraph G).dst e'.1 = u))
    refine ⟨⟨ea, hout⟩, ?_, ?_⟩
    · simpa [PhysicalGraph.restrictWord, activeWordOfCycle_apply, hea] using hx
    · have hcoord : (G.restrictedEdgeEquiv (activeEdges G) ea).1 = e.1 := by
        exact congrArg Subtype.val
          ((G.restrictedEdgeEquiv (activeEdges G)).apply_symm_apply ⟨e.1, hem⟩)
      have hsrc : (activeSubgraph G).src ea = G.src e.1 := by
        change G.src (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
        rw [hcoord]
      have hdst : (activeSubgraph G).dst ea = G.dst e.1 := by
        change G.dst (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
        rw [hcoord]
      change ((activeSubgraph G).src ea = u ∧ (activeSubgraph G).dst ea = v) ∨
        ((activeSubgraph G).src ea = v ∧ (activeSubgraph G).dst ea = u)
      rcases hed with h | h
      · exact Or.inl ⟨hsrc.trans h.1, hdst.trans h.2⟩
      · exact Or.inr ⟨hsrc.trans h.1, hdst.trans h.2⟩
  · intro h
    change ∃ e : (activeSubgraph G).RestrictedEdge (activeOutsideEdges G E),
      ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
        (activeWordOfCycle G x)) e ≠ 0 ∧
        (((activeSubgraph G).src e.1 = u ∧ (activeSubgraph G).dst e.1 = v) ∨
         ((activeSubgraph G).src e.1 = v ∧ (activeSubgraph G).dst e.1 = u)) at h
    rcases h with ⟨e, hx, hed⟩
    have hout : originalActiveEdge G e.1 ∉ E := by
      have he := e.2
      simp only [activeOutsideEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at he
      exact he
    let eo : G.RestrictedEdge Eᶜ := ⟨originalActiveEdge G e.1, by simpa using hout⟩
    change ∃ e' : G.RestrictedEdge Eᶜ,
      (G.restrictWord Eᶜ x.1) e' ≠ 0 ∧
        ((G.src e'.1 = u ∧ G.dst e'.1 = v) ∨ (G.src e'.1 = v ∧ G.dst e'.1 = u))
    refine ⟨eo, ?_, ?_⟩
    · simpa [eo, PhysicalGraph.restrictWord, activeWordOfCycle_apply] using hx
    · have hsrc : (activeSubgraph G).src e.1 = G.src eo.1 := by
        change G.src (G.restrictedEdgeEquiv (activeEdges G) e.1).1 = _
        rfl
      have hdst : (activeSubgraph G).dst e.1 = G.dst eo.1 := by
        change G.dst (G.restrictedEdgeEquiv (activeEdges G) e.1).1 = _
        rfl
      change (G.src eo.1 = u ∧ G.dst eo.1 = v) ∨
        (G.src eo.1 = v ∧ G.dst eo.1 = u)
      rcases hed with h | h
      · exact Or.inl ⟨hsrc.symm.trans h.1, hdst.symm.trans h.2⟩
      · exact Or.inr ⟨hsrc.symm.trans h.1, hdst.symm.trans h.2⟩

theorem restrictedSelectedDegree_outside_eq_active (G : PhysicalGraph)
    (E : Finset G.Edge) (x : G.CycleSpace) (v : G.Vertex) :
    G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v =
      (activeSubgraph G).restrictedSelectedDegree (activeOutsideEdges G E)
        ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
          (activeWordOfCycle G x)) v := by
  classical
  let P := Finset.univ.filter fun e : G.RestrictedEdge Eᶜ =>
    x.1 e.1 ≠ 0 ∧ G.incident e.1 v
  let Q := Finset.univ.filter fun e : (activeSubgraph G).RestrictedEdge
      (activeOutsideEdges G E) =>
    activeWordOfCycle G x e.1 ≠ 0 ∧ (activeSubgraph G).incident e.1 v
  let equiv : {e : G.RestrictedEdge Eᶜ // e ∈ P} ≃
      {e : (activeSubgraph G).RestrictedEdge (activeOutsideEdges G E) // e ∈ Q} := {
    toFun := fun a => by
      have hdata := (Finset.mem_filter.mp a.2).2
      have ha : ActiveEdgeUniform.ActiveEdge G a.1.1 :=
        active_of_cycle_coordinate_ne_zero G x a.1.1 hdata.1
      have hem : a.1.1 ∈ activeEdges G := (mem_activeEdges_iff G a.1.1).2 ha
      let ea : (activeSubgraph G).Edge :=
        (G.restrictedEdgeEquiv (activeEdges G)).symm ⟨a.1.1, hem⟩
      have hea : originalActiveEdge G ea = a.1.1 := by
        simp [originalActiveEdge, ea, PhysicalGraph.restrictedEdgeEquiv]
      have hout : ea ∈ activeOutsideEdges G E := by
        change ea ∈ Finset.univ.filter (fun z => originalActiveEdge G z ∉ E)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hea]
          exact Finset.mem_compl.mp a.1.2⟩
      have hsrc : (activeSubgraph G).src ea = G.src a.1.1 := by
        change G.src (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
        rw [congrArg Subtype.val
          ((G.restrictedEdgeEquiv (activeEdges G)).apply_symm_apply ⟨a.1.1, hem⟩)]
      have hdst : (activeSubgraph G).dst ea = G.dst a.1.1 := by
        change G.dst (G.restrictedEdgeEquiv (activeEdges G) ea).1 = _
        rw [congrArg Subtype.val
          ((G.restrictedEdgeEquiv (activeEdges G)).apply_symm_apply ⟨a.1.1, hem⟩)]
      refine ⟨⟨ea, hout⟩, ?_⟩
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rw [activeWordOfCycle_apply, hea]
        exact hdata.1
      · rcases hdata.2 with hs | hd
        · exact Or.inl (hsrc.trans hs)
        · exact Or.inr (hdst.trans hd)
    invFun := fun a => by
      have hdata := (Finset.mem_filter.mp a.2).2
      have hout : originalActiveEdge G a.1.1 ∉ E := by
        have hf := a.1.2
        simp only [activeOutsideEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hf
        exact hf
      let eo : G.RestrictedEdge Eᶜ :=
        ⟨originalActiveEdge G a.1.1, Finset.mem_compl.mpr hout⟩
      have hsrc : (activeSubgraph G).src a.1.1 = G.src eo.1 := by
        change G.src (G.restrictedEdgeEquiv (activeEdges G) a.1.1).1 = _
        rfl
      have hdst : (activeSubgraph G).dst a.1.1 = G.dst eo.1 := by
        change G.dst (G.restrictedEdgeEquiv (activeEdges G) a.1.1).1 = _
        rfl
      refine ⟨eo, ?_⟩
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rw [← activeWordOfCycle_apply]
        exact hdata.1
      · rcases hdata.2 with hs | hd
        · exact Or.inl (hsrc.symm.trans hs)
        · exact Or.inr (hdst.symm.trans hd)
    left_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      simp [originalActiveEdge, PhysicalGraph.restrictedEdgeEquiv]
    right_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      simp [originalActiveEdge, PhysicalGraph.restrictedEdgeEquiv] }
  unfold PhysicalGraph.restrictedSelectedDegree
  change P.card = Q.card
  calc
    P.card = Fintype.card {e // e ∈ P} := (Fintype.card_coe P).symm
    _ = Fintype.card {e // e ∈ Q} := Fintype.card_congr equiv
    _ = Q.card := Fintype.card_coe Q

theorem outsideLinearForest_iff_active (G : PhysicalGraph) (E : Finset G.Edge)
    (x : G.CycleSpace) :
    G.IsRestrictedLinearForest Eᶜ (G.restrictWord Eᶜ x.1) ↔
      (activeSubgraph G).IsRestrictedLinearForest (activeOutsideEdges G E)
        ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
          (activeWordOfCycle G x)) := by
  unfold PhysicalGraph.IsRestrictedLinearForest
  rw [restrictedSelectedGraph_outside_eq_active]
  constructor
  · rintro ⟨hacyclic, hdegree⟩
    refine ⟨hacyclic, ?_⟩
    intro v
    rw [← restrictedSelectedDegree_outside_eq_active G E x v]
    exact hdegree v
  · rintro ⟨hacyclic, hdegree⟩
    refine ⟨hacyclic, ?_⟩
    intro v
    rw [restrictedSelectedDegree_outside_eq_active G E x v]
    exact hdegree v

theorem outsideLinearForestStates_mem_iff_active (G : PhysicalGraph)
    (E : Finset G.Edge) (x : G.CycleSpace) :
    x ∈ G.outsideLinearForestStates E ↔
      (activeSubgraph G).IsRestrictedLinearForest (activeOutsideEdges G E)
        ((activeSubgraph G).restrictWord (activeOutsideEdges G E)
          (activeWordOfCycle G x)) := by
  simp [PhysicalGraph.outsideLinearForestStates,
    outsideLinearForest_iff_active]


end Erdos1016.Proof.ActivePhysicalComponents

end

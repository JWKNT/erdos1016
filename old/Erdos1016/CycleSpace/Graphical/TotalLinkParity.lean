import Erdos1016.CycleSpace.Graphical.ComponentCutParity

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalLinkTotalParity

open Erdos1016
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalComponentCutParity
open Erdos1016.Proof.GraphicalCommonInformation

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Summing the attachment parities over every component of the two-vertex
deletion counts exactly the u-incident edges whose other endpoint is not v. -/
theorem sum_all_componentCutParity_eq_awayStar (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.Word) :
    (∑ c : (deletedGraph G u v).ConnectedComponent,
      componentCutParity G u v c u x) =
    ∑ e : G.Edge,
      if (G.src e = u ∧ G.dst e ≠ v) ∨ (G.dst e = u ∧ G.src e ≠ v)
      then x e else 0 := by
  classical
  simp only [componentCutParity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e = u
  · have hdstu : G.dst e ≠ u := by
      intro h
      exact G.noLoops e (hs.trans h.symm)
    by_cases hdv : G.dst e = v
    · have hzero : ∀ c : (deletedGraph G u v).ConnectedComponent,
          componentCutAt G u v c u e = False := by
        intro c
        simp [componentCutAt, componentVertexSet, hs, hdv, hdstu,
          G.noLoops e]
      have hterms (c : (deletedGraph G u v).ConnectedComponent) :
          (if componentCutAt G u v c u e then x e else 0) = 0 := by
        simp [hzero c]
      simp [hzero, hdv, hs, hdstu, hne, hne.symm]
    · have hd : G.dst e ≠ u ∧ G.dst e ≠ v := ⟨hdstu, hdv⟩
      let y : DeletedVertex G u v := ⟨G.dst e, hd⟩
      let c₀ := (deletedGraph G u v).connectedComponentMk y
      have hcut (c : (deletedGraph G u v).ConnectedComponent) :
          componentCutAt G u v c u e ↔ c = c₀ := by
        constructor
        · intro hc
          rcases hc with ⟨hsrc, hmem⟩ | ⟨hdst, hmem⟩
          · have : G.dst e ∈ componentVertexSet G u v c := hmem
            simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ,
              true_and] at this
            obtain ⟨hy, hcomp⟩ := this
            have hy' : y = ⟨G.dst e, hy⟩ := Subtype.ext rfl
            dsimp [c₀]
            exact hcomp.symm.trans (congrArg
              (fun z : DeletedVertex G u v =>
                (deletedGraph G u v).connectedComponentMk z) hy')
          · exact (G.noLoops e (hs.trans hdst.symm)).elim
        · intro hc
          left
          refine ⟨hs, ?_⟩
          subst c
          simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ,
            true_and]
          refine ⟨hd, ?_⟩
          dsimp [c₀]
      have hsum :
          (∑ c : (deletedGraph G u v).ConnectedComponent,
            if componentCutAt G u v c u e then x e else 0) = x e := by
        simp_rw [hcut]
        simp
      simpa [hs, hdv] using hsum
  · by_cases ht : G.dst e = u
    · have hsrcu : G.src e ≠ u := hs
      by_cases hsrcv : G.src e = v
      · have hzero (c : (deletedGraph G u v).ConnectedComponent) :
            ¬ componentCutAt G u v c u e := by
          intro hc
          rcases hc with ⟨hsrc, _⟩ | ⟨hdst, hmem⟩
          · exact hs hsrc
          · have hv : v ∈ componentVertexSet G u v c := by
              simpa [hsrcv] using hmem
            obtain ⟨h, _⟩ := componentVertices_spec G u v c hv
            exact h.2 rfl
        simp [componentCutParity, hzero, hs, ht, hsrcv, hne, hne.symm]
      · have hd : G.src e ≠ u ∧ G.src e ≠ v := ⟨hsrcu, hsrcv⟩
        let y : DeletedVertex G u v := ⟨G.src e, hd⟩
        let c₀ := (deletedGraph G u v).connectedComponentMk y
        have hcut (c : (deletedGraph G u v).ConnectedComponent) :
            componentCutAt G u v c u e ↔ c = c₀ := by
          constructor
          · intro hc
            rcases hc with ⟨hsrc, hmem⟩ | ⟨hdst, hmem⟩
            · exact (G.noLoops e (hsrc.trans ht.symm)).elim
            · have : G.src e ∈ componentVertexSet G u v c := hmem
              simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ,
                true_and] at this
              obtain ⟨hy, hcomp⟩ := this
              have hy' : y = ⟨G.src e, hy⟩ := Subtype.ext rfl
              dsimp [c₀]
              exact hcomp.symm.trans (congrArg
                (fun z : DeletedVertex G u v =>
                  (deletedGraph G u v).connectedComponentMk z) hy')
          · intro hc
            right
            refine ⟨ht, ?_⟩
            subst c
            simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ,
              true_and]
            refine ⟨hd, ?_⟩
            dsimp [c₀]
        have hsum :
            (∑ c : (deletedGraph G u v).ConnectedComponent,
              if componentCutAt G u v c u e then x e else 0) = x e := by
          simp_rw [hcut]
          simp
        simpa [componentCutParity, hs, ht, hsrcv] using hsum
    · have hnone (c : (deletedGraph G u v).ConnectedComponent) :
          ¬ componentCutAt G u v c u e := by
        intro hc
        rcases hc with ⟨hsrc, _⟩ | ⟨hdst, _⟩
        · exact hs hsrc
        · exact ht hdst
      simp [componentCutParity, hnone, hs, ht]

/-- The direct `u-v` edges and all other u-incident edges partition the star
at `u`. -/
theorem directEdgeSum_add_awayStar_eq_incidentSum (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.Word) :
    (∑ e : G.Edge,
      if (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
      then x e else 0) +
      (∑ e : G.Edge,
        if (G.src e = u ∧ G.dst e ≠ v) ∨ (G.dst e = u ∧ G.src e ≠ v)
        then x e else 0) =
      ∑ e : G.Edge, if G.incident e u then x e else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e = u
  · have htu : G.dst e ≠ u := by
      intro h
      exact G.noLoops e (hs.trans h.symm)
    by_cases htv : G.dst e = v
    · simp [PhysicalGraph.incident, hs, htu, htv, hne, hne.symm]
    · simp [PhysicalGraph.incident, hs, htu, htv, hne, hne.symm]
  · by_cases ht : G.dst e = u
    · by_cases hsV : G.src e = v
      · simp [PhysicalGraph.incident, hs, ht, hsV, hne, hne.symm]
      · simp [PhysicalGraph.incident, hs, ht, hsV, hne, hne.symm]
    · simp [PhysicalGraph.incident, hs, ht]

/-- The total direct-edge parity and all-component attachment parity vanish
on a cycle. -/
theorem allComponent_and_directParity_eq_zero (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace) :
    (∑ e : G.Edge,
      if (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
      then x.1 e else 0) +
      (∑ c : (deletedGraph G u v).ConnectedComponent,
        componentCutParity G u v c u x.1) = 0 := by
  have hstar : (∑ e : G.Edge, if G.incident e u then x.1 e else 0) = 0 := by
    calc
      (∑ e : G.Edge, if G.incident e u then x.1 e else 0) =
          ∑ e : G.Edge,
            ((if G.src e = u then x.1 e else 0) +
              (if G.dst e = u then x.1 e else 0)) := by
            apply Finset.sum_congr rfl
            intro e he
            have hterm : (if G.incident e u then x.1 e else 0) =
                (if G.src e = u then x.1 e else 0) +
                  (if G.dst e = u then x.1 e else 0) := by
              by_cases hs : G.src e = u
              · have ht : G.dst e ≠ u := by
                  intro h
                  exact G.noLoops e (hs.trans h.symm)
                simp [PhysicalGraph.incident, hs, ht]
              · by_cases ht : G.dst e = u
                · simp [PhysicalGraph.incident, hs, ht]
                · simp [PhysicalGraph.incident, hs, ht]
            exact hterm
      _ = G.boundary x.1 u := rfl
      _ = 0 := by
        have hx : G.boundary x.1 = 0 := x.2
        exact congrFun hx u
  rw [← directEdgeSum_add_awayStar_eq_incidentSum G u v hne x.1] at hstar
  rw [sum_all_componentCutParity_eq_awayStar G u v hne x.1]
  exact hstar

/-- On a cycle, components attached at `u` but not at `v` contribute zero;
therefore summing over all components is the same as summing over the
two-sided component links. -/
theorem sum_componentLinks_eq_sum_all_components (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (x : G.CycleSpace) :
    (∑ c : ComponentLink G u v,
      componentCutParity G u v c.1 u x.1) =
    ∑ c : (deletedGraph G u v).ConnectedComponent,
      componentCutParity G u v c u x.1 := by
  classical
  let p : (deletedGraph G u v).ConnectedComponent → Prop :=
    fun c => componentAttachedAt G u v u c ∧ componentAttachedAt G u v v c
  let f : (deletedGraph G u v).ConnectedComponent → F₂ :=
    fun c => componentCutParity G u v c u x.1
  have hcompl : (∑ c : {c : (deletedGraph G u v).ConnectedComponent // ¬ p c},
      f c.1) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hp := c.2
    dsimp [p] at hp
    by_cases hu : componentAttachedAt G u v u c.1
    · have hv : ¬ componentAttachedAt G u v v c.1 := by
        intro hv
        exact hp ⟨hu, hv⟩
      simpa [f] using componentCutParity_zero_of_no_v_attachment
        G u v hne c.1 x hv
    · simpa [f] using componentCutParity_zero_of_no_attachment
        G u v u c.1 x.1 hu
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  have hsubtype :
      (∑ c : {c : (deletedGraph G u v).ConnectedComponent // p c}, f c.1) =
        ∑ c : ComponentLink G u v,
          componentCutParity G u v c.1 u x.1 := by
    change (∑ c : {c : (deletedGraph G u v).ConnectedComponent //
        componentAttachedAt G u v u c ∧ componentAttachedAt G u v v c},
        componentCutParity G u v c.1 u x.1) = _
    rfl
  calc
    (∑ c : ComponentLink G u v, componentCutParity G u v c.1 u x.1) =
        ∑ c : {c : (deletedGraph G u v).ConnectedComponent // p c}, f c.1 :=
          hsubtype.symm
    _ = ∑ c : (deletedGraph G u v).ConnectedComponent, f c := by
          rw [← hsplit]
          simp [hcompl]
    _ = ∑ c : (deletedGraph G u v).ConnectedComponent,
        componentCutParity G u v c u x.1 := rfl

/-- Every cycle maps to an even assignment on the actual link coordinates. -/
theorem linkMap_totalParity_eq_zero (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace) :
    ∑ i : LinkIndex G u v, linkMap G u v x i = 0 := by
  classical
  change (∑ i : DirectLink G u v ⊕ ComponentLink G u v,
      linkMap G u v x i) = 0
  rw [Fintype.sum_sum_type]
  have hdirect :
      (∑ d : DirectLink G u v, linkMap G u v x (Sum.inl d)) =
        ∑ e : G.Edge,
          if (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
          then x.1 e else 0 := by
    change (∑ d : {e : G.Edge //
        (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)},
          x.1 d.1) = _
    have hsplit := Fintype.sum_subtype_add_sum_subtype
      (fun e : G.Edge => (G.src e = u ∧ G.dst e = v) ∨
        (G.src e = v ∧ G.dst e = u))
      (fun e => if (G.src e = u ∧ G.dst e = v) ∨
        (G.src e = v ∧ G.dst e = u) then x.1 e else 0)
    let p : G.Edge → Prop := fun e =>
      (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)
    have hfirst : (∑ d : {e : G.Edge // p e},
        if p d.1 then x.1 d.1 else 0) = ∑ d : {e : G.Edge // p e}, x.1 d.1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [p, d.2]
    have hsecond : (∑ d : {e : G.Edge // ¬ p e},
        if p d.1 then x.1 d.1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp [p, d.2]
    rw [hfirst, hsecond] at hsplit
    simpa using hsplit
  have hcomponents := sum_componentLinks_eq_sum_all_components G u v hne x
  have hcomponents' :
      (∑ c : ComponentLink G u v, linkMap G u v x (Sum.inr c)) =
        ∑ c : (deletedGraph G u v).ConnectedComponent,
          componentCutParity G u v c u x.1 := by
    simpa [GraphicalLinkMap.linkMap_apply, GraphicalLinkMap.linkCoordinate,
      componentCutParity, componentCutCondition] using hcomponents
  rw [hdirect, hcomponents']
  exact allComponent_and_directParity_eq_zero G u v hne x

end Erdos1016.Proof.GraphicalLinkTotalParity

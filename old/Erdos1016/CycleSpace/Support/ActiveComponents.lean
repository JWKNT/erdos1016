import Erdos1016.Probability.Cylinders.ActiveCoordinateUniformity
import Erdos1016.Extremal.Capacity.RestrictedPhysical

set_option autoImplicit false

/-!
# Active components of a physical graph

Every cycle-space word is supported on the edges active in the global cycle
space. This first reduction removes bridge coordinates exactly and makes the
remaining connected components the candidate factors for Section 10.
-/

noncomputable section

namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016

local notation "F₂" => ZMod 2

/-- The active edges, namely those used by at least one global cycle word. -/
def activeEdges (G : PhysicalGraph) : Finset G.Edge := by
  classical
  exact Finset.univ.filter (ActiveEdgeUniform.ActiveEdge G)

/-- The physical subgraph supported on globally active coordinates. -/
def activeSubgraph (G : PhysicalGraph) : PhysicalGraph :=
  G.restrictPhysical (activeEdges G)

/-- Active connected components are the components after deleting the
globally inactive (bridge) coordinates. -/
abbrev ActiveComponent (G : PhysicalGraph) :=
  (activeSubgraph G).toSimpleGraph.ConnectedComponent

noncomputable instance activeComponentFintype (G : PhysicalGraph) :
    Fintype (ActiveComponent G) := Fintype.ofFinite _

theorem mem_activeEdges_iff (G : PhysicalGraph) (e : G.Edge) :
    e ∈ activeEdges G ↔ ActiveEdgeUniform.ActiveEdge G e := by
  classical
  simp [activeEdges]

/-- Any nonzero cycle-space coordinate witnesses that the edge is active. -/
theorem active_of_cycle_coordinate_ne_zero (G : PhysicalGraph)
    (x : G.CycleSpace) (e : G.Edge) (hx : x.1 e ≠ 0) :
    ActiveEdgeUniform.ActiveEdge G e := by
  refine ⟨x, ?_⟩
  generalize hval : x.1 e = z
  have hz : z ≠ 0 := by rw [← hval]; exact hx
  fin_cases z <;> simp_all

/-- Every global cycle word vanishes on globally inactive coordinates. -/
theorem cycle_coordinate_eq_zero_of_inactive (G : PhysicalGraph)
    (x : G.CycleSpace) (e : G.Edge)
    (hInactive : ¬ ActiveEdgeUniform.ActiveEdge G e) :
    x.1 e = 0 := by
  by_contra hne
  exact hInactive (active_of_cycle_coordinate_ne_zero G x e hne)

/-- The component containing a vertex after inactive coordinates are deleted. -/
def componentOf (G : PhysicalGraph) (v : (activeSubgraph G).Vertex) :
    ActiveComponent G :=
  (activeSubgraph G).toSimpleGraph.connectedComponentMk v

/-- Each active edge is assigned to the component containing its source. -/
def edgeComponent (G : PhysicalGraph) (e : (activeSubgraph G).Edge) :
    ActiveComponent G :=
  componentOf G ((activeSubgraph G).src e)

/-- Both endpoints of an active edge lie in its assigned component. -/
theorem edgeComponent_eq_dst (G : PhysicalGraph)
    (e : (activeSubgraph G).Edge) :
    edgeComponent G e = componentOf G ((activeSubgraph G).dst e) := by
  unfold edgeComponent componentOf
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

/-- The active-edge subset belonging to one connected component. -/
def componentEdges (G : PhysicalGraph) (c : ActiveComponent G) :
    Finset (activeSubgraph G).Edge := by
  classical
  exact Finset.univ.filter fun e => edgeComponent G e = c

/-- Keep only the edges of a chosen finite set that lie in one active
component. -/
def componentPart (G : PhysicalGraph) (F : Finset (activeSubgraph G).Edge)
    (c : ActiveComponent G) : Finset (activeSubgraph G).Edge := by
  classical
  exact F.filter fun e => edgeComponent G e = c

theorem mem_componentPart_iff (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (e : (activeSubgraph G).Edge) :
    e ∈ componentPart G F c ↔ e ∈ F ∧ edgeComponent G e = c := by
  classical
  simp [componentPart]



/-- Endpoints of every active-subgraph edge have the same component label. -/
theorem componentOf_src_eq_dst (G : PhysicalGraph)
    (e : (activeSubgraph G).Edge) :
    componentOf G ((activeSubgraph G).src e) =
      componentOf G ((activeSubgraph G).dst e) :=
  edgeComponent_eq_dst G e







/-- The selected graph using only the portion of an edge set in one active
component. -/
def componentRestrictedSelectedGraph (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (x : (activeSubgraph G).Word) : SimpleGraph (activeSubgraph G).Vertex :=
  (activeSubgraph G).restrictedSelectedGraph (componentPart G F c)
    ((activeSubgraph G).restrictWord (componentPart G F c) x)

/-- An edge of a restricted selected graph whose source component is `c` is
present in that component's restricted selected graph. -/
theorem restrictedAdj_to_component (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (x : (activeSubgraph G).Word) {u v : (activeSubgraph G).Vertex}
    (hu : componentOf G u = c)
    (h : ((activeSubgraph G).restrictedSelectedGraph F
      ((activeSubgraph G).restrictWord F x)).Adj u v) :
    (componentRestrictedSelectedGraph G F c x).Adj u v := by
  change ∃ e : (activeSubgraph G).RestrictedEdge F,
    ((activeSubgraph G).restrictWord F x) e ≠ 0 ∧
      (((activeSubgraph G).src e.1 = u ∧ (activeSubgraph G).dst e.1 = v) ∨
       ((activeSubgraph G).src e.1 = v ∧ (activeSubgraph G).dst e.1 = u)) at h
  rcases h with ⟨e, hx, hsrc | hdst⟩
  · have hc : edgeComponent G e.1 = c := by
      calc
        edgeComponent G e.1 = componentOf G ((activeSubgraph G).src e.1) := rfl
        _ = componentOf G u := congrArg (componentOf G) hsrc.1
        _ = c := hu
    change ∃ e' : (activeSubgraph G).RestrictedEdge (componentPart G F c),
      ((activeSubgraph G).restrictWord (componentPart G F c) x) e' ≠ 0 ∧
        (((activeSubgraph G).src e'.1 = u ∧ (activeSubgraph G).dst e'.1 = v) ∨
         ((activeSubgraph G).src e'.1 = v ∧ (activeSubgraph G).dst e'.1 = u))
    exact ⟨⟨e.1, (mem_componentPart_iff G F c e.1).2 ⟨e.2, hc⟩⟩,
      hx, Or.inl hsrc⟩
  · have hc : edgeComponent G e.1 = c := by
      calc
        edgeComponent G e.1 = componentOf G ((activeSubgraph G).src e.1) := rfl
        _ = componentOf G ((activeSubgraph G).dst e.1) := componentOf_src_eq_dst G e.1
        _ = componentOf G u := congrArg (componentOf G) hdst.2
        _ = c := hu
    change ∃ e' : (activeSubgraph G).RestrictedEdge (componentPart G F c),
      ((activeSubgraph G).restrictWord (componentPart G F c) x) e' ≠ 0 ∧
        (((activeSubgraph G).src e'.1 = u ∧ (activeSubgraph G).dst e'.1 = v) ∨
         ((activeSubgraph G).src e'.1 = v ∧ (activeSubgraph G).dst e'.1 = u))
    exact ⟨⟨e.1, (mem_componentPart_iff G F c e.1).2 ⟨e.2, hc⟩⟩,
      hx, Or.inr hdst⟩

/-- Restricted selected adjacencies, like all active adjacencies, preserve the
active component label. -/
theorem restrictedAdj_same_component (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word)
    {u v : (activeSubgraph G).Vertex}
    (h : ((activeSubgraph G).restrictedSelectedGraph F
      ((activeSubgraph G).restrictWord F x)).Adj u v) :
    componentOf G u = componentOf G v := by
  change ∃ e : (activeSubgraph G).RestrictedEdge F,
    ((activeSubgraph G).restrictWord F x) e ≠ 0 ∧
      (((activeSubgraph G).src e.1 = u ∧ (activeSubgraph G).dst e.1 = v) ∨
       ((activeSubgraph G).src e.1 = v ∧ (activeSubgraph G).dst e.1 = u)) at h
  rcases h with ⟨e, _, hsrc | hdst⟩
  · rw [← hsrc.1, ← hsrc.2]
    exact componentOf_src_eq_dst G e.1
  · rw [← hdst.1, ← hdst.2]
    exact (componentOf_src_eq_dst G e.1).symm



/-- Each component-restricted selected graph is a subgraph of the full
restricted selected graph. -/
theorem componentSelectedGraph_le (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (x : (activeSubgraph G).Word) :
    componentRestrictedSelectedGraph G F c x ≤
      (activeSubgraph G).restrictedSelectedGraph F
        ((activeSubgraph G).restrictWord F x) := by
  intro u v h
  change ∃ e : (activeSubgraph G).RestrictedEdge (componentPart G F c),
    ((activeSubgraph G).restrictWord (componentPart G F c) x) e ≠ 0 ∧
      (((activeSubgraph G).src e.1 = u ∧ (activeSubgraph G).dst e.1 = v) ∨
       ((activeSubgraph G).src e.1 = v ∧ (activeSubgraph G).dst e.1 = u)) at h
  rcases h with ⟨e, hx, h⟩
  have heF := (mem_componentPart_iff G F c e.1).1 e.2 |>.1
  change ∃ e' : (activeSubgraph G).RestrictedEdge F,
    ((activeSubgraph G).restrictWord F x) e' ≠ 0 ∧
      (((activeSubgraph G).src e'.1 = u ∧ (activeSubgraph G).dst e'.1 = v) ∨
       ((activeSubgraph G).src e'.1 = v ∧ (activeSubgraph G).dst e'.1 = u))
  exact ⟨⟨e.1, heF⟩, hx, h⟩

/-- Every edge on a restricted selected walk starting in `c` belongs to the
component-restricted selected graph for `c`. -/
theorem restrictedWalk_edges_in_component (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (x : (activeSubgraph G).Word) {u v : (activeSubgraph G).Vertex}
    (p : ((activeSubgraph G).restrictedSelectedGraph F
      ((activeSubgraph G).restrictWord F x)).Walk u v)
    (hu : componentOf G u = c) :
    ∀ e, e ∈ p.edges → e ∈ (componentRestrictedSelectedGraph G F c x).edgeSet := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        have hlocal := restrictedAdj_to_component G F c x hu h
        exact (componentRestrictedSelectedGraph G F c x).mem_edgeSet.mpr hlocal
      · have huv := restrictedAdj_same_component G F x h
        exact ih (huv.symm.trans hu) e he

/-- At a vertex, only the component containing that vertex contributes to the
restricted selected degree. -/
theorem restrictedSelectedDegree_eq_component (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word)
    (v : (activeSubgraph G).Vertex) :
    (activeSubgraph G).restrictedSelectedDegree F
      ((activeSubgraph G).restrictWord F x) v =
    (activeSubgraph G).restrictedSelectedDegree
      (componentPart G F (componentOf G v))
      ((activeSubgraph G).restrictWord
        (componentPart G F (componentOf G v)) x) v := by
  classical
  let H := activeSubgraph G
  let c := componentOf G v
  let P := Finset.univ.filter fun e : H.RestrictedEdge F =>
    x e.1 ≠ 0 ∧ H.incident e.1 v
  let Q := Finset.univ.filter fun e : H.RestrictedEdge (componentPart G F c) =>
    x e.1 ≠ 0 ∧ H.incident e.1 v
  let equiv : {e : H.RestrictedEdge F // e ∈ P} ≃
      {e : H.RestrictedEdge (componentPart G F c) // e ∈ Q} := {
    toFun := fun z => by
      have hmem := Finset.mem_filter.mp z.2
      have hF : z.1.1 ∈ F := z.1.2
      have hinc : H.incident z.1.1 v := hmem.2.2
      have hc : edgeComponent G z.1.1 = c := by
        rcases hinc with hs | hd
        · calc
            edgeComponent G z.1.1 = componentOf G (H.src z.1.1) := rfl
            _ = componentOf G v := congrArg (componentOf G) hs
            _ = c := rfl
        · calc
            edgeComponent G z.1.1 = componentOf G (H.src z.1.1) := rfl
            _ = componentOf G (H.dst z.1.1) := componentOf_src_eq_dst G z.1.1
            _ = componentOf G v := congrArg (componentOf G) hd
            _ = c := rfl
      refine ⟨⟨z.1.1, (mem_componentPart_iff G F c z.1.1).2
        ⟨hF, hc⟩⟩, ?_⟩
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmem.2
    invFun := fun z => by
      have hmem := Finset.mem_filter.mp z.2
      have hF : z.1.1 ∈ F :=
        ((mem_componentPart_iff G F c z.1.1).1 z.1.2).1
      refine ⟨⟨z.1.1, hF⟩, ?_⟩
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmem.2
    left_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      rfl }
  unfold PhysicalGraph.restrictedSelectedDegree
  change P.card = Q.card
  calc
    P.card = Fintype.card {e // e ∈ P} := (Fintype.card_coe P).symm
    _ = Fintype.card {e // e ∈ Q} := Fintype.card_congr equiv
    _ = Q.card := Fintype.card_coe Q

theorem restrictedSelectedDegree_eq_zero_of_component_ne (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word)
    (v : (activeSubgraph G).Vertex) (c : ActiveComponent G)
    (hc : c ≠ componentOf G v) :
    (activeSubgraph G).restrictedSelectedDegree
      (componentPart G F c)
      ((activeSubgraph G).restrictWord (componentPart G F c) x) v = 0 := by
  classical
  let H := activeSubgraph G
  unfold PhysicalGraph.restrictedSelectedDegree
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  have hecomp := (mem_componentPart_iff G F c e.1).1 e.2
  rcases he.2 with hs | hd
  · apply hc
    calc
      c = edgeComponent G e.1 := hecomp.2.symm
      _ = componentOf G (H.src e.1) := rfl
      _ = componentOf G v := congrArg (componentOf G) hs
  · apply hc
    calc
      c = edgeComponent G e.1 := hecomp.2.symm
      _ = componentOf G (H.src e.1) := rfl
      _ = componentOf G (H.dst e.1) := componentOf_src_eq_dst G e.1
      _ = componentOf G v := congrArg (componentOf G) hd

/-- A restricted selected graph is acyclic exactly when every component
restriction is acyclic. -/
theorem restrictedSelectedGraph_acyclic_iff_components (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word) :
    ((activeSubgraph G).restrictedSelectedGraph F
      ((activeSubgraph G).restrictWord F x)).IsAcyclic ↔
      ∀ c : ActiveComponent G,
        (componentRestrictedSelectedGraph G F c x).IsAcyclic := by
  constructor
  · intro hglobal c u p hp
    have hle := componentSelectedGraph_le G F c x
    exact hglobal (p.mapLe hle) (hp.mapLe hle)
  · intro hlocal u p hp
    let c : ActiveComponent G := componentOf G u
    have hEdges := restrictedWalk_edges_in_component G F c x p rfl
    have hp' : (p.transfer (componentRestrictedSelectedGraph G F c x) hEdges).IsCycle :=
      SimpleGraph.Walk.IsCycle.transfer
        (H := componentRestrictedSelectedGraph G F c x) hp hEdges
    exact hlocal c (p.transfer (componentRestrictedSelectedGraph G F c x) hEdges) hp'

/-- The full restricted-linear-forest predicate factors over the active
components: acyclicity splits by walks, and each vertex degree is contributed
only by its own component. -/
theorem isRestrictedLinearForest_iff_components (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word) :
    (activeSubgraph G).IsRestrictedLinearForest F
      ((activeSubgraph G).restrictWord F x) ↔
      ∀ c : ActiveComponent G,
        (activeSubgraph G).IsRestrictedLinearForest (componentPart G F c)
          ((activeSubgraph G).restrictWord (componentPart G F c) x) := by
  unfold PhysicalGraph.IsRestrictedLinearForest
  rw [restrictedSelectedGraph_acyclic_iff_components]
  constructor
  · rintro ⟨hacyc, hdegree⟩ c
    refine ⟨hacyc c, ?_⟩
    intro v
    by_cases hc : c = componentOf G v
    · subst c
      have hl := hdegree v
      rw [restrictedSelectedDegree_eq_component G F x v] at hl
      exact hl
    · rw [restrictedSelectedDegree_eq_zero_of_component_ne G F x v c hc]
      omega
  · intro h
    refine ⟨(fun c => (h c).1), ?_⟩
    intro v
    rw [restrictedSelectedDegree_eq_component G F x v]
    exact (h (componentOf G v)).2 v

theorem mem_componentEdges_iff (G : PhysicalGraph) (c : ActiveComponent G)
    (e : (activeSubgraph G).Edge) :
    e ∈ componentEdges G c ↔ edgeComponent G e = c := by
  classical
  simp [componentEdges]

/-- Every active edge belongs to exactly one of the component edge sets. -/
theorem edgeComponent_mem_componentEdges (G : PhysicalGraph)
    (e : (activeSubgraph G).Edge) :
    e ∈ componentEdges G (edgeComponent G e) := by
  rw [mem_componentEdges_iff]



/-- The active edge labels are partitioned by their unique component. -/
def edgeSigmaEquiv (G : PhysicalGraph) :
    (activeSubgraph G).Edge ≃
      Σ c : ActiveComponent G,
        (activeSubgraph G).RestrictedEdge (componentEdges G c) where
  toFun e := ⟨edgeComponent G e,
    ⟨e, edgeComponent_mem_componentEdges G e⟩⟩
  invFun p := p.2.1
  left_inv e := rfl
  right_inv := by
    rintro ⟨c, ⟨e, he⟩⟩
    have hc : edgeComponent G e = c :=
      (mem_componentEdges_iff G c e).1 he
    subst c
    rfl

/-- Exact coordinate splitting of all active edge words into component words. -/
def edgeWordProductEquiv (G : PhysicalGraph) :
    (activeSubgraph G).Word ≃
      ((c : ActiveComponent G) →
        (activeSubgraph G).RestrictedWord (componentEdges G c)) where
  toFun x c e := x ((edgeSigmaEquiv G).symm ⟨c, e⟩)
  invFun y e := y ((edgeSigmaEquiv G e).1) ((edgeSigmaEquiv G e).2)
  left_inv x := by
    funext e
    change x ((edgeSigmaEquiv G).symm (edgeSigmaEquiv G e)) = x e
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    funext c
    funext e
    let a : Σ c : ActiveComponent G,
        (activeSubgraph G).RestrictedEdge (componentEdges G c) := ⟨c, e⟩
    change y ((edgeSigmaEquiv G ((edgeSigmaEquiv G).symm a)).1)
      ((edgeSigmaEquiv G ((edgeSigmaEquiv G).symm a)).2) = y c e
    rw [Equiv.apply_symm_apply]

/-- The word-product equivalence's coordinate formula. -/
theorem edgeWordProductEquiv_apply (G : PhysicalGraph)
    (x : (activeSubgraph G).Word) (c : ActiveComponent G)
    (e : (activeSubgraph G).RestrictedEdge (componentEdges G c)) :
    edgeWordProductEquiv G x c e =
      x ((edgeSigmaEquiv G).symm ⟨c, e⟩) := by
  rfl

/-- Boundary of a component restriction is the host boundary at vertices in
that component, and zero at all other vertices. -/
theorem restrictedBoundary_component_formula (G : PhysicalGraph)
    (x : (activeSubgraph G).Word) (c : ActiveComponent G)
    (v : (activeSubgraph G).Vertex)
    [Decidable (componentOf G v = c)] :
    (activeSubgraph G).restrictedBoundary (componentEdges G c)
      ((activeSubgraph G).restrictWord (componentEdges G c) x) v =
        if componentOf G v = c then (activeSubgraph G).boundary x v else 0 := by
  classical
  let H := activeSubgraph G
  let E := componentEdges G c
  change H.boundary (H.extendWord E (H.restrictWord E x)) v = _
  change (∑ e : H.Edge,
      ((if H.src e = v then H.extendWord E (H.restrictWord E x) e else 0) +
       (if H.dst e = v then H.extendWord E (H.restrictWord E x) e else 0))) = _
  have hsrc (e : H.Edge) :
      (if H.src e = v then H.extendWord E (H.restrictWord E x) e else 0) =
        if componentOf G v = c then
          (if H.src e = v then x e else 0) else 0 := by
    by_cases hs : H.src e = v
    · subst v
      have hcomp : edgeComponent G e = componentOf G (H.src e) := rfl
      simp [E, H, PhysicalGraph.extendWord, PhysicalGraph.restrictWord,
        componentEdges, edgeComponent, componentOf, hcomp]
    · simp [hs]
  have hdst (e : H.Edge) :
      (if H.dst e = v then H.extendWord E (H.restrictWord E x) e else 0) =
        if componentOf G v = c then
          (if H.dst e = v then x e else 0) else 0 := by
    by_cases hd : H.dst e = v
    · subst v
      have hcomp : edgeComponent G e = componentOf G (H.dst e) :=
        edgeComponent_eq_dst G e
      change componentOf G (H.src e) = componentOf G (H.dst e) at hcomp
      simp [E, H, PhysicalGraph.extendWord, PhysicalGraph.restrictWord,
        componentEdges, edgeComponent, hcomp]
    · simp [hd]
  rw [Finset.sum_congr rfl (fun e he => by rw [hsrc e, hdst e])]
  by_cases hvc : componentOf G v = c <;> simp [hvc, H, PhysicalGraph.boundary]

/-- Cycle-space decomposition on restricted edge labels, before converting
each factor back to the corresponding reindexed physical graph. -/
def restrictedCycleSpaceProductEquiv (G : PhysicalGraph) :
    (activeSubgraph G).CycleSpace ≃
      ((c : ActiveComponent G) →
        (activeSubgraph G).RestrictedCycleSpace (componentEdges G c)) where
  toFun x c := by
    classical
    letI : DecidablePred (fun v : (activeSubgraph G).Vertex =>
      componentOf G v = c) := fun v => Classical.propDecidable _
    refine ⟨edgeWordProductEquiv G x.1 c, ?_⟩
    funext v
    have hword : edgeWordProductEquiv G x.1 c =
        (activeSubgraph G).restrictWord (componentEdges G c) x.1 := by
      funext e
      rw [edgeWordProductEquiv_apply]
      simp [PhysicalGraph.restrictWord, edgeSigmaEquiv, e.2]
    rw [hword, restrictedBoundary_component_formula G x.1 c v]
    by_cases hvc : componentOf G v = c <;> simp [hvc, x.2]
  invFun y := by
    let w : (activeSubgraph G).Word :=
      (edgeWordProductEquiv G).symm (fun c => (y c).1)
    refine ⟨w, ?_⟩
    classical
    funext v
    let c : ActiveComponent G := componentOf G v
    letI : Decidable (componentOf G v = c) := Classical.propDecidable _
    have hloc :
        (activeSubgraph G).restrictWord (componentEdges G c) w = (y c).1 := by
      have h := (edgeWordProductEquiv G).apply_symm_apply (fun c => (y c).1)
      exact congrFun h c
    have hf := restrictedBoundary_component_formula G w c v
    have hcv : componentOf G v = c := rfl
    simp [hcv] at hf
    rw [← hf, hloc]
    exact congrFun (y c).2 v
  left_inv x := by
    apply Subtype.ext
    exact (edgeWordProductEquiv G).left_inv x.1
  right_inv y := by
    funext c
    apply Subtype.ext
    exact congrFun ((edgeWordProductEquiv G).apply_symm_apply
      (fun c => (y c).1)) c

/-- Reindex each restricted cycle space as the cycle space of its own physical
edge-subgraph. -/
def componentCycleSpaceReindexEquiv (G : PhysicalGraph) :
    ((c : ActiveComponent G) →
      (activeSubgraph G).RestrictedCycleSpace (componentEdges G c)) ≃
    ((c : ActiveComponent G) →
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) where
  toFun y c :=
    ((activeSubgraph G).restrictPhysicalCycleEquiv (componentEdges G c)).symm (y c)
  invFun y c :=
    (activeSubgraph G).restrictPhysicalCycleEquiv (componentEdges G c) (y c)
  left_inv y := by
    funext c
    exact ((activeSubgraph G).restrictPhysicalCycleEquiv
      (componentEdges G c)).right_inv (y c)
  right_inv y := by
    funext c
    exact ((activeSubgraph G).restrictPhysicalCycleEquiv
      (componentEdges G c)).left_inv (y c)

/-- Exact product equivalence for the active cycle space, with componentwise
edge coordinates. -/
def activeCycleSpaceProductEquiv (G : PhysicalGraph) :
    (activeSubgraph G).CycleSpace ≃
      ((c : ActiveComponent G) →
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) :=
  (restrictedCycleSpaceProductEquiv G).trans (componentCycleSpaceReindexEquiv G)

/-- The physical component equivalence preserves the edge coordinate attached
to each component label. -/
theorem activeCycleSpaceProductEquiv_apply_coordinate (G : PhysicalGraph)
    (x : (activeSubgraph G).CycleSpace) (c : ActiveComponent G)
    (j : Fin (componentEdges G c).card) :
    (activeCycleSpaceProductEquiv G x c).1 j =
      x.1 ((edgeSigmaEquiv G).symm
        ⟨c, (activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) j⟩) := by
  change ((((activeSubgraph G).restrictPhysicalCycleEquiv
    (componentEdges G c)).symm
      (restrictedCycleSpaceProductEquiv G x c)) :
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace).1 j = _
  change ((activeSubgraph G).restrictPhysicalWordEquiv
    (componentEdges G c)).symm
      (edgeWordProductEquiv G x.1 c) j = _
  simp [PhysicalGraph.restrictPhysicalWordEquiv, edgeWordProductEquiv_apply]

/-- The active cycle space is the product of the cycle spaces of its active
connected components. -/
def cycleSpaceProductDecomposition (G : PhysicalGraph) :
    (activeSubgraph G).CycleSpace ≃
      ((c : ActiveComponent G) →
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) :=
  activeCycleSpaceProductEquiv G

/-- Every active edge coordinate outside the active subgraph is forced to zero
on the host cycle space. This is the bridge-coordinate formula needed before
the component product split. -/
theorem cycle_word_zero_off_active_edges (G : PhysicalGraph)
    (x : G.CycleSpace) (e : G.Edge) (he : e ∉ activeEdges G) :
    x.1 e = 0 := by
  apply cycle_coordinate_eq_zero_of_inactive
  simpa [mem_activeEdges_iff] using he

end Erdos1016.Proof.ActivePhysicalComponents

end

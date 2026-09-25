import Erdos1016.CycleSpace.Graphical.LinkMap
import Erdos1016.CycleSpace.Graphical.EndpointCycles

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalLinkPairWitnesses

open Erdos1016
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalCommonInformation

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private def vertexUnit (G : PhysicalGraph) (v : G.Vertex) : G.Demand :=
  fun w => if w = v then 1 else 0

private def edgeUnit (G : PhysicalGraph) (e : G.Edge) : G.Word :=
  fun f => if f = e then 1 else 0

private theorem double_zero (x : F₂) : x + x = 0 := by
  have h2zero : (2 : F₂) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : F₂) * x := by ring
    _ = 0 := by rw [h2zero]; simp

noncomputable def physicalEdgeOfAdj (G : PhysicalGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) : G.Edge :=
  Classical.choose (by
    simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h)

theorem physicalEdgeOfAdj_spec (G : PhysicalGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) :
    (G.src (physicalEdgeOfAdj G h) = u ∧ G.dst (physicalEdgeOfAdj G h) = v) ∨
      (G.src (physicalEdgeOfAdj G h) = v ∧ G.dst (physicalEdgeOfAdj G h) = u) := by
  have hspec := Classical.choose_spec (by
    simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h)
  simpa [physicalEdgeOfAdj] using hspec

noncomputable def walkChain (G : PhysicalGraph) {u v : G.Vertex} :
    G.toSimpleGraph.Walk u v → G.Word
  | .nil => 0
  | .cons h p => edgeUnit G (physicalEdgeOfAdj G h) + walkChain G p

/-- Recursive certificate that every vertex visited by a walk avoids `w`. -/
def walkAvoidsVertex (G : PhysicalGraph) {a b : G.Vertex} (w : G.Vertex) :
    G.toSimpleGraph.Walk a b → Prop
  | .nil => a ≠ w
  | @SimpleGraph.Walk.cons _ _ a c b _ p =>
      a ≠ w ∧ c ≠ w ∧ walkAvoidsVertex G w p

/-- A walk whose vertices avoid `w` has a word with no selected edge at `w`. -/
theorem walkChain_zero_on_incident_of_walkAvoidsVertex (G : PhysicalGraph)
    {a b : G.Vertex} (w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
    (hp : walkAvoidsVertex G w p) (e : G.Edge) (he : G.incident e w) :
    walkChain G p e = 0 := by
  induction p with
  | nil => simp [walkChain]
  | @cons a c b hac p ih =>
      rcases hp with ⟨ha, hc, hp⟩
      simp only [walkChain]
      have hnot : ¬ G.incident (physicalEdgeOfAdj G hac) w := by
        intro h
        have hedge := physicalEdgeOfAdj_spec G hac
        rcases hedge with h' | h'
        · rcases h with hs | ht
          · exact ha (h'.1.symm.trans hs)
          · exact hc (h'.2.symm.trans ht)
        · rcases h with hs | ht
          · exact hc (h'.1.symm.trans hs)
          · exact ha (h'.2.symm.trans ht)
      have hunit : edgeUnit G (physicalEdgeOfAdj G hac) e = 0 := by
        dsimp [edgeUnit]
        by_cases hEq : physicalEdgeOfAdj G hac = e
        · subst e
          exact (hnot he).elim
        · have hEq' : e ≠ physicalEdgeOfAdj G hac := Ne.symm hEq
          simp [edgeUnit, hEq']
      change edgeUnit G (physicalEdgeOfAdj G hac) e + walkChain G p e = 0
      rw [hunit, ih hp]
      simp

theorem walkAvoidsVertex_append (G : PhysicalGraph) {a b c : G.Vertex}
    (w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
    (q : G.toSimpleGraph.Walk b c)
    (hp : walkAvoidsVertex G w p) (hq : walkAvoidsVertex G w q) :
    walkAvoidsVertex G w (p.append q) := by
  induction p with
  | nil => simpa [walkAvoidsVertex] using hq
  | @cons a b d hab p ih =>
      simp only [SimpleGraph.Walk.cons_append, walkAvoidsVertex] at hp ⊢
      rcases hp with ⟨ha, hb, hp⟩
      exact ⟨ha, hb, ih q hp hq⟩

private theorem boundary_edgeUnit (G : PhysicalGraph) (e : G.Edge) :
    G.boundary (edgeUnit G e) = vertexUnit G (G.src e) + vertexUnit G (G.dst e) := by
  classical
  ext v
  change (∑ f, ((if G.src f = v then edgeUnit G e f else 0) +
    (if G.dst f = v then edgeUnit G e f else 0))) = _
  rw [Finset.sum_add_distrib]
  have hsrc : (∑ f, if G.src f = v then edgeUnit G e f else 0) =
      if G.src e = v then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp [edgeUnit]
    · intro f _ hfe
      simp [edgeUnit, hfe]
    · simp
  have hdst : (∑ f, if G.dst f = v then edgeUnit G e f else 0) =
      if G.dst e = v then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp [edgeUnit]
    · intro f _ hfe
      simp [edgeUnit, hfe]
    · simp
  rw [hsrc, hdst]
  simp [vertexUnit, eq_comm]

private theorem boundary_walkChain (G : PhysicalGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    G.boundary (walkChain G p) = vertexUnit G u + vertexUnit G v := by
  induction p with
  | nil =>
      rename_i a
      simp [walkChain]
      ext x
      by_cases hx : x = a <;> simp [vertexUnit, hx, double_zero]
  | @cons a b c hab p ih =>
      simp only [walkChain, map_add, boundary_edgeUnit, ih]
      have hedge := physicalEdgeOfAdj_spec G hab
      rcases hedge with h | h
      · rw [h.1, h.2]
        ext x
        by_cases hx : x = b
        · subst x
          have hba : b ≠ a := Ne.symm hab.ne
          dsimp [vertexUnit]
          simp only [if_neg hba, if_pos]
          simp only [zero_add, add_zero]
          rw [← add_assoc, double_zero 1, zero_add]
        · simp [vertexUnit, hx]
      · rw [h.1, h.2]
        ext x
        by_cases hx : x = b
        · subst x
          have hba : b ≠ a := Ne.symm hab.ne
          dsimp [vertexUnit]
          simp only [if_neg hba, if_pos]
          simp only [zero_add, add_zero]
          rw [← add_assoc, double_zero 1, zero_add]
        · simp [vertexUnit, hx]

/-- The link-coordinate map before restricting to cycle words. -/
def rawLinkCoordinate (G : PhysicalGraph) (u v : G.Vertex) :
    G.Word →ₗ[F₂] (LinkIndex G u v → F₂) where
  toFun x i := by
    classical
    cases i with
    | inl e => exact x e.1
    | inr c => exact ∑ e : G.Edge,
        if componentCutCondition G u v c.1 e then x e else 0
  map_add' x y := by
    classical
    ext i
    cases i with
    | inl e => rfl
    | inr c =>
        change (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then (x e + y e) else 0) =
          (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then x e else 0) +
          (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then y e else 0)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : componentCutCondition G u v c.1 e <;> simp [h]
  map_smul' a x := by
    classical
    funext i
    cases i with
    | inl e => rfl
    | inr c =>
        change (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then a * x e else 0) =
          a * (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then x e else 0)
        calc
          (∑ e : G.Edge,
              if componentCutCondition G u v c.1 e then a * x e else 0) =
              ∑ e : G.Edge, a * (if componentCutCondition G u v c.1 e then x e else 0) := by
                apply Finset.sum_congr rfl
                intro e he
                by_cases h : componentCutCondition G u v c.1 e <;> simp [h]
          _ = _ := by rw [Finset.mul_sum]

@[simp] theorem rawLinkCoordinate_edgeUnit (G : PhysicalGraph) (u v : G.Vertex)
    (e : G.Edge) (i : LinkIndex G u v) :
    rawLinkCoordinate G u v (edgeUnit G e) i =
      match i with
      | .inl d => if d.1 = e then 1 else 0
      | .inr c => if componentCutCondition G u v c.1 e then 1 else 0 := by
  classical
  cases i with
  | inl d => simp [rawLinkCoordinate, edgeUnit]
  | inr c =>
      change (∑ f : G.Edge,
        if componentCutCondition G u v c.1 f then (if f = e then (1 : F₂) else 0) else 0) =
        if componentCutCondition G u v c.1 e then (1 : F₂) else 0
      calc
        (∑ f : G.Edge,
          if componentCutCondition G u v c.1 f then (if f = e then 1 else 0) else 0) =
            ∑ f : G.Edge, if f = e then
              (if componentCutCondition G u v c.1 f then (1 : F₂) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro f hf
          by_cases h : f = e <;> simp [h]
        _ = if componentCutCondition G u v c.1 e then 1 else 0 := by simp

@[simp] theorem rawLinkCoordinate_add (G : PhysicalGraph) (u v : G.Vertex)
    (x y : G.Word) :
    rawLinkCoordinate G u v (x + y) =
      rawLinkCoordinate G u v x + rawLinkCoordinate G u v y :=
  map_add (rawLinkCoordinate G u v) x y

/-- The walk-chain construction respects concatenation. -/
private theorem walkChain_append (G : PhysicalGraph) {a b c : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) (q : G.toSimpleGraph.Walk b c) :
    walkChain G (p.append q) = walkChain G p + walkChain G q := by
  induction p with
  | nil => simp [walkChain]
  | @cons a b d hab p ih =>
      simp only [SimpleGraph.Walk.cons_append, walkChain]
      rw [ih]
      abel

private def linkComponentVertices (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) : Finset G.Vertex :=
  Finset.univ.filter fun z =>
    ∃ hz : z ≠ u ∧ z ≠ v,
      (deletedGraph G u v).connectedComponentMk ⟨z, hz⟩ = c

private theorem componentCutCondition_of_link_attachment (G : PhysicalGraph)
    (u v : G.Vertex) (c : ComponentLink G u v) (e : G.Edge)
    (x : DeletedVertex G u v)
    (he : (G.src e = u ∧ G.dst e = x.1) ∨
      (G.dst e = u ∧ G.src e = x.1))
    (hx : (deletedGraph G u v).connectedComponentMk x = c.1) :
    componentCutCondition G u v c.1 e := by
  rcases he with h | h
  · change (G.src e = u ∧ G.dst e ∈ linkComponentVertices G u v c.1) ∨
      (G.dst e = u ∧ G.src e ∈ linkComponentVertices G u v c.1)
    left
    refine ⟨h.1, ?_⟩
    simp [linkComponentVertices, h.2, x.2, hx]
  · change (G.src e = u ∧ G.dst e ∈ linkComponentVertices G u v c.1) ∨
      (G.dst e = u ∧ G.src e ∈ linkComponentVertices G u v c.1)
    right
    refine ⟨h.1, ?_⟩
    simp [linkComponentVertices, h.2, x.2, hx]

private theorem componentCutCondition_attachment_iff (G : PhysicalGraph)
    (u v : G.Vertex) (c d : ComponentLink G u v) (e : G.Edge)
    (x : DeletedVertex G u v)
    (he : (G.src e = u ∧ G.dst e = x.1) ∨
      (G.dst e = u ∧ G.src e = x.1))
    (hx : (deletedGraph G u v).connectedComponentMk x = c.1) :
    componentCutCondition G u v d.1 e ↔ d = c := by
  constructor
  · intro hcut
    have hmem : x.1 ∈ linkComponentVertices G u v d.1 := by
      change (G.src e = u ∧ G.dst e ∈ linkComponentVertices G u v d.1) ∨
        (G.dst e = u ∧ G.src e ∈ linkComponentVertices G u v d.1) at hcut
      rcases he with h | h
      · rcases hcut with hcut | hcut
        · simpa [h.1, h.2] using hcut.2
        · have : x.1 = u := h.2.symm.trans hcut.1
          exact (x.2.1 this).elim
      · rcases hcut with hcut | hcut
        · have : x.1 = u := h.2.symm.trans hcut.1
          exact (x.2.1 this).elim
        · simpa [h.1, h.2] using hcut.2
    have hcomp : (deletedGraph G u v).connectedComponentMk x = d.1 := by
      simp only [linkComponentVertices, Finset.mem_filter, Finset.mem_univ,
        true_and] at hmem
      rcases hmem with ⟨_, hcomp⟩
      exact hcomp
    have hval : d.1 = c.1 := hcomp.symm.trans hx
    exact Subtype.ext hval
  · intro hdc
    cases hdc
    exact componentCutCondition_of_link_attachment G u v c e x he hx

/-- The assignment supported on one component link. -/
def componentLinkUnit (G : PhysicalGraph) (u v : G.Vertex)
    (c : ComponentLink G u v) : LinkIndex G u v → F₂ :=
  fun i => if i = Sum.inr c then 1 else 0

/-- The assignment supported on one direct-edge link. -/
def directLinkUnit (G : PhysicalGraph) (u v : G.Vertex)
    (d : DirectLink G u v) : LinkIndex G u v → F₂ :=
  fun i => if i = Sum.inl d then 1 else 0

private theorem componentCutCondition_formula (G : PhysicalGraph)
    (u v : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge) :
    componentCutCondition G u v c e ↔
      (G.src e = u ∧ G.dst e ∈ linkComponentVertices G u v c) ∨
      (G.dst e = u ∧ G.src e ∈ linkComponentVertices G u v c) := by
  rfl

private theorem not_componentCut_of_deleted_endpoints (G : PhysicalGraph)
    (u v : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (a b : DeletedVertex G u v)
    (he : (G.src e = a.1 ∧ G.dst e = b.1) ∨
      (G.src e = b.1 ∧ G.dst e = a.1)) :
    ¬ componentCutCondition G u v c e := by
  rw [componentCutCondition_formula]
  rcases he with h | h
  · rintro (hcut | hcut)
    · exact a.2.1 (h.1.symm.trans hcut.1)
    · exact b.2.1 (h.2.symm.trans hcut.1)
  · rintro (hcut | hcut)
    · exact b.2.1 (h.1.symm.trans hcut.1)
    · exact a.2.1 (h.2.symm.trans hcut.1)

private theorem not_direct_of_deleted_endpoints (G : PhysicalGraph)
    (u v : G.Vertex) (d : DirectLink G u v) (e : G.Edge)
    (a b : DeletedVertex G u v)
    (he : (G.src e = a.1 ∧ G.dst e = b.1) ∨
      (G.src e = b.1 ∧ G.dst e = a.1)) : e ≠ d.1 := by
  intro hed
  subst e
  rcases d.2 with hd | hd
  · rcases he with h | h
    · exact a.2.1 (h.1.symm.trans hd.1)
    · exact b.2.1 (h.1.symm.trans hd.1)
  · rcases he with h | h
    · exact b.2.1 (h.2.symm.trans hd.2)
    · exact a.2.1 (h.2.symm.trans hd.2)

private theorem not_direct_of_u_attachment (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (d : DirectLink G u v) (e : G.Edge)
    (x : DeletedVertex G u v)
    (he : (G.src e = u ∧ G.dst e = x.1) ∨
      (G.dst e = u ∧ G.src e = x.1)) : e ≠ d.1 := by
  intro hed
  subst e
  rcases he with he | he
  · rcases d.2 with hd | hd
    · exact x.2.2 (he.2.symm.trans hd.2)
    · exact hne (he.1.symm.trans hd.1)
  · rcases d.2 with hd | hd
    · exact x.2.1 (he.2.symm.trans hd.1)
    · exact x.2.2 (he.2.symm.trans hd.1)

private theorem not_direct_of_v_attachment (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (d : DirectLink G u v) (e : G.Edge)
    (y : DeletedVertex G u v)
    (he : (G.src e = v ∧ G.dst e = y.1) ∨
      (G.dst e = v ∧ G.src e = y.1)) : e ≠ d.1 := by
  intro hed
  subst e
  rcases he with he | he
  · rcases d.2 with hd | hd
    · exact hne (hd.1.symm.trans he.1)
    · exact y.2.1 (he.2.symm.trans hd.2)
  · rcases d.2 with hd | hd
    · exact y.2.1 (he.2.symm.trans hd.1)
    · exact (hne.symm) (he.1.symm.trans hd.2)

private theorem not_componentCut_of_v_attachment (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (y : DeletedVertex G u v)
    (he : (G.src e = v ∧ G.dst e = y.1) ∨
      (G.dst e = v ∧ G.src e = y.1)) :
    ¬ componentCutCondition G u v c e := by
  rw [componentCutCondition_formula]
  rcases he with h | h
  · rintro (hc | hc)
    · exact hne (hc.1.symm.trans h.1)
    · exact y.2.1 (h.2.symm.trans hc.1)
  · rintro (hc | hc)
    · exact y.2.1 (h.2.symm.trans hc.1)
    · exact hne.symm (h.1.symm.trans hc.1)

private theorem rawLinkCoordinate_uAttachment (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (c : ComponentLink G u v)
    (e : G.Edge) (x : DeletedVertex G u v)
    (he : (G.src e = u ∧ G.dst e = x.1) ∨
      (G.dst e = u ∧ G.src e = x.1))
    (hx : (deletedGraph G u v).connectedComponentMk x = c.1) :
    rawLinkCoordinate G u v (edgeUnit G e) = componentLinkUnit G u v c := by
  classical
  ext i
  cases i with
  | inl d =>
      have hne' : d.1 ≠ e := fun h =>
        not_direct_of_u_attachment G u v hne d e x he h.symm
      simp [rawLinkCoordinate_edgeUnit, componentLinkUnit, hne']
  | inr d =>
      simp only [rawLinkCoordinate_edgeUnit, componentLinkUnit]
      rw [componentCutCondition_attachment_iff G u v c d e x he hx]
      by_cases hdc : d = c
      · simp [hdc]
      · have hsum : (Sum.inr d : LinkIndex G u v) ≠ Sum.inr c := by
          intro heq
          exact hdc (Sum.inr.inj heq)
        simp [hdc, hsum]

private theorem rawLinkCoordinate_vAttachment_zero (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (e : G.Edge) (y : DeletedVertex G u v)
    (he : (G.src e = v ∧ G.dst e = y.1) ∨
      (G.dst e = v ∧ G.src e = y.1)) :
    rawLinkCoordinate G u v (edgeUnit G e) = 0 := by
  classical
  ext i
  cases i with
  | inl d =>
      have hne' : d.1 ≠ e := fun h =>
        not_direct_of_v_attachment G u v hne d e y he h.symm
      simp [rawLinkCoordinate_edgeUnit, hne']
  | inr c =>
      simp only [rawLinkCoordinate_edgeUnit]
      exact if_neg (not_componentCut_of_v_attachment G u v hne c.1 e y he)

def deletedGraphInc (G : PhysicalGraph) (u v : G.Vertex) :
    deletedGraph G u v →g G.toSimpleGraph where
  toFun := fun x => x.1
  map_rel' := by intro a b h; exact h

/-- A walk within one two-vertex-deleted component avoids every vertex outside
that component. -/
theorem deletedWalk_avoidsVertex_of_component (G : PhysicalGraph) (u v w : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent)
    {a b : DeletedVertex G u v} (p : (deletedGraph G u v).Walk a b)
    (ha : (deletedGraph G u v).connectedComponentMk a = c)
    (hnot : w ∉ componentVertices G u v c) :
    walkAvoidsVertex G w (p.map (deletedGraphInc G u v)) := by
  induction p with
  | nil =>
      rename_i a
      simp only [SimpleGraph.Walk.map, walkAvoidsVertex]
      intro hw
      have hmem : a.1 ∈ componentVertices G u v c := by
        simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨a.2, ?_⟩
        simpa using ha
      exact hnot (hw ▸ hmem)
  | @cons a b d hab p ih =>
      simp only [SimpleGraph.Walk.map, walkAvoidsVertex]
      have hbcomp : (deletedGraph G u v).connectedComponentMk b = c := by
        have hreach := SimpleGraph.Adj.reachable hab
        have hsame := SimpleGraph.ConnectedComponent.sound hreach
        exact hsame.symm.trans ha
      have ha_mem : a.1 ∈ componentVertices G u v c := by
        simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨a.2, ?_⟩
        simpa using ha
      have hb_mem : b.1 ∈ componentVertices G u v c := by
        simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨b.2, hbcomp⟩
      have ha_ne : a.1 ≠ w := by
        intro h
        exact hnot (h ▸ ha_mem)
      have hb_ne : b.1 ≠ w := by
        intro h
        exact hnot (h ▸ hb_mem)
      exact ⟨ha_ne, hb_ne, ih hbcomp⟩

private theorem rawLinkCoordinate_deletedEdge_zero (G : PhysicalGraph)
    (u v : G.Vertex) (a b : DeletedVertex G u v) (e : G.Edge)
    (he : (G.src e = a.1 ∧ G.dst e = b.1) ∨
      (G.src e = b.1 ∧ G.dst e = a.1)) :
    rawLinkCoordinate G u v (edgeUnit G e) = 0 := by
  classical
  ext i
  cases i with
  | inl d =>
      have hne : d.1 ≠ e := fun h =>
        not_direct_of_deleted_endpoints G u v d e a b he h.symm
      simp [rawLinkCoordinate_edgeUnit, hne]
  | inr c =>
      simp only [rawLinkCoordinate_edgeUnit]
      exact if_neg (not_componentCut_of_deleted_endpoints G u v c.1 e a b he)

private theorem rawLinkCoordinate_walkChain_deleted (G : PhysicalGraph)
    (u v : G.Vertex) {a b : DeletedVertex G u v}
    (p : (deletedGraph G u v).Walk a b) :
    rawLinkCoordinate G u v (walkChain G (p.map (deletedGraphInc G u v))) = 0 := by
  induction p with
  | nil =>
      ext i
      cases i <;> simp [walkChain, rawLinkCoordinate]
  | @cons a b c hab p ih =>
      simp only [SimpleGraph.Walk.map, walkChain]
      rw [map_add (rawLinkCoordinate G u v), ih]
      rw [add_zero]
      apply rawLinkCoordinate_deletedEdge_zero G u v a b
      exact physicalEdgeOfAdj_spec G (show G.toSimpleGraph.Adj a.1 b.1 from hab)

private theorem physicalEdgeAdj (G : PhysicalGraph) (e : G.Edge) :
    G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
  change ∃ f, (fun _ : G.Edge => (1 : F₂)) f ≠ 0 ∧
    ((G.src f = G.src e ∧ G.dst f = G.dst e) ∨
      (G.src f = G.dst e ∧ G.dst f = G.src e))
  exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

/-- A path word from u into a specified two-vertex-deleted component and back
out to v has precisely that component's link coordinate. -/
theorem componentLink_pathWord_exists (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (c : ComponentLink G u v) :
    ∃ w : G.Word,
      G.boundary w = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v w = componentLinkUnit G u v c := by
  classical
  rcases c.2.1 with ⟨e₁, x, hattachU, hx⟩
  rcases c.2.2 with ⟨e₂, y, hattachV, hy⟩
  have hux : G.toSimpleGraph.Adj u x.1 := by
    rcases hattachU with h | h
    · simpa [h.1, h.2] using physicalEdgeAdj G e₁
    · simpa [h.1, h.2] using G.toSimpleGraph.symm (physicalEdgeAdj G e₁)
  have hyv : G.toSimpleGraph.Adj y.1 v := by
    rcases hattachV with h | h
    · simpa [h.1, h.2] using G.toSimpleGraph.symm (physicalEdgeAdj G e₂)
    · simpa [h.1, h.2] using physicalEdgeAdj G e₂
  have hxy : (deletedGraph G u v).Reachable x y :=
    SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
  rcases hxy with ⟨p⟩
  let q : G.toSimpleGraph.Walk u v := SimpleGraph.Walk.cons hux
    ((p.map (deletedGraphInc G u v)).append (SimpleGraph.Walk.cons hyv SimpleGraph.Walk.nil))
  let first := physicalEdgeOfAdj G hux
  let last := physicalEdgeOfAdj G hyv
  have hfirst0 := physicalEdgeOfAdj_spec G hux
  have hfirst : (G.src first = u ∧ G.dst first = x.1) ∨
      (G.dst first = u ∧ G.src first = x.1) := by
    rcases hfirst0 with h | h
    · exact Or.inl (by simpa [first] using h)
    · exact Or.inr ⟨by simpa [first] using h.2,
        by simpa [first] using h.1⟩
  have hlast0 : (G.src last = y.1 ∧ G.dst last = v) ∨
      (G.src last = v ∧ G.dst last = y.1) := by
    simpa [last] using physicalEdgeOfAdj_spec G hyv
  have hlast : (G.src last = v ∧ G.dst last = y.1) ∨
      (G.dst last = v ∧ G.src last = y.1) := by
    rcases hlast0 with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.1, h.2⟩
  have hchain : walkChain G q =
      edgeUnit G first + walkChain G (p.map (deletedGraphInc G u v)) + edgeUnit G last := by
    dsimp [q, first, last]
    simp only [walkChain, walkChain_append, add_zero]
    abel
  refine ⟨walkChain G q, boundary_walkChain G q, ?_⟩
  rw [hchain, map_add (rawLinkCoordinate G u v),
    map_add (rawLinkCoordinate G u v)]
  rw [rawLinkCoordinate_walkChain_deleted G u v p]
  rw [rawLinkCoordinate_uAttachment G u v hne c first x hfirst hx]
  rw [rawLinkCoordinate_vAttachment_zero G u v hne last y hlast]
  simp [componentLinkUnit]

/-- The component-link path witness can be chosen to avoid any vertex outside
its deleted component and distinct from its two endpoints. -/
theorem componentLink_pathWord_exists_avoiding (G : PhysicalGraph)
    (u v w : G.Vertex) (hne : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (c : ComponentLink G u v)
    (hnot : w ∉ componentVertices G u v c.1) :
    ∃ z : G.Word,
      G.boundary z = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v z = componentLinkUnit G u v c ∧
      ∀ e, G.incident e w → z e = 0 := by
  classical
  rcases c.2.1 with ⟨e₁, x, hattachU, hx⟩
  rcases c.2.2 with ⟨e₂, y, hattachV, hy⟩
  have hux : G.toSimpleGraph.Adj u x.1 := by
    rcases hattachU with h | h
    · simpa [h.1, h.2] using physicalEdgeAdj G e₁
    · simpa [h.1, h.2] using G.toSimpleGraph.symm (physicalEdgeAdj G e₁)
  have hyv : G.toSimpleGraph.Adj y.1 v := by
    rcases hattachV with h | h
    · simpa [h.1, h.2] using G.toSimpleGraph.symm (physicalEdgeAdj G e₂)
    · simpa [h.1, h.2] using physicalEdgeAdj G e₂
  have hxy : (deletedGraph G u v).Reachable x y :=
    SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
  rcases hxy with ⟨p⟩
  let q : G.toSimpleGraph.Walk u v := SimpleGraph.Walk.cons hux
    ((p.map (deletedGraphInc G u v)).append (SimpleGraph.Walk.cons hyv SimpleGraph.Walk.nil))
  let first := physicalEdgeOfAdj G hux
  let last := physicalEdgeOfAdj G hyv
  have hfirst0 := physicalEdgeOfAdj_spec G hux
  have hfirst : (G.src first = u ∧ G.dst first = x.1) ∨
      (G.dst first = u ∧ G.src first = x.1) := by
    rcases hfirst0 with h | h
    · exact Or.inl (by simpa [first] using h)
    · exact Or.inr ⟨by simpa [first] using h.2,
        by simpa [first] using h.1⟩
  have hlast0 : (G.src last = y.1 ∧ G.dst last = v) ∨
      (G.src last = v ∧ G.dst last = y.1) := by
    simpa [last] using physicalEdgeOfAdj_spec G hyv
  have hlast : (G.src last = v ∧ G.dst last = y.1) ∨
      (G.dst last = v ∧ G.src last = y.1) := by
    rcases hlast0 with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.1, h.2⟩
  have hchain : walkChain G q =
      edgeUnit G first + walkChain G (p.map (deletedGraphInc G u v)) + edgeUnit G last := by
    dsimp [q, first, last]
    simp only [walkChain, walkChain_append, add_zero]
    abel
  have hxmem : x.1 ∈ componentVertices G u v c.1 := by
    simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x.2, hx⟩
  have hymem : y.1 ∈ componentVertices G u v c.1 := by
    simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y.2, hy⟩
  have hxw : x.1 ≠ w := by
    intro h
    exact hnot (h ▸ hxmem)
  have hyw : y.1 ≠ w := by
    intro h
    exact hnot (h ▸ hymem)
  have hmiddleAvoid := deletedWalk_avoidsVertex_of_component G u v w c.1 p hx hnot
  have hlastAvoid : walkAvoidsVertex G w
      (SimpleGraph.Walk.cons hyv SimpleGraph.Walk.nil) := by
    simp [walkAvoidsVertex, hyw, hwv.symm]
  have happendedAvoid := walkAvoidsVertex_append G w
    (p.map (deletedGraphInc G u v))
    (SimpleGraph.Walk.cons hyv SimpleGraph.Walk.nil) hmiddleAvoid hlastAvoid
  have hqAvoid : walkAvoidsVertex G w q := by
    dsimp [q]
    exact ⟨hwu.symm, hxw, happendedAvoid⟩
  refine ⟨walkChain G q, boundary_walkChain G q, ?_, ?_⟩
  · rw [hchain, map_add (rawLinkCoordinate G u v),
      map_add (rawLinkCoordinate G u v)]
    rw [rawLinkCoordinate_walkChain_deleted G u v p]
    rw [rawLinkCoordinate_uAttachment G u v hne c first x hfirst hx]
    rw [rawLinkCoordinate_vAttachment_zero G u v hne last y hlast]
    simp [componentLinkUnit]
  · intro e he
    exact walkChain_zero_on_incident_of_walkAvoidsVertex G w q hqAvoid e he

private theorem not_componentCut_of_directLink (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (c : (deletedGraph G u v).ConnectedComponent)
    (d : DirectLink G u v) : ¬ componentCutCondition G u v c d.1 := by
  rw [componentCutCondition_formula]
  rcases d.2 with h | h
  · rintro (hc | hc)
    · have hv : v ∈ linkComponentVertices G u v c := by
        simpa [h.1, h.2] using hc.2
      simp [linkComponentVertices] at hv
    · exact hne (hc.1.symm.trans h.2)
  · rintro (hc | hc)
    · exact hne.symm (h.1.symm.trans hc.1)
    · have hv : v ∈ linkComponentVertices G u v c := by
        simpa [h.1, h.2] using hc.2
      simp [linkComponentVertices] at hv

/-- The single-edge word for a direct link has exactly its direct-link bit. -/
theorem directLink_pathWord_exists (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (d : DirectLink G u v) :
    ∃ w : G.Word,
      G.boundary w = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v w = directLinkUnit G u v d := by
  refine ⟨edgeUnit G d.1, ?_, ?_⟩
  · rcases d.2 with h | h
    · simpa [vertexUnit, h.1, h.2] using boundary_edgeUnit G d.1
    · calc
        G.boundary (edgeUnit G d.1) = vertexUnit G v + vertexUnit G u := by
          simpa [h.1, h.2] using boundary_edgeUnit G d.1
        _ = vertexUnit G u + vertexUnit G v := add_comm _ _
  · classical
    ext i
    cases i with
    | inl d' =>
        simp only [rawLinkCoordinate_edgeUnit, directLinkUnit]
        by_cases hd : d' = d
        · subst d'
          simp
        · have hval : d'.1 ≠ d.1 := by
            intro hval
            exact hd (Subtype.ext hval)
          have hsum : (Sum.inl d' : LinkIndex G u v) ≠ Sum.inl d := by
            intro h
            exact hd (Sum.inl.inj h)
          simp [hval, hsum, hd]
    | inr c =>
        simp [rawLinkCoordinate_edgeUnit, directLinkUnit,
          not_componentCut_of_directLink G u v hne c.1 d]

/-- Every actual link has a physical path word with exactly its own bit. -/
def linkUnitAssignment (G : PhysicalGraph) (u v : G.Vertex)
    (i : LinkIndex G u v) : LinkIndex G u v → F₂ :=
  fun j => if j = i then 1 else 0

private theorem directLink_pathWord_exists_avoiding (G : PhysicalGraph)
    (u v w : G.Vertex) (hwu : w ≠ u) (hwv : w ≠ v)
    (d : DirectLink G u v) :
    ∃ z : G.Word,
      G.boundary z = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v z = directLinkUnit G u v d ∧
      ∀ e, G.incident e w → z e = 0 := by
  refine ⟨edgeUnit G d.1, ?_, ?_, ?_⟩
  · rcases d.2 with h | h
    · simpa [vertexUnit, h.1, h.2] using boundary_edgeUnit G d.1
    · calc
        G.boundary (edgeUnit G d.1) = vertexUnit G v + vertexUnit G u := by
          simpa [vertexUnit, h.1, h.2] using boundary_edgeUnit G d.1
        _ = vertexUnit G u + vertexUnit G v := add_comm _ _
  · classical
    ext i
    cases i with
    | inl d' =>
        simp only [rawLinkCoordinate_edgeUnit, directLinkUnit]
        by_cases hd : d' = d
        · subst d'
          simp
        · have hval : d'.1 ≠ d.1 := by
            intro hval
            exact hd (Subtype.ext hval)
          have hsum : (Sum.inl d' : LinkIndex G u v) ≠ Sum.inl d := by
            intro h
            exact hd (Sum.inl.inj h)
          simp [hval, hsum, hd]
    | inr c =>
        have hne : u ≠ v := by
          intro h
          subst v
          rcases d.2 with h' | h'
          · exact G.noLoops d.1 (h'.1.trans h'.2.symm)
          · exact G.noLoops d.1 (h'.1.trans h'.2.symm)
        simp [rawLinkCoordinate_edgeUnit, directLinkUnit,
          not_componentCut_of_directLink G u v hne c.1 d]
  · intro e he
    have hnot : ¬ G.incident d.1 w := by
      intro h
      rcases h with hs | hd
      · rcases d.2 with h' | h'
        · exact hwu (hs.symm.trans h'.1)
        · exact hwv (hs.symm.trans h'.1)
      · rcases d.2 with h' | h'
        · exact hwv (hd.symm.trans h'.2)
        · exact hwu (hd.symm.trans h'.2)
    have hne : e ≠ d.1 := by
      intro h
      subst e
      exact hnot he
    simp [edgeUnit, hne]

theorem link_pathWord_exists (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (i : LinkIndex G u v) :
    ∃ w : G.Word,
      G.boundary w = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v w = linkUnitAssignment G u v i := by
  cases i with
  | inl d =>
      obtain ⟨w, hb, hc⟩ := directLink_pathWord_exists G u v hne d
      exact ⟨w, hb, by simpa [linkUnitAssignment, directLinkUnit] using hc⟩
  | inr c =>
      obtain ⟨w, hb, hc⟩ := componentLink_pathWord_exists G u v hne c
      exact ⟨w, hb, by simpa [linkUnitAssignment, componentLinkUnit] using hc⟩

/-- Every link other than the component containing `w` has a unit path
witness avoiding `w`. -/
theorem link_pathWord_exists_avoiding (G : PhysicalGraph) (u v w : G.Vertex)
    (hne : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (k i : LinkIndex G u v) (hik : i ≠ k)
    (hcomp : ∀ c : ComponentLink G u v,
      (Sum.inr c : LinkIndex G u v) ≠ k →
        w ∉ componentVertices G u v c.1) :
    ∃ z : G.Word,
      G.boundary z = vertexUnit G u + vertexUnit G v ∧
      rawLinkCoordinate G u v z = linkUnitAssignment G u v i ∧
      ∀ e, G.incident e w → z e = 0 := by
  cases i with
  | inl d =>
      obtain ⟨z, hb, hc, hz⟩ :=
        directLink_pathWord_exists_avoiding G u v w hwu hwv d
      exact ⟨z, hb, by simpa [linkUnitAssignment, directLinkUnit] using hc, hz⟩
  | inr c =>
      have hck : (Sum.inr c : LinkIndex G u v) ≠ k := by
        intro h
        exact hik (by simpa using h)
      obtain ⟨z, hb, hc, hz⟩ :=
        componentLink_pathWord_exists_avoiding G u v w hne hwu hwv c (hcomp c hck)
      exact ⟨z, hb, by simpa [linkUnitAssignment, componentLinkUnit] using hc, hz⟩

/-- Pair-link path witnesses away from the component containing `w` give a
cycle with the desired pair coordinates that avoids `w`. -/
theorem pairLink_cycleWord_exists_avoiding (G : PhysicalGraph)
    (u v w : G.Vertex) (hne : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (k i j : LinkIndex G u v) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcomp : ∀ c : ComponentLink G u v,
      (Sum.inr c : LinkIndex G u v) ≠ k →
        w ∉ componentVertices G u v c.1) :
    ∃ x : G.CycleSpace, x ∈ cyclesAvoidingVertex G w ∧
      rawLinkCoordinate G u v x.1 =
        fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
  obtain ⟨p, hpBoundary, hpCoordinates, hpAvoid⟩ :=
    link_pathWord_exists_avoiding G u v w hne hwu hwv k i hik hcomp
  obtain ⟨q, hqBoundary, hqCoordinates, hqAvoid⟩ :=
    link_pathWord_exists_avoiding G u v w hne hwu hwv k j hjk hcomp
  let z := p + q
  have hcycle : z ∈ G.CycleSpace := by
    dsimp [z, PhysicalGraph.CycleSpace]
    exact Erdos1016.Proof.GraphicalLinkCycleLemmas.add_mem_cycleSpace_of_boundary_eq
      G p q (hpBoundary.trans hqBoundary.symm)
  let x : G.CycleSpace := ⟨z, hcycle⟩
  refine ⟨x, ?_, ?_⟩
  · change vertexStarRestriction G w x = 0
    ext e
    change z e.1 = 0
    dsimp [z]
    rw [hpAvoid e.1 e.2, hqAvoid e.1 e.2]
    simp
  · rw [show x.1 = p + q from rfl, rawLinkCoordinate_add,
      hpCoordinates, hqCoordinates]
    rfl

/-- Two link paths with equal endpoint boundary produce a cycle whose
link-coordinate vector is supported on precisely those two links. -/
theorem pairLink_cycleWord_exists (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (i j : LinkIndex G u v) (_hij : i ≠ j) :
    ∃ w : G.Word, w ∈ G.CycleSpace ∧
      rawLinkCoordinate G u v w =
        fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
  obtain ⟨p, hpBoundary, hpCoordinates⟩ := link_pathWord_exists G u v hne i
  obtain ⟨q, hqBoundary, hqCoordinates⟩ := link_pathWord_exists G u v hne j
  let w := p + q
  have hcycle : w ∈ G.CycleSpace := by
    dsimp [w, PhysicalGraph.CycleSpace]
    exact Erdos1016.Proof.GraphicalLinkCycleLemmas.add_mem_cycleSpace_of_boundary_eq
      G p q (hpBoundary.trans hqBoundary.symm)
  refine ⟨w, hcycle, ?_⟩
  rw [show w = p + q from rfl, rawLinkCoordinate_add, hpCoordinates, hqCoordinates]
  ext k
  rfl

/-- On cycle words, the unrestricted cut-coordinate map is the actual link map. -/
theorem rawLinkCoordinate_eq_linkMap (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) :
    rawLinkCoordinate G u v x.1 = GraphicalLinkMap.linkMap G u v x := by
  ext i
  cases i <;> rfl

/-- Actual graph cycles realize every pair assignment on link coordinates. -/
theorem pairLinkMap_cycleWitness (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (i j : LinkIndex G u v) (hij : i ≠ j) :
    ∃ x : G.CycleSpace,
      GraphicalLinkMap.linkMap G u v x =
        fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
  obtain ⟨w, hw, hcoords⟩ := pairLink_cycleWord_exists G u v hne i j hij
  let x : G.CycleSpace := ⟨w, hw⟩
  refine ⟨x, ?_⟩
  rw [← rawLinkCoordinate_eq_linkMap G u v x]
  exact hcoords

/-- The pair-link witness can avoid a third vertex when neither link is the
component containing it. -/
theorem pairLinkMap_cycleWitness_avoiding (G : PhysicalGraph)
    (u v w : G.Vertex) (hne : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (k i j : LinkIndex G u v) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcomp : ∀ c : ComponentLink G u v,
      (Sum.inr c : LinkIndex G u v) ≠ k →
        w ∉ componentVertices G u v c.1) :
    ∃ x : G.CycleSpace, x ∈ cyclesAvoidingVertex G w ∧
      GraphicalLinkMap.linkMap G u v x =
        fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
  obtain ⟨x, hx, hcoords⟩ := pairLink_cycleWord_exists_avoiding
    G u v w hne hwu hwv k i j hij hik hjk hcomp
  refine ⟨x, hx, ?_⟩
  rw [← rawLinkCoordinate_eq_linkMap G u v x]
  exact hcoords

end Erdos1016.Proof.GraphicalLinkPairWitnesses

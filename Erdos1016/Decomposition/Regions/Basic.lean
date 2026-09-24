import Erdos1016.Boundary.PhysicalGraph

set_option autoImplicit false

/-!
# Actual finite vertex regions of a labelled owner

All vertex sets and all edge labels belong to ONE unchanged PhysicalGraph.
The auxiliary reachability relation retains membership of every intermediate
vertex. It is proved equivalent to reachability in the actual induced graph.
Components are finite sets of actual vertices, not contracted representatives.

Source: ANALYTIC_CUBIC_INVERSE_PROOF.md, Sections 13--16.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.SafeCore

local instance instSafeCoreRegionsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- Original labelled edges joining two sets; either orientation is allowed. -/
def crossing (S T : Finset G.Vertex) : Finset G.Edge :=
  Finset.univ.filter fun e =>
    (G.src e ∈ S ∧ G.dst e ∈ T) ∨ (G.src e ∈ T ∧ G.dst e ∈ S)

def internalEdges (S : Finset G.Vertex) : Finset G.Edge :=
  Finset.univ.filter fun e => G.src e ∈ S ∧ G.dst e ∈ S

/-- This cut is ALWAYS in G, not in an intermediate deleted graph. -/
def ownerCut (S : Finset G.Vertex) : Finset G.Edge := crossing G S Sᶜ

def cutSize (S : Finset G.Vertex) : ℕ := (ownerCut G S).card

def crossSize (S T : Finset G.Vertex) : ℕ := (crossing G S T).card

@[simp] theorem mem_crossing (S T : Finset G.Vertex) (e : G.Edge) :
    e ∈ crossing G S T ↔
      (G.src e ∈ S ∧ G.dst e ∈ T) ∨ (G.src e ∈ T ∧ G.dst e ∈ S) := by
  simp [crossing]

@[simp] theorem mem_ownerCut (S : Finset G.Vertex) (e : G.Edge) :
    e ∈ ownerCut G S ↔
      (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.src e ∉ S ∧ G.dst e ∈ S) := by
  simp [ownerCut]

theorem crossing_comm (S T : Finset G.Vertex) : crossing G S T = crossing G T S := by
  ext e
  simp only [mem_crossing]
  tauto

@[simp] theorem crossSize_comm (S T : Finset G.Vertex) :
    crossSize G S T = crossSize G T S := by
  simp only [crossSize, crossing_comm G S T]

@[simp] theorem ownerCut_compl (S : Finset G.Vertex) : ownerCut G Sᶜ = ownerCut G S := by
  simp only [ownerCut, compl_compl]
  exact crossing_comm G Sᶜ S

@[simp] theorem cutSize_compl (S : Finset G.Vertex) : cutSize G Sᶜ = cutSize G S := by
  simp only [cutSize, ownerCut_compl]

/-- A path in a region, with actual vertices and actual owner adjacency. -/
inductive InReach (G : PhysicalGraph) (S : Finset G.Vertex) : G.Vertex → G.Vertex → Prop
  | refl (u : G.Vertex) (hu : u ∈ S) : InReach G S u u
  | step {u v w : G.Vertex} (p : InReach G S u v) (hw : w ∈ S)
      (edge : G.toSimpleGraph.Adj v w) : InReach G S u w

namespace InReach
variable {G} {S T : Finset G.Vertex} {u v w : G.Vertex}

theorem source (p : InReach G S u v) : u ∈ S := by
  induction p with
  | refl hu => exact hu
  | step p hw edge ih => exact ih

theorem target (p : InReach G S u v) : v ∈ S := by
  cases p with
  | refl hu => exact hu
  | step p hw edge => exact hw

theorem edge (hu : u ∈ S) (hv : v ∈ S) (h : G.toSimpleGraph.Adj u v) :
    InReach G S u v := .step (.refl u hu) hv h

theorem trans (p : InReach G S u v) (q : InReach G S v w) : InReach G S u w := by
  induction q with
  | refl hu => exact p
  | step q hw edge ih => exact .step ih hw edge

theorem symm (p : InReach G S u v) : InReach G S v u := by
  induction p with
  | refl hu => exact .refl _ hu
  | step p hw edge ih =>
      exact (InReach.edge hw p.target edge.symm).trans ih

theorem mono (hST : S ⊆ T) (p : InReach G S u v) : InReach G T u v := by
  induction p with
  | refl hu => exact .refl _ (hST hu)
  | step p hw edge ih => exact .step ih (hST hw) edge

/-- Lift the entire path, not just its endpoints, through a closed region. -/
theorem restrict (p : InReach G S u v) (hu : u ∈ T)
    (hclosed : ∀ x ∈ T, ∀ y ∈ S, G.toSimpleGraph.Adj x y → y ∈ T) :
    InReach G T u v := by
  induction p with
  | refl hu' => exact .refl _ hu
  | step p hw edge ih => exact .step ih (hclosed _ ih.target _ hw edge) edge

end InReach

/-- Nonempty connected induced vertex region. -/
def ConnectedRegion (S : Finset G.Vertex) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, InReach G S u v

/-- Closure only with respect to neighbors that remain in the ambient region U. -/
def ClosedIn (U S : Finset G.Vertex) : Prop :=
  ∀ u ∈ S, ∀ v ∈ U, G.toSimpleGraph.Adj u v → v ∈ S

/-- A literal connected component of G[U], given as actual vertices. -/
def IsComponent (U C : Finset G.Vertex) : Prop :=
  C ⊆ U ∧ ConnectedRegion G C ∧ ClosedIn G U C

/-- All actual components, including singleton components. -/
def components (U : Finset G.Vertex) : Finset (Finset G.Vertex) :=
  U.powerset.filter fun C => ConnectedRegion G C ∧ ClosedIn G U C

def componentCount (U : Finset G.Vertex) : ℕ := (components G U).card

def exteriorCount (U : Finset G.Vertex) : ℕ := componentCount G Uᶜ

@[simp] theorem mem_components (U C : Finset G.Vertex) :
    C ∈ components G U ↔ IsComponent G U C := by
  simp only [components, Finset.mem_filter, Finset.mem_powerset, IsComponent]

/-- The set of vertices reachable from u inside U. -/
def reachSet (U : Finset G.Vertex) (u : G.Vertex) : Finset G.Vertex :=
  U.filter (InReach G U u)

@[simp] theorem mem_reachSet (U : Finset G.Vertex) (u v : G.Vertex) :
    v ∈ reachSet G U u ↔ v ∈ U ∧ InReach G U u v := by
  simp only [reachSet, Finset.mem_filter]

theorem reachSet_subset (U : Finset G.Vertex) (u : G.Vertex) : reachSet G U u ⊆ U :=
  Finset.filter_subset _ _

theorem self_mem_reachSet {U : Finset G.Vertex} {u : G.Vertex} (hu : u ∈ U) :
    u ∈ reachSet G U u := (mem_reachSet G U u u).2 ⟨hu, .refl u hu⟩

theorem reachSet_closed (U : Finset G.Vertex) (u : G.Vertex) :
    ClosedIn G U (reachSet G U u) := by
  intro v hv w hw hvw
  obtain ⟨_, p⟩ := (mem_reachSet G U u v).1 hv
  exact (mem_reachSet G U u w).2 ⟨hw, .step p hw hvw⟩

theorem reachSet_connected {U : Finset G.Vertex} {u : G.Vertex} (hu : u ∈ U) :
    ConnectedRegion G (reachSet G U u) := by
  have hroot := self_mem_reachSet G hu
  refine ⟨⟨u, hroot⟩, ?_⟩
  intro v hv w hw
  have pv := ((mem_reachSet G U u v).1 hv).2.restrict hroot (reachSet_closed G U u)
  have pw := ((mem_reachSet G U u w).1 hw).2.restrict hroot (reachSet_closed G U u)
  exact pv.symm.trans pw

theorem reachSet_isComponent {U : Finset G.Vertex} {u : G.Vertex} (hu : u ∈ U) :
    IsComponent G U (reachSet G U u) :=
  ⟨reachSet_subset G U u, reachSet_connected G hu, reachSet_closed G U u⟩

theorem component_eq_reachSet {U C : Finset G.Vertex} (hC : IsComponent G U C)
    {u : G.Vertex} (hu : u ∈ C) : C = reachSet G U u := by
  apply Finset.Subset.antisymm
  · intro v hv
    exact (mem_reachSet G U u v).2 ⟨hC.1 hv, (hC.2.1.2 u hu v hv).mono hC.1⟩
  · intro v hv
    exact (((mem_reachSet G U u v).1 hv).2.restrict hu hC.2.2).target

theorem components_cover {U : Finset G.Vertex} {u : G.Vertex} (hu : u ∈ U) :
    ∃ C ∈ components G U, u ∈ C :=
  ⟨reachSet G U u, (mem_components G U _).2 (reachSet_isComponent G hu),
    self_mem_reachSet G hu⟩

theorem components_eq_of_mem {U C D : Finset G.Vertex}
    (hC : C ∈ components G U) (hD : D ∈ components G U)
    {u : G.Vertex} (huC : u ∈ C) (huD : u ∈ D) : C = D := by
  rw [component_eq_reachSet G ((mem_components G U C).1 hC) huC,
    component_eq_reachSet G ((mem_components G U D).1 hD) huD]

theorem components_disjoint {U C D : Finset G.Vertex}
    (hC : C ∈ components G U) (hD : D ∈ components G U) (hne : C ≠ D) :
    Disjoint C D := by
  apply Finset.disjoint_left.2
  intro u huC huD
  exact hne (components_eq_of_mem G hC hD huC huD)

theorem component_connected {U C : Finset G.Vertex} (hC : C ∈ components G U) :
    ConnectedRegion G C := ((mem_components G U C).1 hC).2.1

theorem component_subset {U C : Finset G.Vertex} (hC : C ∈ components G U) : C ⊆ U :=
  ((mem_components G U C).1 hC).1

theorem component_closed {U C : Finset G.Vertex} (hC : C ∈ components G U) :
    ClosedIn G U C := ((mem_components G U C).1 hC).2.2

/-- Components can be identified by closure, connectedness, and an exact cover. -/
theorem components_eq_of_cover (U : Finset G.Vertex) (P : Finset (Finset G.Vertex))
    (hvalid : ∀ C ∈ P, IsComponent G U C)
    (hcover : ∀ u ∈ U, ∃ C ∈ P, u ∈ C) : components G U = P := by
  apply Finset.Subset.antisymm
  · intro C hC
    obtain ⟨u, hu⟩ := (component_connected G hC).1
    obtain ⟨D, hD, huD⟩ := hcover u (component_subset G hC hu)
    have heq := components_eq_of_mem G hC ((mem_components G U D).2 (hvalid D hD)) hu huD
    simpa only [heq] using hD
  · intro C hC
    exact (mem_components G U C).2 (hvalid C hC)

theorem connected_components_eq_singleton {U : Finset G.Vertex}
    (hU : ConnectedRegion G U) : components G U = {U} := by
  apply components_eq_of_cover G U {U}
  · intro C hC
    have hCU : C = U := by simpa only [Finset.mem_singleton] using hC
    subst C
    exact ⟨Finset.Subset.refl _, hU, fun _ _ _ hv _ => hv⟩
  · intro u hu
    exact ⟨U, Finset.mem_singleton_self _, hu⟩

theorem componentCount_eq_one_of_connected {U : Finset G.Vertex}
    (hU : ConnectedRegion G U) : componentCount G U = 1 := by
  unfold componentCount
  rw [connected_components_eq_singleton G hU, Finset.card_singleton]

theorem connected_of_componentCount_eq_one {U : Finset G.Vertex}
    (h : componentCount G U = 1) : ConnectedRegion G U := by
  obtain ⟨C, hC⟩ := Finset.card_eq_one.1 h
  have hCU : C = U := by
    apply Finset.Subset.antisymm
    · apply component_subset G
      rw [hC]
      exact Finset.mem_singleton_self _
    · intro u hu
      obtain ⟨D, hD, hud⟩ := components_cover G hu
      have hDC : D = C := by simpa only [hC, Finset.mem_singleton] using hD
      simpa only [hDC] using hud
  subst C
  exact component_connected G (by rw [hC]; exact Finset.mem_singleton_self _)

/-- Identification with mathlib's ordinary induced-graph reachability. -/
theorem inReach_iff_induced_reachable (S : Finset G.Vertex)
    (u v : {v : G.Vertex // v ∈ S}) :
    InReach G S u.1 v.1 ↔
      (G.toSimpleGraph.induce (↑S : Set G.Vertex)).Reachable u v := by
  constructor
  · intro h
    have aux : ∀ {x y : G.Vertex}, (p : InReach G S x y) →
        (G.toSimpleGraph.induce (↑S : Set G.Vertex)).Reachable
          ⟨x, p.source⟩ ⟨y, p.target⟩ := by
      intro x y p
      induction p with
      | refl => exact SimpleGraph.Reachable.rfl
      | step p hw h ih => exact ih.trans (SimpleGraph.Adj.reachable h)
    exact aux h
  · rintro ⟨p⟩
    have hrt := (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (show (G.toSimpleGraph.induce (↑S : Set G.Vertex)).Reachable u v from ⟨p⟩)
    clear p
    induction hrt with
    | refl => exact .refl _ u.2
    | @tail b c hpath hab ih => exact .step ih c.2 hab

theorem connectedRegion_iff_induce_connected (S : Finset G.Vertex) :
    ConnectedRegion G S ↔
      (G.toSimpleGraph.induce (↑S : Set G.Vertex)).Connected := by
  constructor
  · intro h
    haveI : Nonempty (↑S : Set G.Vertex) := by
      obtain ⟨u, hu⟩ := h.1
      exact ⟨⟨u, by simpa using hu⟩⟩
    refine ⟨?_⟩
    intro u v
    exact (inReach_iff_induced_reachable G S u v).1 (h.2 u.1 u.2 v.1 v.2)
  · intro h
    obtain ⟨u⟩ := h.nonempty
    refine ⟨⟨u.1, u.2⟩, ?_⟩
    intro v hv w hw
    exact (inReach_iff_induced_reachable G S ⟨v, hv⟩ ⟨w, hw⟩).2 (h _ _)

/-- The finite component model has exactly the usual graph-theoretic count. -/
theorem componentCount_eq_natCard (S : Finset G.Vertex) :
    componentCount G S =
      Nat.card (G.toSimpleGraph.induce (↑S : Set G.Vertex)).ConnectedComponent := by
  let H := G.toSimpleGraph.induce (↑S : Set G.Vertex)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let root (C : {C // C ∈ components G S}) : {v : G.Vertex // v ∈ S} :=
    ⟨Classical.choose (component_connected G C.2).1,
      component_subset G C.2 (Classical.choose_spec (component_connected G C.2).1)⟩
  let f (C : {C // C ∈ components G S}) : H.ConnectedComponent :=
    H.connectedComponentMk (root C)
  have hf : Function.Bijective f := by
    constructor
    · intro C D heq
      have hp : InReach G S (root C).1 (root D).1 :=
        (inReach_iff_induced_reachable G S _ _).2
          (SimpleGraph.ConnectedComponent.exact heq)
      have hc : (root C).1 ∈ C.1 := Classical.choose_spec (component_connected G C.2).1
      have hd : (root D).1 ∈ D.1 := Classical.choose_spec (component_connected G D.2).1
      have hdC := (hp.restrict hc (component_closed G C.2)).target
      exact Subtype.ext (components_eq_of_mem G C.2 D.2 hdC hd)
    · intro c
      obtain ⟨v, hv⟩ := c.exists_rep
      obtain ⟨C, hC, hvC⟩ := components_cover G v.2
      refine ⟨⟨C, hC⟩, ?_⟩
      have hr : (root ⟨C, hC⟩).1 ∈ C := Classical.choose_spec (component_connected G hC).1
      have hp := ((component_connected G hC).2 _ hr _ hvC).mono (component_subset G hC)
      change H.connectedComponentMk (root ⟨C, hC⟩) = c
      rw [← hv]
      exact SimpleGraph.ConnectedComponent.sound
        ((inReach_iff_induced_reachable G S _ _).1 hp)
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  simpa only [componentCount, Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

/-- Compatibility with the already delivered trace theorem. -/
theorem exteriorCount_eq_original (S : Finset G.Vertex) :
    exteriorCount G S = G.originalExteriorComponents S := by
  unfold exteriorCount PhysicalGraph.originalExteriorComponents
  rw [componentCount_eq_natCard]
  have hsets : (↑(Sᶜ) : Set G.Vertex) = {v | v ∉ S} := by
    ext v
    simp
  rw [hsets]

end Erdos1016.SafeCore

import Erdos1016.Cleanup.Corridors.EdgeSeedConstruction
import Erdos1016.Cleanup.Corridors.CoreIncidenceCoverage
import Erdos1016.Cleanup.Paths.SingleCorridorRoute

set_option autoImplicit false

noncomputable section

local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidablePred (fun v : V => v ∈ c.supp) := fun v =>
    Classical.propDecidable _
  exact Subtype.fintype _

namespace Erdos1016.Proof.CoreComponentAssembly

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.EdgeSeedConstruction
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.ComponentCorridorConstruction
open Erdos1016.Proof.PhysicalDegreeTwoCoreBoundaryAccounting
open Erdos1016.Proof.GraphicalLinkPairWitnesses
open Erdos1016.Proof.WalkEdgeLift
open Erdos1016.Proof.CoreIncidenceCoverage
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.SingleCorridorRoute

/-- A core corridor system records the edge partition over all edges touching
the degree-two core. Protected-to-protected edges are added separately. -/
structure CoreCorridorSystem (G : PhysicalGraph) (P₀ : Finset G.Vertex) where
  corridors : List (PhysicalCorridor G)
  core_edge_cover : ∀ e : G.Edge,
    (G.src e ∉ protectedOrBranch G P₀ ∨ G.dst e ∉ protectedOrBranch G P₀) →
      ∃ C ∈ corridors, e ∈ C.support
  edge_disjoint : ∀ C ∈ corridors, ∀ D ∈ corridors,
    C ≠ D → Disjoint C.support D.support
  edges_touch_core : ∀ C ∈ corridors, ∀ e ∈ C.support,
    G.src e ∉ protectedOrBranch G P₀ ∨ G.dst e ∉ protectedOrBranch G P₀
  internal_unprotected_degree_two : ∀ C ∈ corridors,
    ∀ i : Fin (C.vertices.length - 2),
      let v := C.vertices.get ⟨i.val + 1, by
        have h := C.vertices_length
        omega⟩
      v ∉ P₀ ∧ G.degree v = 2
  maximal : ∀ C ∈ corridors,
    ∀ e : G.Edge, e ∉ C.support →
      (∃ v, v ∉ P₀ ∧ G.degree v = 2 ∧
        ((G.src e = v ∧ (∃ f ∈ C.support, G.dst f = v ∨ G.src f = v)) ∨
         (G.dst e = v ∧ (∃ f ∈ C.support, G.dst f = v ∨ G.src f = v)))) →
      False

abbrev CoreComponent (G : PhysicalGraph) (P : Finset G.Vertex) :=
  (G.toSimpleGraph.induce
    {v | v ∉ protectedOrBranch G P}).ConnectedComponent

/-- Component-indexed corridor data is a more local interface than a global
edge partition. `incident_edge_cover` is the key local fact: every edge at a
vertex of a core component lies on that component's corridor. The remaining
fields state edge ownership and the geometric properties needed globally. -/
structure CoreCorridorChoices (G : PhysicalGraph) (P : Finset G.Vertex) where
  corridor : CoreComponent G P → PhysicalCorridor G
  corridor_edges_nonempty : ∀ c, (corridor c).edges ≠ []
  edge_owned : ∀ c e, e ∈ (corridor c).support →
    G.src e ∈ componentVertices G P c ∨ G.dst e ∈ componentVertices G P c
  incident_edge_cover : ∀ c e,
    (G.src e ∈ componentVertices G P c ∨ G.dst e ∈ componentVertices G P c) →
      e ∈ (corridor c).support
  internal_unprotected_degree_two : ∀ c,
    ∀ i : Fin ((corridor c).vertices.length - 2),
      let v := (corridor c).vertices.get ⟨i.val + 1, by
        have h := (corridor c).vertices_length
        omega⟩
      v ∉ P ∧ G.degree v = 2
  endpoints_protected : ∀ c, ∃ u w,
    (corridor c).vertices.head? = some u ∧
    (corridor c).vertices.getLast? = some w ∧
    u ∈ protectedOrBranch G P ∧ w ∈ protectedOrBranch G P
  protected_support_endpoints : ∀ c e, e ∈ (corridor c).support →
    (G.src e ∈ protectedOrBranch G P →
      G.src e = corridorStart (corridor c) ∨
        G.src e = corridorFinish (corridor c)) ∧
    (G.dst e ∈ protectedOrBranch G P →
      G.dst e = corridorStart (corridor c) ∨
        G.dst e = corridorFinish (corridor c))

private theorem selectedPhysicalEdge_adjacency (G : PhysicalGraph) (e : G.Edge) :
    G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
  exact ⟨e, by simp [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph],
    Or.inl ⟨rfl, rfl⟩⟩

private theorem endpoint_in_component_of_owned_edge
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (S : CoreCorridorChoices G P) (c : CoreComponent G P)
    (f : G.Edge) (hf : f ∈ (S.corridor c).support)
    (v : G.Vertex) (hv : v ∉ protectedOrBranch G P)
    (hfv : G.src f = v ∨ G.dst f = v) :
    v ∈ componentVertices G P c := by
  rcases S.edge_owned c f hf with hs | ht
  · rcases hfv with hsrc | hdst
    · simpa [hsrc] using hs
    · exact componentVertices_adj_closed G P c hs hv
        (by
          have hadj := selectedPhysicalEdge_adjacency G f
          simpa [hdst] using hadj)
  · rcases hfv with hsrc | hdst
    · exact componentVertices_adj_closed G P c ht hv
        (by
          have hadj := selectedPhysicalEdge_adjacency G f
          simpa [hsrc] using hadj.symm)
    · simpa [hdst] using ht

/-- Component ownership plus local incident-edge coverage assemble a genuine
`CoreCorridorSystem`. Thus cover, disjointness, and maximality reduce to the
single local incident-edge lemma for the selected component corridors. -/
noncomputable def CoreCorridorChoices.toSystem
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (S : CoreCorridorChoices G P) : CoreCorridorSystem G P := by
  classical
  let comps : Finset (CoreComponent G P) := Finset.univ
  let cs := comps.toList.map S.corridor
  refine ⟨cs, ?_, ?_, ?_, ?_, ?_⟩
  · intro e hcore
    obtain ⟨c, hcOwner, _⟩ := core_edge_has_unique_component G P e hcore
    refine ⟨S.corridor c, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨c, Finset.mem_toList.mpr (Finset.mem_univ c), rfl⟩
    · exact S.incident_edge_cover c e hcOwner
  · intro C hC D hD hne
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hC
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hD
    apply Finset.disjoint_left.mpr
    intro e hec hed
    have hce := S.edge_owned c e hec
    have hde := S.edge_owned d e hed
    have hcore : G.src e ∉ protectedOrBranch G P ∨
        G.dst e ∉ protectedOrBranch G P := by
      rcases hce with h | h
      · exact Or.inl (componentVertices_mem_not_protected G P c h)
      · exact Or.inr (componentVertices_mem_not_protected G P c h)
    obtain ⟨owner, _, huniq⟩ := core_edge_has_unique_component G P e hcore
    have hco : c = owner := huniq c hce
    have hdo : d = owner := huniq d hde
    have hcd : c = d := hco.trans hdo.symm
    subst d
    exact hne (congrArg S.corridor hco)
  · intro C hC e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hC
    rcases S.edge_owned c e he with hsrc | hdst
    · exact Or.inl (componentVertices_mem_not_protected G P c hsrc)
    · exact Or.inr (componentVertices_mem_not_protected G P c hdst)
  · intro C hC i
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hC
    exact S.internal_unprotected_degree_two c i
  · intro C hC e heC hattach
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hC
    rcases hattach with ⟨v, hvP, hvdeg, hinc⟩
    have hvQ : v ∉ protectedOrBranch G P := by
      intro hv
      rcases Finset.mem_union.mp hv with hv₀ | hv₃
      · exact hvP hv₀
      · have hdegree3 := Finset.mem_filter.mp hv₃ |>.2
        omega
    rcases hinc with hsrc | hdst
    · rcases hsrc with ⟨hsrcv, f, hf, hfv⟩
      have hfv' : G.src f = v ∨ G.dst f = v := by
        rcases hfv with hdstv | hsrcv'
        · exact Or.inr hdstv
        · exact Or.inl hsrcv'
      have hvComp := endpoint_in_component_of_owned_edge G P S c f hf v hvQ hfv'
      exact heC (S.incident_edge_cover c e (Or.inl (hsrcv ▸ hvComp)))
    · rcases hdst with ⟨hdstv, f, hf, hfv⟩
      have hfv' : G.src f = v ∨ G.dst f = v := by
        rcases hfv with hdstv' | hsrcv'
        · exact Or.inr hdstv'
        · exact Or.inl hsrcv'
      have hvComp := endpoint_in_component_of_owned_edge G P S c f hf v hvQ hfv'
      exact heC (S.incident_edge_cover c e (Or.inr (hdstv ▸ hvComp)))

/-- Every component of the protected-or-branch complement has an attached
physical corridor whose exact interior path is that component. This is the
uniform local corridor input to the global list assembly. -/
theorem exists_core_component_attached_corridor
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (c : (G.toSimpleGraph.induce
      {v | v ∉ protectedOrBranch G P}).ConnectedComponent) :
    ∃ (a b u w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
      (hleft : G.toSimpleGraph.Adj u a) (hright : G.toSimpleGraph.Adj b w)
      (Ccorr : PhysicalCorridor G),
      p.IsPath ∧
      p.support.toFinset = componentVertices G P c ∧
      u ∉ componentVertices G P c ∧ u ∈ protectedOrBranch G P ∧
      w ∉ componentVertices G P c ∧ w ∈ protectedOrBranch G P ∧
      Ccorr.vertices = u :: p.support ++ [w] ∧
      Ccorr.edges = physicalEdgeOfAdj G hleft ::
        (liftedEdges G p ++ [physicalEdgeOfAdj G hright]) ∧
      ∀ v, v ∈ p.support →
        v ∉ protectedOrBranch G P ∧ G.degree v = 2 := by
  classical
  let Q := protectedOrBranch G P
  have hQ : Q.Nonempty := protectedOrBranch_nonempty G P hP
  have hdegreeQ : ∀ v, v ∉ Q → G.degree v = 2 := by
    intro v hv
    have hvP : v ∉ P := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inl h))
    rcases hdegree v hvP with htwo | hthree
    · exact htwo
    · have hvbranch : v ∈ Finset.univ.filter (fun x => G.degree x = 3) := by
        simp [hthree]
      exact (hv (Finset.mem_union.mpr (Or.inr hvbranch))).elim
  obtain ⟨a, b, u, w, p, hleft, hright, Ccorr, hp, hps,
      huC, huQ, hwC, hwQ, hverts, hedges⟩ :=
    exists_physical_corridor_for_component G Q hconn hQ hdegreeQ c
  have hdegpath : ∀ v, v ∈ p.support → v ∉ Q ∧ G.degree v = 2 := by
    intro v hv
    have hvFin : v ∈ p.support.toFinset := List.mem_toFinset.mpr hv
    rw [hps] at hvFin
    obtain ⟨z, hz, hvz⟩ := Finset.mem_map.mp hvFin
    have hvz' : z.1 = v := hvz
    subst v
    exact ⟨z.2, hdegreeQ z.1 z.2⟩
  have hps' : p.support.toFinset = componentVertices G P c := by
    rw [hps]
    ext v
    simp [componentVertices, Q, Finset.mem_map, Set.mem_toFinset]
  have huC' : u ∉ componentVertices G P c := by
    simpa [componentVertices, Q, Finset.mem_map, Set.mem_toFinset] using huC
  have hwC' : w ∉ componentVertices G P c := by
    simpa [componentVertices, Q, Finset.mem_map, Set.mem_toFinset] using hwC
  exact ⟨a, b, u, w, p, hleft, hright, Ccorr, hp, hps',
    huC', huQ, hwC', hwQ, hverts, hedges, hdegpath⟩



/-- A single component corridor simultaneously has exact local edge ownership,
incident-edge coverage, and degree two at every internal vertex. -/
theorem exists_core_component_corridor_facts
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (c : CoreComponent G P) :
    ∃ C : PhysicalCorridor G,
      (∀ e ∈ C.support,
        G.src e ∈ componentVertices G P c ∨ G.dst e ∈ componentVertices G P c) ∧
      (∀ e, (G.src e ∈ componentVertices G P c ∨
        G.dst e ∈ componentVertices G P c) → e ∈ C.support) ∧
      (∀ i : Fin (C.vertices.length - 2),
        let v := C.vertices.get ⟨i.val + 1, by
          have h := C.vertices_length
          omega⟩
        v ∉ P ∧ G.degree v = 2) ∧ C.edges ≠ [] ∧
      (∃ u w, C.vertices.head? = some u ∧ C.vertices.getLast? = some w ∧
        u ∈ protectedOrBranch G P ∧ w ∈ protectedOrBranch G P) ∧
      (∀ e, e ∈ C.support →
        (G.src e ∈ protectedOrBranch G P →
          G.src e = corridorStart C ∨ G.src e = corridorFinish C) ∧
        (G.dst e ∈ protectedOrBranch G P →
          G.dst e = corridorStart C ∨ G.dst e = corridorFinish C)) := by
  classical
  obtain ⟨a, b, u, w, p, hleft, hright, C, hp, hps,
      huC, huQ, hwC, hwQ, hverts, hedges, hdegreePath⟩ :=
    exists_core_component_attached_corridor G P hconn hP hdegree c
  have hpathComp : ∀ v, v ∈ p.support → v ∈ componentVertices G P c := by
    intro v hv
    have hv' : v ∈ p.support.toFinset := List.mem_toFinset.mpr hv
    rw [hps] at hv'
    exact hv'
  have hstart : a ∈ componentVertices G P c :=
    hpathComp a p.start_mem_support
  have hend : b ∈ componentVertices G P c :=
    hpathComp b p.end_mem_support
  have howned : ∀ e, e ∈ C.support →
      G.src e ∈ componentVertices G P c ∨ G.dst e ∈ componentVertices G P c := by
    intro e he
    have helist : e ∈ C.edges := List.mem_toFinset.mp he
    rw [hedges] at helist
    simp only [List.mem_cons] at helist
    rcases helist with heleft | hetail
    · subst e
      rcases physicalEdgeOfAdj_spec G hleft with hs | hs
      · right
        rw [hs.2]
        exact hstart
      · left
        rw [hs.1]
        exact hstart
    · rcases List.mem_append.mp hetail with hepath | heright
      · obtain ⟨hs, ht⟩ := lifted_edge_endpoints_mem_support G p hepath
        exact Or.inl (hpathComp _ hs)
      · simp only [List.mem_singleton] at heright
        subst e
        rcases physicalEdgeOfAdj_spec G hright with hs | hs
        · left
          rw [hs.1]
          exact hend
        · right
          rw [hs.2]
          exact hend
  have hcover : ∀ e, (G.src e ∈ componentVertices G P c ∨
      G.dst e ∈ componentVertices G P c) → e ∈ C.support := by
    intro e he
    exact attached_core_corridor_incident_edge_mem_support G P hdegree c
      a b u w p C hps hverts e he
  have hinternal : ∀ i : Fin (C.vertices.length - 2),
      let v := C.vertices.get ⟨i.val + 1, by
        have h := C.vertices_length
        omega⟩
      v ∉ P ∧ G.degree v = 2 := by
    intro i
    dsimp
    have hlen : C.vertices.length - 2 = p.support.length := by
      rw [hverts]
      simp
    have hi : i.val < p.support.length := by
      rw [← hlen]
      exact i.isLt
    let j : Fin p.support.length := ⟨i.val, hi⟩
    have hidx : C.vertices.get ⟨i.val + 1, by
        have h := C.vertices_length
        omega⟩ = p.support.get j := by
      change C.vertices[i.val + 1] = p.support[j.val]
      simp [hverts, j, List.getElem_append_left hi]
    have hv := hdegreePath (p.support.get j) (List.get_mem p.support j)
    constructor
    · intro hvP
      apply hv.1
      have hPpath : p.support.get j ∈ P := by
        rw [← hidx]
        exact hvP
      exact Finset.mem_union.mpr (Or.inl hPpath)
    · have hvDegree : G.degree (p.support.get j) = 2 := hv.2
      rw [← hidx] at hvDegree
      exact hvDegree
  have hnonempty : C.edges ≠ [] := by
    intro he
    rw [hedges] at he
    cases he
  have hendpoints :
      ∃ x y, C.vertices.head? = some x ∧ C.vertices.getLast? = some y ∧
        x ∈ protectedOrBranch G P ∧ y ∈ protectedOrBranch G P := by
    refine ⟨u, w, ?_, ?_, huQ, hwQ⟩
    · rw [hverts, List.head?_append_of_ne_nil _ (by simp)]
      simp
    · rw [hverts, List.getLast?_append_of_ne_nil _ (by simp)]
      simp
  have hhead : C.vertices.head? = some u := by
    rw [hverts, List.head?_append_of_ne_nil _ (by simp)]
    simp
  have hlast : C.vertices.getLast? = some w := by
    rw [hverts, List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  have huStart : u = corridorStart C :=
    Option.some.inj (hhead.symm.trans (corridorStart_head? C))
  have hwFinish : w = corridorFinish C :=
    Option.some.inj (hlast.symm.trans (corridorFinish_getLast? C))
  have haQ : a ∉ protectedOrBranch G P :=
    componentVertices_mem_not_protected G P c hstart
  have hbQ : b ∉ protectedOrBranch G P :=
    componentVertices_mem_not_protected G P c hend
  have hsrcEndpoint : ∀ e, e ∈ C.support →
      G.src e ∈ protectedOrBranch G P → G.src e = u ∨ G.src e = w := by
    intro e he hq
    have helist : e ∈ C.edges := List.mem_toFinset.mp he
    rw [hedges] at helist
    simp only [List.mem_cons] at helist
    rcases helist with hleftEdge | htail
    · subst e
      rcases physicalEdgeOfAdj_spec G hleft with hs | hs
      · exact Or.inl hs.1
      · exact False.elim (haQ (hs.1 ▸ hq))
    · rcases List.mem_append.mp htail with hpath | hrightEdge
      · obtain ⟨hs, _⟩ := lifted_edge_endpoints_mem_support G p hpath
        exact False.elim ((hdegreePath _ hs).1 hq)
      · simp only [List.mem_singleton] at hrightEdge
        subst e
        rcases physicalEdgeOfAdj_spec G hright with hs | hs
        · exact False.elim (hbQ (hs.1 ▸ hq))
        · exact Or.inr hs.1
  have hdstEndpoint : ∀ e, e ∈ C.support →
      G.dst e ∈ protectedOrBranch G P → G.dst e = u ∨ G.dst e = w := by
    intro e he hq
    have helist : e ∈ C.edges := List.mem_toFinset.mp he
    rw [hedges] at helist
    simp only [List.mem_cons] at helist
    rcases helist with hleftEdge | htail
    · subst e
      rcases physicalEdgeOfAdj_spec G hleft with hs | hs
      · exact False.elim (haQ (hs.2 ▸ hq))
      · exact Or.inl hs.2
    · rcases List.mem_append.mp htail with hpath | hrightEdge
      · obtain ⟨_, ht⟩ := lifted_edge_endpoints_mem_support G p hpath
        exact False.elim ((hdegreePath _ ht).1 hq)
      · simp only [List.mem_singleton] at hrightEdge
        subst e
        rcases physicalEdgeOfAdj_spec G hright with hs | hs
        · exact Or.inr hs.2
        · exact False.elim (hbQ (hs.2 ▸ hq))
  have hprotectedSupport : ∀ e, e ∈ C.support →
      (G.src e ∈ protectedOrBranch G P →
        G.src e = corridorStart C ∨ G.src e = corridorFinish C) ∧
      (G.dst e ∈ protectedOrBranch G P →
        G.dst e = corridorStart C ∨ G.dst e = corridorFinish C) := by
    intro e he
    constructor
    · intro hq
      rcases hsrcEndpoint e he hq with hu | hw
      · exact Or.inl (hu.trans huStart)
      · exact Or.inr (hw.trans hwFinish)
    · intro hq
      rcases hdstEndpoint e he hq with hu | hw
      · exact Or.inl (hu.trans huStart)
      · exact Or.inr (hw.trans hwFinish)
  exact ⟨C, howned, hcover, hinternal, hnonempty, hendpoints, hprotectedSupport⟩

/-- The component-level existence theorem selects one corridor per core
component and packages the resulting ownership, coverage, and degree facts. -/
noncomputable def canonicalCoreCorridorChoices
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) :
    CoreCorridorChoices G P := by
  classical
  let localFacts : ∀ c : CoreComponent G P,
      ∃ C : PhysicalCorridor G,
        (∀ e ∈ C.support,
          G.src e ∈ componentVertices G P c ∨
            G.dst e ∈ componentVertices G P c) ∧
        (∀ e, (G.src e ∈ componentVertices G P c ∨
          G.dst e ∈ componentVertices G P c) → e ∈ C.support) ∧
        (∀ i : Fin (C.vertices.length - 2),
          let v := C.vertices.get ⟨i.val + 1, by
            have h := C.vertices_length
            omega⟩
        v ∉ P ∧ G.degree v = 2) ∧ C.edges ≠ [] ∧
        (∃ u w, C.vertices.head? = some u ∧ C.vertices.getLast? = some w ∧
          u ∈ protectedOrBranch G P ∧ w ∈ protectedOrBranch G P) ∧
        (∀ e, e ∈ C.support →
          (G.src e ∈ protectedOrBranch G P →
            G.src e = corridorStart C ∨ G.src e = corridorFinish C) ∧
          (G.dst e ∈ protectedOrBranch G P →
            G.dst e = corridorStart C ∨ G.dst e = corridorFinish C)) :=
    fun c => exists_core_component_corridor_facts G P hconn hP hdegree c
  let chosen : CoreComponent G P → PhysicalCorridor G := fun c =>
    Classical.choose (localFacts c)
  refine ⟨chosen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact (Classical.choose_spec (localFacts c)).2.2.2.1
  · intro c e he
    exact (Classical.choose_spec (localFacts c)).1 e he
  · intro c e he
    exact (Classical.choose_spec (localFacts c)).2.1 e he
  · intro c i
    exact (Classical.choose_spec (localFacts c)).2.2.1 i
  · intro c
    exact (Classical.choose_spec (localFacts c)).2.2.2.2.1
  · intro c e he
    exact (Classical.choose_spec (localFacts c)).2.2.2.2.2 e he

/-- The exact remaining data needed to assemble component corridors into a
full partition: a disjoint edge-covering family for every edge touching the
degree-two core, with internal-vertex and maximality properties. The theorem
below supplies all protected-to-protected edges as singleton corridors. -/
def protectedProtectedEdges (G : PhysicalGraph) (P₀ : Finset G.Vertex) :
    Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    G.src e ∈ protectedOrBranch G P₀ ∧ G.dst e ∈ protectedOrBranch G P₀

theorem protectedProtectedEdges_mem
    (G : PhysicalGraph) (P₀ : Finset G.Vertex) (e : G.Edge) :
    e ∈ protectedProtectedEdges G P₀ ↔
      G.src e ∈ protectedOrBranch G P₀ ∧ G.dst e ∈ protectedOrBranch G P₀ := by
  classical
  simp [protectedProtectedEdges]



private theorem singletonCore_disjoint
    (G : PhysicalGraph) (P₀ : Finset G.Vertex)
    (S : CoreCorridorSystem G P₀)
    (e : G.Edge) (he : e ∈ protectedProtectedEdges G P₀)
    (C : PhysicalCorridor G) (hC : C ∈ S.corridors) :
    Disjoint C.support (singletonCorridor G e).support := by
  have heCore : G.src e ∈ protectedOrBranch G P₀ ∧
      G.dst e ∈ protectedOrBranch G P₀ :=
    (protectedProtectedEdges_mem G P₀ e).mp he
  have heNot : e ∉ C.support := by
    intro hm
    have htouch := S.edges_touch_core C hC e hm
    rcases htouch with hs | hd
    · exact hs heCore.1
    · exact hd heCore.2
  rw [singletonCorridor_support]
  exact Finset.disjoint_singleton_right.mpr heNot

/-- A core corridor system plus singleton protected-to-protected edges yields
a `CorridorPartition` of the entire physical graph. The proof verifies edge
coverage, disjointness, witness retention, the internal degree condition, and
maximality for the assembled family. -/
def assembleCorridorPartition
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (S : CoreCorridorSystem G P) :
    CorridorPartition G P W := by
  classical
  let Qedges := protectedProtectedEdges G P
  let cs := S.corridors ++ (Qedges.toList.map (singletonCorridor G))
  refine ⟨cs, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases hQ : e ∈ Qedges
    · refine ⟨singletonCorridor G e, ?_, ?_⟩
      · apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨e, Finset.mem_toList.mpr hQ, rfl⟩)
      · rw [singletonCorridor_support]
        simp
    · have hnot : G.src e ∉ protectedOrBranch G P ∨
          G.dst e ∉ protectedOrBranch G P := by
        by_contra h
        push_neg at h
        exact hQ ((protectedProtectedEdges_mem G P e).mpr h)
      obtain ⟨C, hC, heC⟩ := S.core_edge_cover e hnot
      exact ⟨C, List.mem_append.mpr (Or.inl hC), heC⟩
  · intro C hC D hD hne
    have hCMem := List.mem_append.mp hC
    have hDMem := List.mem_append.mp hD
    rcases hCMem with hCcore | hCsingle
    · rcases hDMem with hDcore | hDsingle
      · exact S.edge_disjoint C hCcore D hDcore hne
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hDsingle
        have heQ : e ∈ Qedges := Finset.mem_toList.mp he
        exact singletonCore_disjoint G P S e heQ C hCcore
    · rcases hDMem with hDcore | hDsingle
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hCsingle
        have heQ : e ∈ Qedges := Finset.mem_toList.mp he
        exact (singletonCore_disjoint G P S e heQ D hDcore).symm
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hCsingle
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hDsingle
        have hef : e ≠ f := by
          intro heq
          apply hne
          subst f
          rfl
        rw [singletonCorridor_support, singletonCorridor_support]
        exact Finset.disjoint_singleton.mpr hef
  · intro e heW
    have heP : G.src e ∈ P ∧ G.dst e ∈ P := hW e heW
    have heQ : e ∈ Qedges := by
      apply (protectedProtectedEdges_mem G P e).mpr
      exact ⟨Finset.mem_union.mpr (Or.inl heP.1),
        Finset.mem_union.mpr (Or.inl heP.2)⟩
    refine ⟨singletonCorridor G e, ?_, ?_⟩
    · apply List.mem_append.mpr
      exact Or.inr (List.mem_map.mpr ⟨e, Finset.mem_toList.mpr heQ, rfl⟩)
    · exact singletonCorridor_support G e
  · intro C hC i
    rcases List.mem_append.mp hC with hcore | hsingle
    · exact S.internal_unprotected_degree_two C hcore i
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hsingle
      have hi : i.val < 0 := by
        simpa [singletonCorridor] using i.isLt
      omega
  · intro C hC e heC hattach
    rcases List.mem_append.mp hC with hcore | hsingle
    · exact S.maximal C hcore e heC hattach
    · obtain ⟨f, hf, hCf⟩ := List.mem_map.mp hsingle
      subst C
      have hfQ := (protectedProtectedEdges_mem G P f).mp (Finset.mem_toList.mp hf)
      have hsupp : (singletonCorridor G f).support = {f} :=
        singletonCorridor_support G f
      rw [hsupp] at heC
      have hfe : f ≠ e := by
        intro hEq
        exact heC (hEq ▸ Finset.mem_singleton_self f)
      rcases hattach with ⟨v, hv₀, hvdeg, hinc⟩
      have hvQ : v ∉ protectedOrBranch G P := by
        intro hvQ
        rcases Finset.mem_union.mp hvQ with hvP | hvBranch
        · exact hv₀ hvP
        · have hdegree3 := Finset.mem_filter.mp hvBranch |>.2
          omega
      rcases hinc with hsrc | hdst
      · rcases hsrc with ⟨hsrcEq, g, hg, hgf⟩
        have hgEq : g = f := by
          rw [hsupp] at hg
          exact Finset.mem_singleton.mp hg
        subst g
        rcases hgf with hdstF | hsrcF
        · exact hvQ (hdstF ▸ hfQ.2)
        · exact hvQ (hsrcF ▸ hfQ.1)
      · rcases hdst with ⟨hdstEq, g, hg, hgf⟩
        have hgEq : g = f := by
          rw [hsupp] at hg
          exact Finset.mem_singleton.mp hg
        subst g
        rcases hgf with hdstF | hsrcF
        · exact hvQ (hdstF ▸ hfQ.2)
        · exact hvQ (hsrcF ▸ hfQ.1)

/- The componentwise spanning-path construction, together with the
core-component ownership facts, supplies the global system without any
additional choices from the caller. -/
noncomputable def exists_corridor_partition_of_degree_two_three
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P) :
    CorridorPartition G P W := by
  exact assembleCorridorPartition G P W hW
    ((canonicalCoreCorridorChoices G P hconn hP hdegree).toSystem G P)

/-- Every corridor in the canonical partition has at least one edge. -/
theorem corridor_partition_edges_nonempty_of_degree_two_three
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P) :
    ∀ C, C ∈ (exists_corridor_partition_of_degree_two_three
      G P W hconn hP hdegree hW).corridors → C.edges ≠ [] := by
  classical
  let S := canonicalCoreCorridorChoices G P hconn hP hdegree
  let D := assembleCorridorPartition G P W hW (S.toSystem G P)
  change ∀ C, C ∈ D.corridors → C.edges ≠ []
  intro C hC
  change C ∈ (S.toSystem G P).corridors ++
    (protectedProtectedEdges G P).toList.map (singletonCorridor G) at hC
  rcases List.mem_append.mp hC with hcore | hprotected
  · change C ∈ Finset.univ.toList.map S.corridor at hcore
    obtain ⟨c, _, hCeq⟩ := List.mem_map.mp hcore
    rw [← hCeq]
    exact S.corridor_edges_nonempty c
  · obtain ⟨e, _, hCeq⟩ := List.mem_map.mp hprotected
    rw [← hCeq]
    simp [singletonCorridor]



/-- Both endpoint vertices of every corridor in the canonical assembled
partition lie in the retained protected-or-branch vertex set. -/
theorem canonical_assembled_partition_endpoints_retained
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P) :
    ∀ C, C ∈ (assembleCorridorPartition G P W hW
      ((canonicalCoreCorridorChoices G P hconn hP hdegree).toSystem G P)).corridors →
      SingleCorridorRoute.corridorStart C ∈ protectedOrBranch G P ∧
        SingleCorridorRoute.corridorFinish C ∈ protectedOrBranch G P := by
  classical
  let choices := canonicalCoreCorridorChoices G P hconn hP hdegree
  let S := choices.toSystem G P
  intro C hC
  have hC' : C ∈ S.corridors ++
      (protectedProtectedEdges G P).toList.map (singletonCorridor G) := by
    simpa [assembleCorridorPartition, S, protectedProtectedEdges] using hC
  rcases List.mem_append.mp hC' with hcore | hsingle
  · change C ∈ Finset.univ.toList.map choices.corridor at hcore
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hcore
    obtain ⟨u, w, huHead, hwLast, huQ, hwQ⟩ := choices.endpoints_protected c
    have hstart : SingleCorridorRoute.corridorStart
        (choices.corridor c) = u := by
      have h := (SingleCorridorRoute.corridorStart_head?
        (choices.corridor c)).symm.trans huHead
      exact Option.some.inj h
    have hfinish : SingleCorridorRoute.corridorFinish
        (choices.corridor c) = w := by
      have h := (SingleCorridorRoute.corridorFinish_getLast?
        (choices.corridor c)).symm.trans hwLast
      exact Option.some.inj h
    exact ⟨hstart ▸ huQ, hfinish ▸ hwQ⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hsingle
    have heQ := (protectedProtectedEdges_mem G P e).mp (Finset.mem_toList.mp he)
    constructor
    · simpa [SingleCorridorRoute.corridorStart,
        singletonCorridor] using heQ.1
    · simpa [SingleCorridorRoute.corridorFinish,
        singletonCorridor] using heQ.2

end Erdos1016.Proof.CoreComponentAssembly

end

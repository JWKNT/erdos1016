import Erdos1016.Cleanup.Paths.ComponentBoundaryEndpoints
import Erdos1016.Cleanup.Corridors.TreeBoundaryAttachments
import Erdos1016.Cleanup.Corridors.AttachedPathConstruction

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidablePred (fun v : V => v ∈ c.supp) := fun v =>
    Classical.propDecidable _
  exact Subtype.fintype _

namespace Erdos1016.Proof.ComponentCorridorConstruction

open Erdos1016
open SimpleGraph
open Erdos1016.Proof.GraphicalLinkPairWitnesses
open Erdos1016.Proof.WalkEdgeLift
open Erdos1016.Proof.PhysicalPartition

/-- Every labelled edge lifted from a walk has both of its physical endpoints
among the walk support vertices. -/
theorem lifted_edge_endpoints_mem_support (G : PhysicalGraph) :
    ∀ {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) {e : G.Edge},
      e ∈ liftedEdges G p → G.src e ∈ p.support ∧ G.dst e ∈ p.support := by
  intro u v p
  induction p with
  | nil => intro e he; simp [liftedEdges] at he
  | @cons a b c h p ih =>
      intro e he
      simp only [liftedEdges, List.mem_cons] at he
      rcases he with rfl | he
      · rcases physicalEdgeOfAdj_spec G h with hspec | hspec
        · exact ⟨by simp [hspec.1, Walk.support_cons],
            by simp [hspec.2, Walk.support_cons]⟩
        · exact ⟨by simpa [hspec.1, Walk.support_cons] using (Walk.start_mem_support p),
            by simp [hspec.2, Walk.support_cons]⟩
      · obtain ⟨hs, ht⟩ := ih he
        exact ⟨List.mem_cons.mpr (Or.inr hs), List.mem_cons.mpr (Or.inr ht)⟩

/-- A nontrivial component of unprotected degree-two vertices is the interior
of one physical corridor. Its two boundary edges attach at the endpoints of
the spanning path. The two retained endpoints may coincide. -/
theorem exists_physical_corridor_for_nontrivial_component
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent)
    (hcard : 1 < ((c.supp.toFinset).map
      (Function.Embedding.subtype {v | v ∉ P})).card) :
    ∃ (a b u w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
      (hleft : G.toSimpleGraph.Adj u a) (hright : G.toSimpleGraph.Adj b w)
      (Ccorr : PhysicalCorridor G),
      p.IsPath ∧
      p.support.toFinset = (c.supp.toFinset).map
        (Function.Embedding.subtype {v | v ∉ P}) ∧
      u ∉ (c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P}) ∧
      u ∈ P ∧
      w ∉ (c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P}) ∧
      w ∈ P ∧
      Ccorr.vertices = u :: p.support ++ [w] ∧
      Ccorr.edges = physicalEdgeOfAdj G hleft ::
        (liftedEdges G p ++ [physicalEdgeOfAdj G hright]) := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let C : Finset G.Vertex := c.supp.toFinset.map (Function.Embedding.subtype U)
  have hCcard : 1 < C.card := by simpa [C, U] using hcard
  have hdegreeC : ∀ v ∈ C,
      (G.toSimpleGraph.neighborFinset v).card = 2 := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
    change (G.toSimpleGraph.neighborFinset z.1).card = 2
    rw [← PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G z.1]
    exact hdegree z.1 z.2
  have hinternal : ∀ v ∈ C,
      0 < (G.toSimpleGraph.neighborFinset v ∩ C).card := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
    have hScard : 1 < c.supp.toFinset.card := by simpa [C] using hCcard
    obtain ⟨z₂, hz₂, hne⟩ := Finset.exists_mem_ne hScard z
    let v₁ : c.supp := ⟨z, Set.mem_toFinset.mp hz⟩
    let v₂ : c.supp := ⟨z₂, Set.mem_toFinset.mp hz₂⟩
    have hv₁v₂ : v₁ ≠ v₂ := by
      intro heq
      exact hne (congrArg Subtype.val heq).symm
    let H : SimpleGraph U := G.toSimpleGraph.induce U
    let K : SimpleGraph c.supp := H.induce c.supp
    have hproper : ({v₁} : Set c.supp) ≠ Set.univ := by
      intro heq
      have hv₂ : v₂ ∈ ({v₁} : Set c.supp) := by
        simpa [heq] using (Set.mem_univ v₂)
      have hv₂' : v₂ = v₁ := by simpa using hv₂
      exact hv₁v₂ hv₂'.symm
    obtain ⟨s, t, hs, ht, hadj⟩ :=
      ConnectedRegionBoundary.Connected.exists_adj_boundary
        c.connected_induce_supp ⟨v₁, by simp⟩ hproper
    have hs' : s = v₁ := by simpa using hs
    have hAdj : G.toSimpleGraph.Adj v₁.1.1 t.1.1 := by
      change G.toSimpleGraph.Adj s.1.1 t.1.1 at hadj
      simpa [hs'] using hadj
    have htC : t.1.1 ∈ C := by
      exact Finset.mem_map.mpr
        ⟨t.1, Set.mem_toFinset.mpr t.2, rfl⟩
    refine Finset.card_pos.mpr ⟨t.1.1, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨(SimpleGraph.mem_neighborFinset G.toSimpleGraph v₁.1.1 t.1.1).2 hAdj,
        htC⟩
  have hboundary :=
    ComponentBoundaryCount.component_boundaryCount_eq_two
      G P hconn hP hdegree c
  obtain ⟨x, y, hxC, hyC, hxy, hxout, hyout⟩ :=
    TreeBoundaryAttachments.exists_distinct_boundary_vertices_of_two_incidences
      G.toSimpleGraph C hdegreeC hinternal (by simpa [C, U] using hboundary)
  obtain ⟨u, hu⟩ := hxout
  obtain ⟨w, hw⟩ := hyout
  have hu' := Finset.mem_sdiff.mp hu
  have hw' := Finset.mem_sdiff.mp hw
  have hxu : G.toSimpleGraph.Adj x u :=
    (SimpleGraph.mem_neighborFinset G.toSimpleGraph x u).1 hu'.1
  have hyw : G.toSimpleGraph.Adj y w :=
    (SimpleGraph.mem_neighborFinset G.toSimpleGraph y w).1 hw'.1
  have huP : u ∈ P := by
    by_contra hup
    let H : SimpleGraph U := G.toSimpleGraph.induce U
    let uu : U := ⟨u, hup⟩
    obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp hxC
    have hxz : z.1 = x := by exact heq
    let adj : H.Adj z uu := by
      change G.toSimpleGraph.Adj z.1 u
      simpa [hxz] using hxu
    have huComp : uu ∈ c.supp :=
      (c.mem_supp_congr_adj adj).mp (Set.mem_toFinset.mp hz)
    have huC : u ∈ C := by
      exact Finset.mem_map.mpr ⟨uu, Set.mem_toFinset.mpr huComp, rfl⟩
    exact hu'.2 huC
  have hwP : w ∈ P := by
    by_contra hwp
    let H : SimpleGraph U := G.toSimpleGraph.induce U
    let ww : U := ⟨w, hwp⟩
    obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp hyC
    have hyz : z.1 = y := by exact heq
    let adj : H.Adj z ww := by
      change G.toSimpleGraph.Adj z.1 w
      simpa [hyz] using hyw
    have hwComp : ww ∈ c.supp :=
      (c.mem_supp_congr_adj adj).mp (Set.mem_toFinset.mp hz)
    have hwC : w ∈ C := by
      exact Finset.mem_map.mpr ⟨ww, Set.mem_toFinset.mpr hwComp, rfl⟩
    exact hw'.2 hwC
  have hPth := ComponentBoundaryEndpoints.component_ambient_spanning_path
    G P hconn hP hdegree c
  obtain ⟨a₀, b₀, p₀, hp₀, hsubset₀, hcover₀⟩ := hPth
  have hsubset : ∀ v, v ∈ p₀.support → v ∈ C := by
    simpa [C, U] using hsubset₀
  have hcover : ∀ v, v ∈ C → v ∈ p₀.support := by
    simpa [C, U] using hcover₀
  have hxend := ComponentBoundaryEndpoints.boundary_vertex_is_endpoint
    G C p₀ hp₀ hcover hsubset
    hdegreeC hxC hxu (by simpa [C, U] using hu'.2)
  have hyend := ComponentBoundaryEndpoints.boundary_vertex_is_endpoint
    G C p₀ hp₀ hcover hsubset
    hdegreeC hyC hyw (by simpa [C, U] using hw'.2)
  have hOrient : (x = a₀ ∧ y = b₀) ∨ (x = b₀ ∧ y = a₀) := by
    rcases hxend with hxa | hxb
    · rcases hyend with hya | hyb
      · exact (hxy (hxa.trans hya.symm)).elim
      · exact Or.inl ⟨hxa, hyb⟩
    · rcases hyend with hya | hyb
      · exact Or.inr ⟨hxb, hya⟩
      · exact (hxy (hxb.trans hyb.symm)).elim
  have hsupport₀ : p₀.support.toFinset = C := by
    ext v
    simp only [List.mem_toFinset]
    exact ⟨hsubset v, hcover v⟩
  have hPathChoice : ∃ q : G.toSimpleGraph.Walk x y,
      q.IsPath ∧ q.support.toFinset = C := by
    rcases hOrient with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · subst x
      subst y
      exact ⟨p₀, hp₀, hsupport₀⟩
    · subst x
      subst y
      refine ⟨p₀.reverse, hp₀.reverse, ?_⟩
      simpa using hsupport₀
  let p : G.toSimpleGraph.Walk x y := Classical.choose hPathChoice
  have hp : p.IsPath := (Classical.choose_spec hPathChoice).1
  have hpsupport : p.support.toFinset = C :=
    (Classical.choose_spec hPathChoice).2
  let hleft : G.toSimpleGraph.Adj u x := hxu.symm
  let hright : G.toSimpleGraph.Adj y w := hyw
  let eleft := physicalEdgeOfAdj G hleft
  let eright := physicalEdgeOfAdj G hright
  have hleft_not : eleft ∉ liftedEdges G p := by
    intro he
    obtain ⟨hs, ht⟩ := lifted_edge_endpoints_mem_support G p he
    have hsC : G.src eleft ∈ C := by
      exact hpsupport ▸ (List.mem_toFinset.mpr hs)
    have htC : G.dst eleft ∈ C := by
      exact hpsupport ▸ (List.mem_toFinset.mpr ht)
    rcases physicalEdgeOfAdj_spec G hleft with hspec | hspec
    · exact hu'.2 (by simpa [eleft, hspec.1] using hsC)
    · exact hu'.2 (by simpa [eleft, hspec.2] using htC)
  have hright_not : eright ∉ liftedEdges G p := by
    intro he
    obtain ⟨hs, ht⟩ := lifted_edge_endpoints_mem_support G p he
    have hsC : G.src eright ∈ C := by
      exact hpsupport ▸ (List.mem_toFinset.mpr hs)
    have htC : G.dst eright ∈ C := by
      exact hpsupport ▸ (List.mem_toFinset.mpr ht)
    rcases physicalEdgeOfAdj_spec G hright with hspec | hspec
    · exact hw'.2 (by simpa [eright, hspec.2] using htC)
    · exact hw'.2 (by simpa [eright, hspec.1] using hsC)
  have hattach_ne : eleft ≠ eright := by
    intro heq
    have hsrc := congrArg G.src heq
    have hdst := congrArg G.dst heq
    rcases physicalEdgeOfAdj_spec G hleft with hL | hL <;>
      rcases physicalEdgeOfAdj_spec G hright with hR | hR
    · have : u = y := by simpa [eleft, eright, hL.1, hR.1] using hsrc
      exact hu'.2 (by simpa [this] using hyC)
    · have : x = y := by simpa [eleft, eright, hL.2, hR.2] using hdst
      exact hxy this
    · have : x = y := by simpa [eleft, eright, hL.1, hR.1] using hsrc
      exact hxy this
    · have : x = w := by simpa [eleft, eright, hL.1, hR.1] using hsrc
      exact hw'.2 (by simpa [this] using hxC)
  obtain ⟨Ccorr, hedge, hverts, _, _, _⟩ :=
    AttachedPathConstruction.corridor_from_path_and_two_attachments
      G p hp hleft hright hleft_not hright_not hattach_ne
  refine ⟨x, y, u, w, p, hleft, hright, Ccorr, hp,
    ?_, ?_, huP, ?_, hwP, hverts, hedge⟩
  · simpa [hpsupport, C, U]
  · simpa [C, U] using hu'.2
  · simpa [C, U] using hw'.2

/-- A singleton unprotected degree-two component also has a two-edge physical
corridor. Its endpoints are distinct protected vertices: a simple physical
graph cannot have two different edges from the singleton vertex to the same
endpoint. -/
theorem exists_physical_corridor_for_singleton_component
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent)
    (hcard : ((c.supp.toFinset).map
      (Function.Embedding.subtype {v | v ∉ P})).card = 1) :
    ∃ (x u w : G.Vertex) (hleft : G.toSimpleGraph.Adj u x)
      (hright : G.toSimpleGraph.Adj x w) (Ccorr : PhysicalCorridor G),
      (c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P}) = {x} ∧
      u ∈ P ∧ w ∈ P ∧ u ≠ w ∧
      Ccorr.vertices = [u, x, w] ∧
      Ccorr.edges = [physicalEdgeOfAdj G hleft, physicalEdgeOfAdj G hright] := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let C : Finset G.Vertex := c.supp.toFinset.map (Function.Embedding.subtype U)
  have hCcard : C.card = 1 := by simpa [C, U] using hcard
  obtain ⟨x, hCeq⟩ := Finset.card_eq_one.mp hCcard
  have hxC : x ∈ C := by rw [hCeq]; simp
  have hxP : x ∉ P := by
    obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp hxC
    have hxz : z.1 = x := by exact heq
    rw [← hxz]
    exact z.2
  have hboundary :=
    ComponentBoundaryCount.component_boundaryCount_eq_two
      G P hconn hP hdegree c
  have hboundaryC :
      DegreeTwoComponentCut.boundaryCount G.toSimpleGraph C = 2 := by
    simpa [C, U] using hboundary
  have hboundarySingleton :
      DegreeTwoComponentCut.boundaryCount G.toSimpleGraph {x} = 2 := by
    rw [← hCeq]
    exact hboundaryC
  have houter : (G.toSimpleGraph.neighborFinset x \ {x}).card = 2 := by
    simpa [DegreeTwoComponentCut.boundaryCount] using hboundarySingleton
  obtain ⟨u, w, huw, hEq⟩ := Finset.card_eq_two.mp houter
  have huOut : u ∈ G.toSimpleGraph.neighborFinset x \ {x} := by
    rw [hEq]
    simp [huw]
  have hwOut : w ∈ G.toSimpleGraph.neighborFinset x \ {x} := by
    rw [hEq]
    simp [huw]
  have hux : G.toSimpleGraph.Adj x u :=
    (SimpleGraph.mem_neighborFinset G.toSimpleGraph x u).1 (Finset.mem_sdiff.mp huOut).1
  have hxw : G.toSimpleGraph.Adj x w :=
    (SimpleGraph.mem_neighborFinset G.toSimpleGraph x w).1 (Finset.mem_sdiff.mp hwOut).1
  have hxu : G.toSimpleGraph.Adj u x := hux.symm
  have hu_ne_x : u ≠ x := by
    intro heq
    exact (Finset.mem_sdiff.mp huOut).2 (by simp [heq])
  have hw_ne_x : w ≠ x := by
    intro heq
    exact (Finset.mem_sdiff.mp hwOut).2 (by simp [heq])
  have huP : u ∈ P := by
    by_cases hup : u ∈ P
    · exact hup
    · exfalso
      let z : U := ⟨x, hxP⟩
      let v : U := ⟨u, hup⟩
      have hzC : z ∈ c.supp := by
        obtain ⟨z', hz', heq⟩ := Finset.mem_map.mp hxC
        have hz'eq : z' = z := Subtype.ext heq
        simpa [hz'eq] using (Set.mem_toFinset.mp hz')
      let H : SimpleGraph U := G.toSimpleGraph.induce U
      have hadj : H.Adj z v := by
        change G.toSimpleGraph.Adj x u
        exact hux
      have hvC : v ∈ c.supp := (c.mem_supp_congr_adj hadj).mp hzC
      have huC : u ∈ C := by
        exact Finset.mem_map.mpr ⟨v, Set.mem_toFinset.mpr hvC, rfl⟩
      have huxeq : u = x := by simpa [hCeq] using huC
      exact hu_ne_x huxeq
  have hwP : w ∈ P := by
    by_cases hwp : w ∈ P
    · exact hwp
    · exfalso
      let z : U := ⟨x, hxP⟩
      let v : U := ⟨w, hwp⟩
      have hzC : z ∈ c.supp := by
        obtain ⟨z', hz', heq⟩ := Finset.mem_map.mp hxC
        have hz'eq : z' = z := Subtype.ext heq
        simpa [hz'eq] using (Set.mem_toFinset.mp hz')
      let H : SimpleGraph U := G.toSimpleGraph.induce U
      have hadj : H.Adj z v := by
        change G.toSimpleGraph.Adj x w
        exact hxw
      have hvC : v ∈ c.supp := (c.mem_supp_congr_adj hadj).mp hzC
      have hwC : w ∈ C := by
        exact Finset.mem_map.mpr ⟨v, Set.mem_toFinset.mpr hvC, rfl⟩
      have hwxeq : w = x := by simpa [hCeq] using hwC
      exact hw_ne_x hwxeq
  have hleft_ne_right :
      physicalEdgeOfAdj G hxu ≠ physicalEdgeOfAdj G hxw := by
    intro heq
    have hsrc := congrArg G.src heq
    have hdst := congrArg G.dst heq
    rcases physicalEdgeOfAdj_spec G hxu with hL | hL <;>
      rcases physicalEdgeOfAdj_spec G hxw with hR | hR
    · have : u = x := by simpa [hL.1, hR.1] using hsrc
      exact hu_ne_x this
    · have : u = w := by simpa [hL.1, hR.1] using hsrc
      exact huw this
    · have : u = w := by simpa [hL.2, hR.2] using hdst
      exact huw this
    · have : u = x := by simpa [hL.2, hR.2] using hdst
      exact hu_ne_x this
  obtain ⟨Ccorr, hEdges, hVerts, _, _, _⟩ :=
    AttachedPathConstruction.corridor_from_path_and_two_attachments
      G (Walk.nil : G.toSimpleGraph.Walk x x) (by simp) hxu hxw
      (by simp [liftedEdges]) (by simp [liftedEdges]) hleft_ne_right
  refine ⟨x, u, w, hxu, hxw, Ccorr, ?_, huP, hwP, huw, ?_, ?_⟩
  · simpa [C, U] using hCeq
  · simpa using hVerts
  · simpa [liftedEdges] using hEdges


/-- Every connected component of the unprotected induced graph is the interior
of a physical corridor joining two protected vertices. For a singleton
component the path is `Walk.nil`; its two protected endpoints are necessarily
distinct. For larger components they may coincide. -/
theorem exists_physical_corridor_for_component
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent) :
    ∃ (a b u w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
      (hleft : G.toSimpleGraph.Adj u a) (hright : G.toSimpleGraph.Adj b w)
      (Ccorr : PhysicalCorridor G),
      p.IsPath ∧
      p.support.toFinset = (c.supp.toFinset).map
        (Function.Embedding.subtype {v | v ∉ P}) ∧
      u ∉ (c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P}) ∧
      u ∈ P ∧
      w ∉ (c.supp.toFinset).map (Function.Embedding.subtype {v | v ∉ P}) ∧
      w ∈ P ∧
      Ccorr.vertices = u :: p.support ++ [w] ∧
      Ccorr.edges = physicalEdgeOfAdj G hleft ::
        (liftedEdges G p ++ [physicalEdgeOfAdj G hright]) := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let C : Finset G.Vertex := c.supp.toFinset.map
    (Function.Embedding.subtype U)
  have hCne : C.Nonempty := by
    obtain ⟨z, hz⟩ := c.nonempty_supp
    exact ⟨z.1, Finset.mem_map.mpr ⟨z, Set.mem_toFinset.mpr hz, rfl⟩⟩
  have hCsubset : ∀ v ∈ C, v ∉ P := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
    exact z.2
  by_cases hsingleton : C.card = 1
  · obtain ⟨x, u, w, hleft, hright, Ccorr, hset, huP, hwP,
      huw, hverts, hedges⟩ :=
        exists_physical_corridor_for_singleton_component
          G P hconn hP hdegree c (by simpa [C, U] using hsingleton)
    let p : G.toSimpleGraph.Walk x x := Walk.nil
    have hp : p.IsPath := by simp [p]
    have hsupport : p.support.toFinset = C := by
      simpa [p, C, U] using hset.symm
    have huC : u ∉ C := fun hu => (hCsubset u hu) huP
    have hwC : w ∉ C := fun hw => (hCsubset w hw) hwP
    refine ⟨x, x, u, w, p, hleft, hright, Ccorr, hp, hsupport,
      huC, huP, hwC, hwP, ?_, ?_⟩
    · simpa [p] using hverts
    · simpa [p, liftedEdges] using hedges
  · have hlarge : 1 < C.card := by
      have : 0 < C.card := Finset.card_pos.mpr hCne
      omega
    obtain ⟨a, b, u, w, p, hleft, hright, Ccorr, hp, hsupport,
      huC, huP, hwC, hwP, hverts, hedges⟩ :=
        exists_physical_corridor_for_nontrivial_component
          G P hconn hP hdegree c (by simpa [C, U] using hlarge)
    exact ⟨a, b, u, w, p, hleft, hright, Ccorr, hp, hsupport,
      huC, huP, hwC, hwP, hverts, hedges⟩

end Erdos1016.Proof.ComponentCorridorConstruction

end

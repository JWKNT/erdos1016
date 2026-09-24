import Erdos1016.Cleanup.CleanupSpecification
import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Graph.PathExpansion.RouteConstancy
import Erdos1016.CycleSpace.EvenForestZero

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ReducedForestEventTransfer

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.PhysicalGraph
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PhysicalPartition

variable {Γ : FiniteMultiGraph}

private def walkAuxEdges : ∀ {u v : Γ.Vertex},
    Γ.toSimpleGraph.Walk u v → List Γ.Edge
  | _, _, .nil => []
  | _, _, .cons h p => Γ.edgeForAdj h :: walkAuxEdges p

private theorem walkAuxEdges_cons {u v w : Γ.Vertex}
    (h : Γ.toSimpleGraph.Adj u v) (p : Γ.toSimpleGraph.Walk v w) :
    walkAuxEdges (.cons h p) = Γ.edgeForAdj h :: walkAuxEdges p := rfl

private theorem walkWord_eq_zero_of_not_mem_auxEdges
    {u v : Γ.Vertex} (p : Γ.toSimpleGraph.Walk u v) {e : Γ.Edge}
    (he : e ∉ walkAuxEdges p) : Γ.walkWord p e = 0 := by
  induction p with
  | nil => simp [walkAuxEdges, FiniteMultiGraph.walkWord]
  | @cons a b c h p ih =>
      simp only [walkAuxEdges_cons, List.mem_cons, not_or] at he
      simp only [FiniteMultiGraph.walkWord, Pi.add_apply, Pi.single_apply]
      simp [he.1, ih he.2]



private theorem pair_mem_edges_of_auxEdge_mem
    {u v : Γ.Vertex} (p : Γ.toSimpleGraph.Walk u v) {e : Γ.Edge}
    (he : e ∈ walkAuxEdges p) : s(Γ.src e, Γ.dst e) ∈ p.edges := by
  induction p with
  | nil => simp [walkAuxEdges] at he
  | @cons a b c h p ih =>
      rw [walkAuxEdges_cons] at he
      simp only [List.mem_cons] at he
      rcases he with he | he
      · have hp := Γ.edgeForAdj_endpoints h
        rw [SimpleGraph.Walk.edges_cons]
        rcases hp with hp | hp
        · have hpair : s(Γ.src e, Γ.dst e) = s(a, b) := by
            rw [he]
            exact Sym2.eq_iff.2 (Or.inl ⟨hp.1, hp.2⟩)
          exact List.mem_cons.mpr (Or.inl hpair)
        · have hpair : s(Γ.src e, Γ.dst e) = s(a, b) := by
            rw [he]
            exact Sym2.eq_iff.2 (Or.inr ⟨hp.1, hp.2⟩)
          exact List.mem_cons.mpr (Or.inl hpair)
      · have hpair := ih he
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons.mpr (Or.inr hpair)

private theorem head_auxEdge_not_mem_tail
    {u v : Γ.Vertex} (h : Γ.toSimpleGraph.Adj u v)
    (p : Γ.toSimpleGraph.Walk v u)
    (hp : (SimpleGraph.Walk.cons h p).IsCycle) :
    Γ.edgeForAdj h ∉ walkAuxEdges p := by
  have hedges := hp.isCircuit.isTrail.edges_nodup
  intro hm
  have hpair := pair_mem_edges_of_auxEdge_mem p hm
  have heq : s(u, v) = s(Γ.src (Γ.edgeForAdj h), Γ.dst (Γ.edgeForAdj h)) := by
    rcases Γ.edgeForAdj_endpoints h with hh | hh
    · exact (Sym2.eq_iff.2 (Or.inl ⟨hh.1, hh.2⟩)).symm
    · exact (Sym2.eq_iff.2 (Or.inr ⟨hh.1, hh.2⟩)).symm
  rw [← heq] at hpair
  have hnot := (List.nodup_cons.mp hedges).1
  exact hnot hpair

private theorem walkWord_ne_zero_at_head
    {u v : Γ.Vertex} (h : Γ.toSimpleGraph.Adj u v)
    (p : Γ.toSimpleGraph.Walk v u) (hp : (SimpleGraph.Walk.cons h p).IsCycle) :
    Γ.walkWord (SimpleGraph.Walk.cons h p) (Γ.edgeForAdj h) ≠ 0 := by
  have hnot := head_auxEdge_not_mem_tail h p hp
  rw [FiniteMultiGraph.walkWord]
  simp only [Pi.add_apply, Pi.single_apply, if_pos rfl]
  rw [walkWord_eq_zero_of_not_mem_auxEdges p hnot]
  exact one_ne_zero

private theorem walkWord_ne_zero_of_isCycle
    {u : Γ.Vertex} (p : Γ.toSimpleGraph.Walk u u) (hp : p.IsCycle) :
    Γ.walkWord p ≠ 0 := by
  cases p with
  | nil => exact fun _ => hp.isCircuit.ne_nil rfl
  | @cons a b c h tail =>
      change (SimpleGraph.Walk.cons h tail).IsCycle at hp
      intro hz
      have hhead := walkWord_ne_zero_at_head h tail hp
      have hz' : Γ.walkWord (SimpleGraph.Walk.cons h tail) = 0 := hz
      have := congrFun hz' (Γ.edgeForAdj h)
      exact hhead this

private def selectedToUnderlying (Γ : FiniteMultiGraph) (w : Γ.EdgeWord) :
    selectedGraph Γ w →g Γ.toSimpleGraph := {
  toFun := id
  map_rel' := by
    intro a b hab
    rcases hab with ⟨hne, e, he, hend⟩
    exact ⟨hne, e, hend⟩
}

private theorem edgeForAdj_mem_internal_of_selectedAdj
    (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex) (w : Γ.EdgeWord)
    (hroot : IsCleanupRoot Γ H)
    {u v : Γ.Vertex}
    (hselected : (selectedGraph Γ w).Adj u v)
    (hbase : Γ.toSimpleGraph.Adj u v)
    (hsupport : ∀ e, w e ≠ 0 → e ∈ internalEdges Γ H) :
    w (Γ.edgeForAdj hbase) ≠ 0 ∧
      Γ.edgeForAdj hbase ∈ internalEdges Γ H := by
  classical
  rcases hselected with ⟨hne, e, he, hend⟩
  have heInternal := hsupport e he
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at heInternal
  have huRoot : u ∈ H := by
    rcases hend with hh | hh
    · exact hh.1 ▸ heInternal.1
    · exact hh.2 ▸ heInternal.2
  have hvRoot : v ∈ H := by
    rcases hend with hh | hh
    · exact hh.2 ▸ heInternal.2
    · exact hh.1 ▸ heInternal.1
  let f := Γ.edgeForAdj hbase
  have hfend := Γ.edgeForAdj_endpoints hbase
  have hsrcRoot : Γ.src f ∈ H := by
    rcases hfend with h | h
    · rw [h.1]
      exact huRoot
    · rw [h.1]
      exact hvRoot
  have hdstRoot : Γ.dst f ∈ H := by
    rcases hfend with h | h
    · rw [h.2]
      exact hvRoot
    · rw [h.2]
      exact huRoot
  have hlabel : e = f := by
    apply hroot.2.2 e f heInternal.1 heInternal.2 hsrcRoot hdstRoot
    rcases hend with he' | he' <;> rcases hfend with hf' | hf'
    · exact Or.inl ⟨he'.1.trans hf'.1.symm, he'.2.trans hf'.2.symm⟩
    · exact Or.inr ⟨he'.1.trans hf'.2.symm, he'.2.trans hf'.1.symm⟩
    · exact Or.inr ⟨he'.1.trans hf'.2.symm, he'.2.trans hf'.1.symm⟩
    · exact Or.inl ⟨he'.1.trans hf'.1.symm, he'.2.trans hf'.2.symm⟩
  have hfsel : w f ≠ 0 := by simpa [hlabel] using he
  refine ⟨hfsel, ?_⟩
  simpa [f, hbase, internalEdges] using ⟨hsrcRoot, hdstRoot⟩

private theorem walkAuxEdges_internal
    (Γ : FiniteMultiGraph) (w : Γ.EdgeWord) (H : Finset Γ.Vertex)
    (hroot : IsCleanupRoot Γ H)
    (hsupport : ∀ e, w e ≠ 0 → e ∈ internalEdges Γ H)
    :
    ∀ {u v : Γ.Vertex} (p : (selectedGraph Γ w).Walk u v)
      e, e ∈ walkAuxEdges (p.map (selectedToUnderlying Γ w)) →
        e ∈ internalEdges Γ H ∧ w e ≠ 0 := by
  intro u v p
  induction p with
  | nil => simp [walkAuxEdges]
  | @cons a b c h p ih =>
      intro e he
      simp only [SimpleGraph.Walk.map_cons, walkAuxEdges_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        have hbase := (selectedToUnderlying Γ w).map_rel h
        have hmem := edgeForAdj_mem_internal_of_selectedAdj Γ H w hroot h hbase hsupport
        exact ⟨hmem.2, hmem.1⟩
      · exact ih e he

/-- A simple-graph cycle in a selected word, when all selected edges are
internal to a simple root, gives a nonzero cycle-space word on those edges.
The root simplicity certificate ensures the arbitrary edge labels chosen by
`walkWord` are exactly the selected internal labels. -/
theorem exists_nonzero_cycleSpace_supported_on_internal_of_selectedGraph_cycle
    (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex)
    (hroot : IsCleanupRoot Γ H) (w : Γ.EdgeWord)
    {v : Γ.Vertex}
    (p : (selectedGraph Γ w).Walk v v)
    (hp : p.IsCycle)
    (hsupport : ∀ e, w e ≠ 0 → e ∈ internalEdges Γ H) :
    ∃ z : Γ.CycleSpace, z ≠ 0 ∧
      ∀ e, z.1 e ≠ 0 → e ∈ internalEdges Γ H ∧ w e ≠ 0 := by
  classical
  have hsimple := hroot
  let f := selectedToUnderlying Γ w
  let q := p.map f
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective (fun _ _ h => h)).2 hp
  let z : Γ.CycleSpace := ⟨Γ.walkWord q, by
    change Γ.boundary (Γ.walkWord q) = 0
    rw [Γ.boundary_walkWord]
    simp [q]
  ⟩
  have hne : z ≠ 0 := by
    intro hz
    have hzero : Γ.walkWord q = 0 := congrArg Subtype.val hz
    exact walkWord_ne_zero_of_isCycle q hq hzero
  have hword_support : ∀ e, z.1 e ≠ 0 →
      e ∈ internalEdges Γ H ∧ w e ≠ 0 := by
    intro e he
    have hm : e ∈ walkAuxEdges q := by
      by_contra hnot
      have hz := @walkWord_eq_zero_of_not_mem_auxEdges Γ _ _ q e hnot
      exact he hz
    have hinter := walkAuxEdges_internal Γ w H hroot hsupport p e hm
    exact hinter
  exact ⟨z, hne, hword_support⟩


variable {G : PhysicalGraph} {I : CleanupInput G}

/-- Route-graph view of the physical graph, forgetting simplicity metadata. -/
def reducedRouteGraph (G : PhysicalGraph) : FiniteMultiGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  src := G.src
  dst := G.dst

/-- Reduced data for transporting the cleanup event.  In particular this
record does not contain a `CleanupOutput` or an event-transport conclusion.
The endpoint-edge field is the minimal endpoint datum needed for the degree
comparison; it can be filled from recorded corridor endpoints. -/
structure ReducedEventTransportCertificate (G : PhysicalGraph) (I : CleanupInput G) where
  Γ : FiniteMultiGraph
  root : Finset Γ.Vertex
  testEdges : Finset Γ.Edge
  marginal : G.CycleSpace →ₗ[F₂] Γ.CycleSpace
  liftCycles : Γ.CycleSpace →ₗ[F₂] G.CycleSpace
  vertexMap : Γ.Vertex → G.Vertex
  edgePath : Γ.Edge → PhysicalCorridor G
  edgeRepresentative : Γ.Edge → G.Edge
  edgeRepresentative_mem : ∀ e, edgeRepresentative e ∈ (edgePath e).support
  marginal_reads_representatives : ∀ x e,
    (marginal x).1 e = x.1 (edgeRepresentative e)
  routeSystem : EdgeDisjointRouteSystem Γ (reducedRouteGraph G)
  /-- Active degree-two corridors force constancy for cycle words. Requiring
  full ambient degree two would incorrectly exclude inactive bridge edges. -/
  path_cycle_constant : ∀ x : G.CycleSpace, ∀ e p q,
    p ∈ routeSystem.support e → q ∈ routeSystem.support e → x.1 p = x.1 q
  route_support_eq_path : ∀ e, routeSystem.support e = (edgePath e).support
  lift_is_path_expansion : ∀ x : Γ.CycleSpace, ∀ p : G.Edge,
    (liftCycles x).1 p =
      if ∃ e, x.1 e ≠ 0 ∧ p ∈ (edgePath e).support then 1 else 0
  marginal_lift : ∀ x, marginal (liftCycles x) = x
  testEdges_internal : testEdges = internalEdges Γ root
  tested_paths_in_complement : ∀ e ∈ testEdges,
    ∀ p ∈ (edgePath e).support, p ∉ I.witnessEdges
  endpoint_edges : ∀ e, ∃ p q : G.Edge,
    p ∈ (edgePath e).support ∧ q ∈ (edgePath e).support ∧
    G.incident p (vertexMap (Γ.src e)) ∧ G.incident q (vertexMap (Γ.dst e))
  root_structure : IsCleanupRoot Γ root
  root_cubic_ambient_degree : ∀ v ∈ root, ambientDegree Γ v = 3

namespace ReducedEventTransportCertificate

variable (C : ReducedEventTransportCertificate G I)

theorem edgePaths_disjoint (e f : C.Γ.Edge) (hne : e ≠ f) :
    Disjoint (C.edgePath e).support (C.edgePath f).support := by
  rw [← C.route_support_eq_path e, ← C.route_support_eq_path f]
  exact C.routeSystem.disjoint hne

/-- A cycle word is constant along the recorded support of each route. -/
theorem marginal_agrees_on_path (x : G.CycleSpace) (e : C.Γ.Edge)
    (p : G.Edge) (hp : p ∈ (C.edgePath e).support) :
    (C.marginal x).1 e = x.1 p := by
  rw [C.marginal_reads_representatives]
  exact C.path_cycle_constant x e (C.edgeRepresentative e) p
    (by rw [C.route_support_eq_path]; exact C.edgeRepresentative_mem e)
    (by rw [C.route_support_eq_path]; exact hp)

/-- The expansion of a tested auxiliary cycle supported by the marginal is
inside the witness complement. -/
theorem lift_support_subset (x : G.CycleSpace) (z : C.Γ.CycleSpace)
    (hsupported : ∀ e, e ∉ C.testEdges → z.1 e = 0)
    (hselected : ∀ e, z.1 e ≠ 0 → (C.marginal x).1 e ≠ 0) :
    ∀ p, (C.liftCycles z).1 p ≠ 0 → x.1 p ≠ 0 ∧ p ∉ I.witnessEdges := by
  intro p hp
  have hex : ∃ e, z.1 e ≠ 0 ∧ p ∈ (C.edgePath e).support := by
    by_contra h
    have hz := C.lift_is_path_expansion z p
    simp [h] at hz
    exact hp hz
  obtain ⟨e, he, hpPath⟩ := hex
  have heTest : e ∈ C.testEdges := by
    by_contra hnot
    exact he (hsupported e hnot)
  have hpMarginal : (C.marginal x).1 e ≠ 0 := hselected e he
  have hpOriginal : x.1 p ≠ 0 := by
    rw [← C.marginal_agrees_on_path x e p hpPath]
    exact hpMarginal
  exact ⟨hpOriginal,
    C.tested_paths_in_complement e heTest p hpPath⟩

end ReducedEventTransportCertificate


namespace ReducedEventTransportCertificate

variable (C : ReducedEventTransportCertificate G I)

/-- A nonzero tested lift supported under the selected marginal cannot lie in
a good witness-complement linear forest. -/
theorem no_selected_test_cycle_over_good_outside_forest
    (x : G.CycleSpace) (z : C.Γ.CycleSpace)
    (hgood : originalCleanupGood G I x) (hz : z ≠ 0)
    (hsupported : ∀ e, e ∉ C.testEdges → z.1 e = 0)
    (hselected : ∀ e, z.1 e ≠ 0 → (C.marginal x).1 e ≠ 0) : False := by
  let E : Finset G.Edge := I.witnessEdgesᶜ
  let y : G.Word := (C.liftCycles z).1
  have hboundary : G.boundary y = 0 := by
    change G.boundary (C.liftCycles z).1 = 0
    exact (C.liftCycles z).2
  have hvanish : ∀ p, p ∉ E → y p = 0 := by
    intro p hp
    have hpW : p ∈ I.witnessEdges := by simpa [E] using hp
    by_cases hne : y p = 0
    · exact hne
    · exact False.elim ((C.lift_support_subset x z hsupported hselected p hne).2 hpW)
  have hrestore : G.extendWord E (G.restrictWord E y) = y :=
    G.extend_restrict_of_outside_zero E y hvanish
  have hboundary' : G.restrictedBoundary E (G.restrictWord E y) = 0 := by
    change G.boundary (G.extendWord E (G.restrictWord E y)) = 0
    rw [hrestore]
    exact hboundary
  have hforest :
      (G.restrictedSelectedGraph E (G.restrictWord E y)).IsAcyclic := by
    have hsub :
        G.restrictedSelectedGraph E (G.restrictWord E y) ≤
          G.restrictedSelectedGraph E (G.restrictWord E x.1) := by
      intro u v huv
      rcases huv with ⟨e, he, hend⟩
      have hy : y e.1 ≠ 0 := by simpa [restrictWord] using he
      have hx := (C.lift_support_subset x z hsupported hselected e.1 hy).1
      refine ⟨e, ?_, hend⟩
      simpa [restrictWord] using hx
    intro a p hp
    let inc : (G.restrictedSelectedGraph E (G.restrictWord E y)) →g
        (G.restrictedSelectedGraph E (G.restrictWord E x.1)) :=
      { toFun := id, map_rel' := by intro v w hvw; exact hsub hvw }
    have hinj : Function.Injective inc := by intro v w hvw; exact hvw
    have hmap : (p.map inc).IsCycle :=
      (SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).2 hp
    exact hgood.1 (p.map inc) hmap
  have hzero := Erdos1016.Proof.CycleSpaceForestZero.restrictedWord_eq_zero_of_boundary_zero_of_acyclic
    G E (G.restrictWord E y) hboundary' hforest
  have hyzero : y = 0 := by
    funext p
    by_cases hpW : p ∈ I.witnessEdges
    · exact hvanish p (by simpa [E] using hpW)
    · have hpE : p ∈ E := by simpa [E] using hpW
      have hz' := congrFun hzero ⟨p, hpE⟩
      simpa [restrictWord] using hz'
  have hspacezero : C.liftCycles z = 0 := by apply Subtype.ext; exact hyzero
  have hz0 : z = 0 := by rw [← C.marginal_lift z, hspacezero]; simp
  exact hz hz0

/-- A good original outside forest rules out cycles in the selected internal
auxiliary root restriction. -/
theorem selected_root_restriction_acyclic_of_original_good
    (C : ReducedEventTransportCertificate G I)
    (x : G.CycleSpace) (hgood : originalCleanupGood G I x) :
    (selectedGraph C.Γ
      (fun e => if e ∈ internalEdges C.Γ C.root then (C.marginal x).1 e else 0)).IsAcyclic := by
  classical
  let w : C.Γ.EdgeWord := fun e =>
    if e ∈ internalEdges C.Γ C.root then (C.marginal x).1 e else 0
  change (selectedGraph C.Γ w).IsAcyclic
  have hsupport : ∀ e, w e ≠ 0 → e ∈ internalEdges C.Γ C.root := by
    intro e he
    by_contra hnot
    have hz : w e = 0 := by simp [w, hnot]
    exact he hz
  intro v p hp
  obtain ⟨z, hz, hzsupport⟩ :=
    exists_nonzero_cycleSpace_supported_on_internal_of_selectedGraph_cycle
      C.Γ C.root C.root_structure w p hp hsupport
  have htest : ∀ e, e ∉ C.testEdges → z.1 e = 0 := by
    intro e he
    by_contra hne
    have hint := (hzsupport e hne).1
    have hmem : e ∈ C.testEdges := by rw [C.testEdges_internal]; exact hint
    exact he hmem
  have hselected : ∀ e, z.1 e ≠ 0 → (C.marginal x).1 e ≠ 0 := by
    intro e he
    have hw := (hzsupport e he).2
    have hint := (hzsupport e he).1
    simpa [w, hint] using hw
  exact C.no_selected_test_cycle_over_good_outside_forest x z hgood hz htest hselected

end ReducedEventTransportCertificate

namespace ReducedEventTransportCertificate

variable (C : ReducedEventTransportCertificate G I)

def AuxSrc (C : ReducedEventTransportCertificate G I) (x : C.Γ.EdgeWord)
    (v : C.Γ.Vertex) :=
  {e : C.Γ.Edge // x e ≠ 0 ∧ C.Γ.src e = v}

def AuxDst (C : ReducedEventTransportCertificate G I) (x : C.Γ.EdgeWord)
    (v : C.Γ.Vertex) :=
  {e : C.Γ.Edge // x e ≠ 0 ∧ C.Γ.dst e = v}

def AuxInc (C : ReducedEventTransportCertificate G I) (x : C.Γ.EdgeWord)
    (v : C.Γ.Vertex) := Sum (AuxSrc C x v) (AuxDst C x v)

def SelectedRestrictedIncident (C : ReducedEventTransportCertificate G I) (y : G.CycleSpace)
    (v : C.Γ.Vertex) :=
  {p : G.RestrictedEdge I.witnessEdgesᶜ //
    (G.restrictWord I.witnessEdgesᶜ y.1) p ≠ 0 ∧
      G.incident p.1 (C.vertexMap v)}

/-- Each selected auxiliary source/target incidence maps to its chosen physical
endpoint label. Endpoint orientation is irrelevant here: physical degree on
the restricted graph counts incident labels. -/
theorem restricted_selectedDegree_le_of_endpoint_labels
    (C : ReducedEventTransportCertificate G I)
    (H : Finset C.Γ.Vertex) (v : C.Γ.Vertex)
    (x : C.Γ.EdgeWord) (y : G.CycleSpace)
    (hx_internal : ∀ e, x e ≠ 0 → e ∈ internalEdges C.Γ H)
    (sourceLabel targetLabel : C.Γ.Edge → G.Edge)
    (hsource_mem : ∀ e, sourceLabel e ∈ (C.edgePath e).support)
    (htarget_mem : ∀ e, targetLabel e ∈ (C.edgePath e).support)
    (hsource_outside : ∀ e, x e ≠ 0 → sourceLabel e ∉ I.witnessEdges)
    (htarget_outside : ∀ e, x e ≠ 0 → targetLabel e ∉ I.witnessEdges)
    (hsource_incident : ∀ e, G.incident (sourceLabel e) (C.vertexMap (C.Γ.src e)))
    (htarget_incident : ∀ e, G.incident (targetLabel e) (C.vertexMap (C.Γ.dst e)))
    (hsource_selected : ∀ e, e ∈ internalEdges C.Γ H → x e ≠ 0 →
      y.1 (sourceLabel e) ≠ 0)
    (htarget_selected : ∀ e, e ∈ internalEdges C.Γ H → x e ≠ 0 →
      y.1 (targetLabel e) ≠ 0)
    (hloopless : ∀ e, e ∈ internalEdges C.Γ H → C.Γ.src e ≠ C.Γ.dst e) :
    selectedDegree C.Γ x v ≤
      G.restrictedSelectedDegree I.witnessEdgesᶜ
        (G.restrictWord I.witnessEdgesᶜ y.1) (C.vertexMap v) := by
  classical
  let f : AuxInc C x v → SelectedRestrictedIncident C y v := fun z =>
    match z with
    | Sum.inl a =>
        ⟨⟨sourceLabel a.1, Finset.mem_compl.mpr (hsource_outside a.1 a.2.1)⟩,
          by
            constructor
            · simpa [PhysicalGraph.restrictWord] using
                hsource_selected a.1 (hx_internal a.1 a.2.1) a.2.1
            · have hvm : C.vertexMap (C.Γ.src a.1) = C.vertexMap v :=
                congrArg C.vertexMap a.2.2
              rcases hsource_incident a.1 with hs | ht
              · exact Or.inl (hs.trans hvm)
              · exact Or.inr (ht.trans hvm)⟩
    | Sum.inr a =>
        ⟨⟨targetLabel a.1, Finset.mem_compl.mpr (htarget_outside a.1 a.2.1)⟩,
          by
            constructor
            · simpa [PhysicalGraph.restrictWord] using
                htarget_selected a.1 (hx_internal a.1 a.2.1) a.2.1
            · have hvm : C.vertexMap (C.Γ.dst a.1) = C.vertexMap v :=
                congrArg C.vertexMap a.2.2
              rcases htarget_incident a.1 with hs | ht
              · exact Or.inl (hs.trans hvm)
              · exact Or.inr (ht.trans hvm)⟩
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hp : sourceLabel a.1 = sourceLabel b.1 := congrArg (fun z => z.1.1) hab
        have he : a.1 = b.1 := by
          by_cases he : a.1 = b.1
          · exact he
          · have hd := C.edgePaths_disjoint a.1 b.1 he
            have hm := Finset.disjoint_left.mp hd (hsource_mem a.1)
            exact (hm (hp ▸ hsource_mem b.1)).elim
        exact congrArg Sum.inl (Subtype.ext he)
      | inr b =>
        have hp : sourceLabel a.1 = targetLabel b.1 := congrArg (fun z => z.1.1) hab
        by_cases he : a.1 = b.1
        · have hdst : C.Γ.dst a.1 = v := by rw [he]; exact b.2.2
          exact (hloopless a.1 (hx_internal a.1 a.2.1)
            (a.2.2.trans hdst.symm)).elim
        · have hd := C.edgePaths_disjoint a.1 b.1 he
          have hm := Finset.disjoint_left.mp hd (hsource_mem a.1)
          exact (hm (hp ▸ htarget_mem b.1)).elim
    | inr a =>
      cases b with
      | inl b =>
        have hp : targetLabel a.1 = sourceLabel b.1 := congrArg (fun z => z.1.1) hab
        by_cases he : a.1 = b.1
        · have hsrc : C.Γ.src a.1 = v := by rw [he]; exact b.2.2
          exact (hloopless a.1 (hx_internal a.1 a.2.1)
            (hsrc.trans a.2.2.symm)).elim
        · have hd := C.edgePaths_disjoint a.1 b.1 he
          have hm := Finset.disjoint_left.mp hd (htarget_mem a.1)
          exact (hm (hp ▸ hsource_mem b.1)).elim
      | inr b =>
        have hp : targetLabel a.1 = targetLabel b.1 := congrArg (fun z => z.1.1) hab
        have he : a.1 = b.1 := by
          by_cases he : a.1 = b.1
          · exact he
          · have hd := C.edgePaths_disjoint a.1 b.1 he
            have hm := Finset.disjoint_left.mp hd (htarget_mem a.1)
            exact (hm (hp ▸ htarget_mem b.1)).elim
        exact congrArg Sum.inr (Subtype.ext he)
  letI : Fintype (AuxInc C x v) := by unfold AuxInc AuxSrc AuxDst; infer_instance
  letI : Fintype (SelectedRestrictedIncident C y v) := by
    unfold SelectedRestrictedIncident
    infer_instance
  have hc := Fintype.card_le_of_injective f hf
  have haux : Fintype.card (AuxInc C x v) = CleanupSpecification.selectedDegree C.Γ x v := by
    simp [AuxInc, AuxSrc, AuxDst, CleanupSpecification.selectedDegree, Fintype.card_sum,
      Fintype.card_subtype, Finset.filter_filter, and_assoc,
      and_left_comm, and_comm]
  have hphys : Fintype.card (SelectedRestrictedIncident C y v) ≤
      G.restrictedSelectedDegree I.witnessEdgesᶜ
        (G.restrictWord I.witnessEdgesᶜ y.1) (C.vertexMap v) := by
    simp [SelectedRestrictedIncident, PhysicalGraph.restrictedSelectedDegree,
      Fintype.card_subtype, Finset.filter_filter, and_assoc, and_left_comm, and_comm]
  rw [← haux]
  exact hc.trans hphys


end ReducedEventTransportCertificate


namespace ReducedEventTransportCertificate

variable (C : ReducedEventTransportCertificate G I)

theorem rootRestriction_mem_internal (y : C.Γ.CycleSpace) (e : C.Γ.Edge)
    (hne : (if e ∈ internalEdges C.Γ C.root then y.1 e else 0) ≠ 0) :
    e ∈ internalEdges C.Γ C.root := by
  by_contra h
  simp [h] at hne

theorem rootRestriction_loopless (y : C.Γ.CycleSpace) :
    ∀ e, (if e ∈ internalEdges C.Γ C.root then y.1 e else 0) ≠ 0 →
      C.Γ.src e ≠ C.Γ.dst e := by
  intro e he
  have hint := C.rootRestriction_mem_internal y e he
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hint
  exact C.root_structure.2.1 e hint.1 hint.2

theorem rootRestriction_noParallel (y : C.Γ.CycleSpace) :
    ∀ e f, e ≠ f →
      (if e ∈ internalEdges C.Γ C.root then y.1 e else 0) ≠ 0 →
      (if f ∈ internalEdges C.Γ C.root then y.1 f else 0) ≠ 0 →
      ((C.Γ.src e = C.Γ.src f ∧ C.Γ.dst e = C.Γ.dst f) ∨
       (C.Γ.src e = C.Γ.dst f ∧ C.Γ.dst e = C.Γ.src f)) → False := by
  intro e f hef he hf horient
  have hintE := C.rootRestriction_mem_internal y e he
  have hintF := C.rootRestriction_mem_internal y f hf
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hintE hintF
  have hlabel := C.root_structure.2.2 e f hintE.1 hintE.2 hintF.1 hintF.2 horient
  exact hef hlabel

theorem auxiliaryGood_of_acyclic_and_degree (y : C.Γ.CycleSpace)
    (hacyclic : (selectedGraph C.Γ
      (fun e => if e ∈ internalEdges C.Γ C.root then y.1 e else 0)).IsAcyclic)
    (hdegree : ∀ v, selectedDegree C.Γ
      (fun e => if e ∈ internalEdges C.Γ C.root then y.1 e else 0) v ≤ 2) :
    auxiliaryCleanupGood C.Γ C.root y := by
  unfold auxiliaryCleanupGood IsLinearForestWord
  exact ⟨C.rootRestriction_loopless y,
    C.rootRestriction_noParallel y, hacyclic, hdegree⟩

/-- Endpoint labels from recorded paths inject auxiliary incidences into the
outside physical incidences, so the original degree-two bound transports. -/
theorem root_selectedDegree_le_restrictedSelectedDegree
    (C : ReducedEventTransportCertificate G I) (v : C.Γ.Vertex)
    (y : G.CycleSpace)
    (hcoord : ∀ e p, p ∈ (C.edgePath e).support →
      (C.marginal y).1 e = y.1 p) :
    selectedDegree C.Γ
      (fun e => if e ∈ internalEdges C.Γ C.root then (C.marginal y).1 e else 0) v ≤
    G.restrictedSelectedDegree I.witnessEdgesᶜ
      (G.restrictWord I.witnessEdgesᶜ y.1) (C.vertexMap v) := by
  classical
  let endpointPair : C.Γ.Edge → G.Edge × G.Edge := fun e =>
    Classical.choose (show ∃ z : G.Edge × G.Edge,
      z.1 ∈ (C.edgePath e).support ∧ z.2 ∈ (C.edgePath e).support ∧
      G.incident z.1 (C.vertexMap (C.Γ.src e)) ∧
      G.incident z.2 (C.vertexMap (C.Γ.dst e)) from by
        obtain ⟨p, q, hp, hq, hpi, hqi⟩ := C.endpoint_edges e
        exact ⟨(p, q), hp, hq, hpi, hqi⟩)
  let sourceLabel : C.Γ.Edge → G.Edge := fun e => (endpointPair e).1
  let targetLabel : C.Γ.Edge → G.Edge := fun e => (endpointPair e).2
  have hlabels : ∀ e,
      sourceLabel e ∈ (C.edgePath e).support ∧
      targetLabel e ∈ (C.edgePath e).support ∧
      G.incident (sourceLabel e) (C.vertexMap (C.Γ.src e)) ∧
      G.incident (targetLabel e) (C.vertexMap (C.Γ.dst e)) := by
    intro e
    exact Classical.choose_spec (show ∃ z : G.Edge × G.Edge,
      z.1 ∈ (C.edgePath e).support ∧ z.2 ∈ (C.edgePath e).support ∧
      G.incident z.1 (C.vertexMap (C.Γ.src e)) ∧
      G.incident z.2 (C.vertexMap (C.Γ.dst e)) from by
        obtain ⟨p, q, hp, hq, hpi, hqi⟩ := C.endpoint_edges e
        exact ⟨(p, q), hp, hq, hpi, hqi⟩)
  let x : C.Γ.EdgeWord := fun e =>
    if e ∈ internalEdges C.Γ C.root then (C.marginal y).1 e else 0
  have hx_internal : ∀ e, x e ≠ 0 → e ∈ internalEdges C.Γ C.root := by
    intro e hx
    by_contra hnot
    simp [x, hnot] at hx
  have houtside : ∀ e, x e ≠ 0 → sourceLabel e ∉ I.witnessEdges ∧
      targetLabel e ∉ I.witnessEdges := by
    intro e he
    have hint := hx_internal e he
    have htest : e ∈ C.testEdges := by rw [C.testEdges_internal]; exact hint
    exact ⟨C.tested_paths_in_complement e htest (sourceLabel e) (hlabels e).1,
      C.tested_paths_in_complement e htest (targetLabel e) (hlabels e).2.1⟩
  have hselected : ∀ e, e ∈ internalEdges C.Γ C.root → x e ≠ 0 →
      y.1 (sourceLabel e) ≠ 0 ∧ y.1 (targetLabel e) ≠ 0 := by
    intro e he hxne
    have hm : (C.marginal y).1 e ≠ 0 := by simpa [x, he] using hxne
    exact ⟨by rw [← hcoord e (sourceLabel e) (hlabels e).1]; exact hm,
      by rw [← hcoord e (targetLabel e) (hlabels e).2.1]; exact hm⟩
  have hloopless : ∀ e, e ∈ internalEdges C.Γ C.root →
      C.Γ.src e ≠ C.Γ.dst e := by
    intro e he
    have hs : C.Γ.src e ∈ C.root := (Finset.mem_filter.mp he).2.1
    have ht : C.Γ.dst e ∈ C.root := (Finset.mem_filter.mp he).2.2
    exact C.root_structure.2.1 e hs ht
  apply C.restricted_selectedDegree_le_of_endpoint_labels C.root v x y hx_internal sourceLabel targetLabel
  · exact fun e => (hlabels e).1
  · exact fun e => (hlabels e).2.1
  · exact fun e he => (houtside e he).1
  · exact fun e he => (houtside e he).2
  · exact fun e => (hlabels e).2.2.1
  · exact fun e => (hlabels e).2.2.2
  · exact fun e he hxne => (hselected e he hxne).1
  · exact fun e he hxne => (hselected e he hxne).2
  · exact hloopless

/-- Pointwise event transport from only reduced route/lift data. -/
theorem good_event_maps_of_reduced_routes
    (C : ReducedEventTransportCertificate G I)
    (x : G.CycleSpace) (hgood : originalCleanupGood G I x) :
    auxiliaryCleanupGood C.Γ C.root (C.marginal x) := by
  have hacyclic := C.selected_root_restriction_acyclic_of_original_good x hgood
  have hcoord : ∀ e p, p ∈ (C.edgePath e).support →
      (C.marginal x).1 e = x.1 p := C.marginal_agrees_on_path x
  have hdegree : ∀ v, selectedDegree C.Γ
      (fun e => if e ∈ internalEdges C.Γ C.root then (C.marginal x).1 e else 0) v ≤ 2 := by
    intro v
    calc
      selectedDegree C.Γ
          (fun e => if e ∈ internalEdges C.Γ C.root then (C.marginal x).1 e else 0) v
          ≤ G.restrictedSelectedDegree I.witnessEdgesᶜ
              (G.restrictWord I.witnessEdgesᶜ x.1) (C.vertexMap v) :=
        C.root_selectedDegree_le_restrictedSelectedDegree v x hcoord
      _ ≤ 2 := hgood.2 (C.vertexMap v)
  exact C.auxiliaryGood_of_acyclic_and_degree (C.marginal x) hacyclic hdegree

end ReducedEventTransportCertificate

end Erdos1016.Proof.ReducedForestEventTransfer

end

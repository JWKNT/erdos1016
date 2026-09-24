import Erdos1016.Cleanup.Support.ActiveDegreeControl
import Erdos1016.Cleanup.Transport.SupportCycleSpaceEquivalence
import Erdos1016.Extremal.Capacity.ComponentRankExtraction
import Erdos1016.Cleanup.Protection.ParallelEndpointCardinality

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ComponentWitnessCorridorGeometry

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.ActiveComponentRankSum
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.CorridorPairedPathCertificates
open Erdos1016.Proof.ProtectedExteriorComponents
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.CompressedComponentLift

open Erdos1016.Proof.CompressedRouteDecomposition

open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.OutsideComponentRoot

open Erdos1016.Proof.PostProtectionSimplicity

open Erdos1016.Proof.ActiveDegreeExtraction
open Erdos1016.Proof.BadVertexCardinalityBound
open Erdos1016.Proof.ActiveDegreeControl
open Erdos1016.Proof.ParallelEndpointCardinality
open Erdos1016.Proof.ParallelProtectionComplement
open Erdos1016.Proof.ActiveComponentSurvival
open Erdos1016.Proof.ProtectedDeletionRankLedger
open Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge
open Erdos1016.Proof.RestrictedComponentGraph
open Erdos1016.Proof.ComponentCorridorReindexing
open Erdos1016.Proof.SupportCycleSpaceEquivalence

variable {G : PhysicalGraph} {c : ActiveComponent G} {I : CleanupInput G}

local instance {V : Type*} (J : SimpleGraph V) : DecidableRel J.Adj := Classical.decRel _


/-- Active-subgraph degree counts its incident physical edge labels. -/
private theorem active_degree_eq_incident_card
    (G : PhysicalGraph) (v : (activeSubgraph G).Vertex) :
    (activeSubgraph G).degree v =
      (PhysicalSimpleGraphDegreeBridge.incidentEdges (activeSubgraph G) v).card := by
  unfold PhysicalGraph.degree PhysicalGraph.selectedDegree
  congr 1
  ext e
  simp [PhysicalSimpleGraphDegreeBridge.incidentEdges, PhysicalGraph.incident]

/-- If a vertex is outside the witness endpoints, every incident active edge
is counted by the outside-witness active-star bound. -/
theorem active_degree_le_outside_star
    (G : PhysicalGraph) (I : CleanupInput G) (R : ℕ)
    (v : (activeSubgraph G).Vertex) (hv : v ∉ I.witnessVertices)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability I.witnessEdges) :
    (activeSubgraph G).degree v ≤
      (activeOutsideIncidentEdges G I.witnessEdges v).card := by
  classical
  let A := activeSubgraph G
  let S := PhysicalSimpleGraphDegreeBridge.incidentEdges A v
  let T := activeOutsideIncidentEdges G I.witnessEdges v
  let Eact := activeEdges G
  let edgeIso := G.restrictedEdgeEquiv Eact
  let f : {e : A.Edge // e ∈ S} → {e : G.Edge // e ∈ T} := fun e => by
    let g := edgeIso e.1
    have hinc : G.incident g.1 v := by
      simpa [A, g, edgeIso, PhysicalGraph.incident,
        PhysicalGraph.restrictPhysical] using
        (Finset.mem_filter.mp e.2).2
    have hactive : Erdos1016.Proof.ActiveEdgeUniform.ActiveEdge G g.1 :=
      (mem_activeEdges_iff G g.1).1 g.2
    have hnot : g.1 ∉ I.witnessEdges := by
      intro hw
      have hend := I.witness_endpoints g.1 hw
      exact hv (by
        rcases hinc with hs | ht
        · rw [← hs]
          exact hend.1
        · rw [← ht]
          exact hend.2)
    exact ⟨g.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hactive, hnot, hinc⟩⟩
  have hinj : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have hval : (edgeIso e.1).1 = (edgeIso e'.1).1 := by
      have hh := congrArg (fun a : {e : G.Edge // e ∈ T} => a.1) he
      simpa [f] using hh
    have heq : edgeIso e.1 = edgeIso e'.1 := Subtype.ext hval
    exact edgeIso.injective heq
  have hcard : Fintype.card {e : A.Edge // e ∈ S} ≤
      Fintype.card {e : G.Edge // e ∈ T} := Fintype.card_le_of_injective f hinj
  calc
    A.degree v = S.card := active_degree_eq_incident_card G v
    _ = Fintype.card {e : A.Edge // e ∈ S} := (Fintype.card_coe S).symm
    _ ≤ Fintype.card {e : G.Edge // e ∈ T} := hcard
    _ = T.card := Fintype.card_coe T

/-- The bad-set certificate turns the active outside-star bound into the
subcubic upper bound needed away from witness and bad vertices. -/
theorem active_degree_eq_two_or_three_off_witness_bad
    (G : PhysicalGraph) (I : CleanupInput G) (R : ℕ)
    (v : (activeSubgraph G).Vertex)
    (hincident : ∃ e : (activeSubgraph G).Edge, (activeSubgraph G).incident e v)
    (hvWitness : v ∉ I.witnessVertices)
    (hvBad : v ∉ badVertexSet G I.witnessEdges)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability I.witnessEdges) :
    (activeSubgraph G).degree v = 2 ∨ (activeSubgraph G).degree v = 3 := by
  have hupper := active_degree_le_outside_star G I R v hvWitness hprob
  have hlt : (activeOutsideIncidentEdges G I.witnessEdges v).card < 4 := by
    by_contra hn
    have hn' : 4 ≤ (activeOutsideIncidentEdges G I.witnessEdges v).card := by omega
    have hmem : v ∈ badVertexSet G I.witnessEdges := by
      simp [badVertexSet, hn']
    exact hvBad hmem
  have hle3 : (activeSubgraph G).degree v ≤ 3 := by omega
  have hge2 : 2 ≤ (activeSubgraph G).degree v := by
    rcases hincident with ⟨e, hi⟩
    exact Erdos1016.Proof.ActiveComponentMinimumDegree.activeSubgraph_degree_ge_two_of_incident G e v hi
  omega

/-- An edge-bearing active component has no isolated vertex in its support. -/
theorem componentSupportVertex_incident_of_edge
    (G : PhysicalGraph) (c : ActiveComponent G)
    (e₀ : (activeSubgraph G).Edge) (he₀ : edgeComponent G e₀ = c)
    (v : (componentSupportPhysical G c).Vertex) :
    ∃ e : (activeSubgraph G).Edge,
      (activeSubgraph G).incident e (componentSupportVertexMap G c v) := by
  classical
  let A := activeSubgraph G
  let x := componentSupportVertexMap G c v
  let y := A.src e₀
  have hx : componentOf G x = c :=
    (mem_componentSupportFinset G c x).1
      (componentSupportVertexMap_mem_support G c v)
  have hy : componentOf G y = c := by
    simpa [edgeComponent, y] using he₀
  by_cases hxy : x = y
  · refine ⟨e₀, ?_⟩
    change A.src e₀ = x ∨ A.dst e₀ = x
    rw [hxy]
    exact Or.inl rfl
  · have hreach : A.toSimpleGraph.Reachable x y :=
      SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
    obtain ⟨p⟩ := hreach
    obtain ⟨w, hadj, p', _⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hxy p
    have hadj' : A.toSimpleGraph.Adj x w := by simpa using hadj
    rcases hadj' with ⟨f, _, hsrc | hdst⟩
    · exact ⟨f, Or.inl hsrc.1⟩
    · exact ⟨f, Or.inr hdst.2⟩

/-- Protected vertices for a component-local corridor partition: just the
witness endpoints and the high active-outside-degree vertices that the
cleanup argument charges separately. -/
def componentWitnessBadProtected (G : PhysicalGraph) (c : ActiveComponent G)
    (I : CleanupInput G) : Finset (componentSupportPhysical G c).Vertex := by
  classical
  exact Finset.univ.filter fun v =>
    componentSupportVertexMap G c v ∈ I.witnessVertices ∪ badVertexSet G I.witnessEdges

/-- Witness labels restricted to the support-carrier physical component. -/
def componentLocalWitnessPullback (G : PhysicalGraph) (c : ActiveComponent G)
    (I : CleanupInput G) : Finset (componentSupportPhysical G c).Edge := by
  classical
  exact Finset.univ.filter fun q =>
    componentCorridorEdgeToOriginal G c (componentSupportEdgeEquiv G c q) ∈ I.witnessEdges

/-- Compressed auxiliary vertices representing vertices in a local support
protected set. -/
def componentSupportCompressedProtectedVertices
    (G : PhysicalGraph) (c : ActiveComponent G)
    {P : Finset (componentSupportPhysical G c).Vertex}
    {W : Finset (componentSupportPhysical G c).Edge}
    (D : CorridorPartition (componentSupportPhysical G c) P W)
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c) P ∧
      corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c) P) :
    Finset (compressedCorridorGraph D hend).Vertex := by
  classical
  exact Finset.univ.filter fun v => compressedCorridorVertexMap D hend v ∈ P






theorem componentLocalWitnessPullback_endpoints
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    (q : (componentSupportPhysical G c).Edge)
    (hq : q ∈ componentLocalWitnessPullback G c I) :
    (componentSupportPhysical G c).src q ∈ componentWitnessBadProtected G c I ∧
      (componentSupportPhysical G c).dst q ∈ componentWitnessBadProtected G c I := by
  classical
  have horiginal : componentCorridorEdgeToOriginal G c
      (componentSupportEdgeEquiv G c q) ∈ I.witnessEdges :=
    (Finset.mem_filter.mp hq).2
  have hends := I.witness_endpoints _ horiginal
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_union_left
    have hs := src_componentCorridorEdgeToOriginal G c
      (componentSupportEdgeEquiv G c q)
    have hs' := componentSupportEdgeEquiv_src G c q
    rw [hs, hs'] at hends
    exact hends.1
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_union_left
    have ht := dst_componentCorridorEdgeToOriginal G c
      (componentSupportEdgeEquiv G c q)
    have ht' := componentSupportEdgeEquiv_dst G c q
    rw [ht, ht'] at hends
    exact hends.2

/-- The support-local witness/bad protected set inherits the CleanupInput
cardinality scale: witness endpoints cost at most the witness edge count, and
bad vertices cost at most `520 R`. -/
theorem componentWitnessBadProtected_card_le
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    (hbad : (badVertexSet G I.witnessEdges).card ≤ 520 * I.R) :
    (componentWitnessBadProtected G c I).card ≤
      I.witnessEdges.card + 520 * I.R := by
  classical
  let U := I.witnessVertices ∪ badVertexSet G I.witnessEdges
  let P := componentWitnessBadProtected G c I
  let f : {v : (componentSupportPhysical G c).Vertex // v ∈ P} →
      {u : G.Vertex // u ∈ U} := fun v => by
    refine ⟨componentSupportVertexMap G c v.1, ?_⟩
    have hv := (Finset.mem_filter.mp v.2).2
    simpa [P, componentWitnessBadProtected, U] using hv
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hval := congrArg (fun z : {u : G.Vertex // u ∈ U} => z.1) h
    exact componentSupportVertexMap_injective G c (by simpa [f] using hval)
  have hcard := Fintype.card_le_of_injective f hinj
  calc
    P.card = Fintype.card {v : (componentSupportPhysical G c).Vertex // v ∈ P} :=
      (Fintype.card_coe P).symm
    _ ≤ Fintype.card {u : G.Vertex // u ∈ U} := hcard
    _ = U.card := Fintype.card_coe U
    _ ≤ I.witnessVertices.card + (badVertexSet G I.witnessEdges).card :=
      Finset.card_union_le _ _
    _ ≤ I.witnessEdges.card + 520 * I.R := by
      exact Nat.add_le_add I.vertices_le_edges hbad

/-- Instantiate the preceding protected-set count directly from the
CleanupInput hypotheses. -/
theorem componentWitnessBadProtected_card_le_of_cleanup_input
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    (hR : 5 ≤ I.R) :
    (componentWitnessBadProtected G c I).card ≤
      I.witnessEdges.card + 520 * I.R := by
  have hlocal := active_degree_and_bad_vertex_bounds G I.witnessEdges I.R hR
    I.outside_probability I.graph_connected
  exact componentWitnessBadProtected_card_le G c I (Nat.le_of_lt hlocal.2)



theorem componentSupportCompressedProtectedVertices_card_le
    (G : PhysicalGraph) (c : ActiveComponent G)
    {P : Finset (componentSupportPhysical G c).Vertex}
    {W : Finset (componentSupportPhysical G c).Edge}
    (D : CorridorPartition (componentSupportPhysical G c) P W)
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c) P ∧
      corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c) P) :
    (componentSupportCompressedProtectedVertices G c D hend).card ≤ P.card := by
  classical
  let Q := componentSupportCompressedProtectedVertices G c D hend
  let f : {q : (compressedCorridorGraph D hend).Vertex // q ∈ Q} →
      {v : (componentSupportPhysical G c).Vertex // v ∈ P} := fun q => by
    refine ⟨compressedCorridorVertexMap D hend q.1, ?_⟩
    exact (Finset.mem_filter.mp q.2).2
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hval := congrArg
      (fun z : {v : (componentSupportPhysical G c).Vertex // v ∈ P} => z.1) h
    exact compressedCorridorVertexMap_injective D hend (by simpa [f] using hval)
  have hcard := Fintype.card_le_of_injective f hinj
  calc
    Q.card = Fintype.card {q : (compressedCorridorGraph D hend).Vertex // q ∈ Q} :=
      (Fintype.card_coe Q).symm
    _ ≤ Fintype.card {v : (componentSupportPhysical G c).Vertex // v ∈ P} := hcard
    _ = P.card := Fintype.card_coe P

theorem exists_component_local_corridor_partition_connected
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    (e₀ : (activeSubgraph G).Edge) (he₀ : edgeComponent G e₀ = c)
    (hWnonempty : (componentLocalWitnessPullback G c I).Nonempty) :
    ∃ D : CorridorPartition (componentSupportPhysical G c)
        (componentWitnessBadProtected G c I)
        (componentLocalWitnessPullback G c I),
      ∃ hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [],
      ∃ hendpoints : ∀ C ∈ D.corridors,
        corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c)
          (componentWitnessBadProtected G c I) ∧
        corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c)
          (componentWitnessBadProtected G c I),
        (componentWitnessBadProtected G c I).Nonempty ∧
        (compressedCorridorGraph D hendpoints).toSimpleGraph.Connected := by
  classical
  let H := componentSupportPhysical G c
  let P := componentWitnessBadProtected G c I
  let W := componentLocalWitnessPullback G c I
  have hincident : ∀ v : H.Vertex, ∃ e : (activeSubgraph G).Edge,
      (activeSubgraph G).incident e (componentSupportVertexMap G c v) :=
    fun v => componentSupportVertex_incident_of_edge G c e₀ he₀ v
  have hP : P.Nonempty := by
    obtain ⟨q, hq⟩ := hWnonempty
    obtain ⟨hs, _⟩ := componentLocalWitnessPullback_endpoints G c I q hq
    exact ⟨H.src q, hs⟩
  have hdegree : ∀ v, v ∉ P → H.degree v = 2 ∨ H.degree v = 3 := by
    intro v hv
    have hvbad : componentSupportVertexMap G c v ∉ badVertexSet G I.witnessEdges := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ h⟩)
    have hvwit : componentSupportVertexMap G c v ∉ I.witnessVertices := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_left _ h⟩)
    have hlocal := active_degree_eq_two_or_three_off_witness_bad G I I.R
      (componentSupportVertexMap G c v) (hincident v) hvwit hvbad I.outside_probability
    have hdegreeEq := componentSupportPhysical_degree_eq G c
      ((Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
        (componentSupportFinset G c))).symm v)
    have hphysical : H.degree v = (activeSubgraph G).degree
        (componentSupportVertexMap G c v) := by
      calc
        H.degree v = (activeSubgraph G).toSimpleGraph.degree
            (componentSupportVertexMap G c v) := by simpa [H, componentSupportVertexMap] using hdegreeEq
        _ = (activeSubgraph G).degree (componentSupportVertexMap G c v) :=
          (Erdos1016.Nonbacktracking.FiniteTwoCore.original_degree_eq_graph_degree
            (activeSubgraph G) (componentSupportVertexMap G c v)).symm
    rw [← hphysical] at hlocal
    exact hlocal
  have hWends : ∀ e ∈ W, H.src e ∈ P ∧ H.dst e ∈ P := by
    intro e he
    exact componentLocalWitnessPullback_endpoints G c I e he
  let D : CorridorPartition H P W :=
    CoreComponentAssembly.exists_corridor_partition_of_degree_two_three
      H P W (componentSupportPhysical_connected G c) hP hdegree hWends
  let hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [] :=
    CoreComponentAssembly.corridor_partition_edges_nonempty_of_degree_two_three
      H P W (componentSupportPhysical_connected G c) hP hdegree hWends
  let hendpoints : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch H P ∧ corridorFinish C ∈ protectedOrBranch H P :=
    CoreComponentAssembly.canonical_assembled_partition_endpoints_retained
      H P W (componentSupportPhysical_connected G c) hP hdegree hWends
  refine ⟨D, hnonempty, hendpoints, hP, ?_⟩
  exact AssembledCorridorCompression.canonicalCompressedCorridorGraph_connected
    H P W hWends (componentSupportPhysical_connected G c) hP hdegree



/-- The compressed degree is exactly the degree in the support graph: every
endpoint slot is identified with its unique physical incident edge. -/
theorem component_support_compressed_degree_eq
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    {P : Finset (componentSupportPhysical G c).Vertex}
    {W : Finset (componentSupportPhysical G c).Edge}
    (D : CorridorPartition (componentSupportPhysical G c) P W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c) P ∧
      corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c) P)
    (q : (compressedCorridorGraph D hend).Vertex) :
    ambientDegree (compressedCorridorGraph D hend) q =
      (activeSubgraph G).degree
        (componentSupportVertexMap G c
          (compressedCorridorVertexMap D hend q)) := by
  have hcompressed :=
    Erdos1016.Proof.EndpointIncidenceBijection.compressedCorridor_ambientDegree_eq_physical_degree
      D hnonempty hend q
  have hlocal := componentSupportPhysical_degree_eq G c
    ((Fintype.equivFin (Erdos1016.BoundaryTrace.Network.Shore.InsideVertex
      (componentSupportFinset G c))).symm (compressedCorridorVertexMap D hend q))
  have hphysical :
      (componentSupportPhysical G c).degree (compressedCorridorVertexMap D hend q) =
        (activeSubgraph G).degree
          (componentSupportVertexMap G c
            (compressedCorridorVertexMap D hend q)) := by
    calc
      (componentSupportPhysical G c).degree (compressedCorridorVertexMap D hend q) =
          (activeSubgraph G).toSimpleGraph.degree
            (componentSupportVertexMap G c (compressedCorridorVertexMap D hend q)) := by
        simpa [componentSupportVertexMap] using hlocal
      _ = (activeSubgraph G).degree
            (componentSupportVertexMap G c (compressedCorridorVertexMap D hend q)) :=
        (Erdos1016.Nonbacktracking.FiniteTwoCore.original_degree_eq_graph_degree
          (activeSubgraph G)
          (componentSupportVertexMap G c (compressedCorridorVertexMap D hend q))).symm
  rw [hcompressed, hphysical]







/-- Preserve a large-rank active component while extracting its witness-local
corridor data. Every edge-bearing active component meets the CleanupInput
witness set under the `> 1/2` consequence of the outside-probability bound. -/
theorem exists_large_rank_component_local_corridor_partition_connected
    (G : PhysicalGraph) (I : CleanupInput G)
    (hcount : (nonemptyActiveComponents G).card < 5 * I.R)
    (hrank : 0 < G.cycleRank) :
    ∃ c ∈ nonemptyActiveComponents G,
      ∃ D : CorridorPartition (componentSupportPhysical G c)
          (componentWitnessBadProtected G c I)
          (componentLocalWitnessPullback G c I),
        ∃ hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [],
        ∃ hendpoints : ∀ C ∈ D.corridors,
          corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c)
            (componentWitnessBadProtected G c I) ∧
          corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c)
            (componentWitnessBadProtected G c I),
        (componentWitnessBadProtected G c I).Nonempty ∧
        (compressedCorridorGraph D hendpoints).toSimpleGraph.Connected ∧
        G.cycleRank ≤ 5 * I.R *
          (componentSupportPhysical G c).cycleRank := by
  classical
  obtain ⟨c, hc, hshare⟩ :=
    Erdos1016.Proof.ActivePhysicalComponents.exists_activeComponent_large_rank_of_screen
      G I.R hcount hrank
  have hRpos : 0 < I.R := by
    by_contra hn
    have hRzero : I.R = 0 := by omega
    obtain ⟨ew, hew⟩ := I.witness_nonempty
    have hwcard : 1 ≤ I.witnessEdges.card := Finset.card_pos.mpr ⟨ew, hew⟩
    have hbudget : I.witnessEdges.card + 1 ≤ 1 := by
      simpa [hRzero] using I.witness_edges_budget
    omega
  have hhalf : (1 / 2 : ℝ) < G.outsideLinearForestProbability I.witnessEdges := by
    have hden : (0 : ℝ) < (I.R : ℝ) := by exact_mod_cast hRpos
    have hterm : (0 : ℝ) < 1 / (I.R : ℝ) := one_div_pos.mpr hden
    linarith [I.outside_probability]
  obtain ⟨eA, heA, heW⟩ :=
    Erdos1016.Proof.ActivePhysicalComponents.every_nonempty_activeComponent_meets_witness
      G I.witnessEdges hhalf c
      (by simpa [nonemptyActiveComponents] using hc)
  let e : G.Edge := (G.restrictedEdgeEquiv (activeEdges G) eA).1
  have heW' : e ∈ I.witnessEdges := by simpa [e] using heW
  have hcomp : edgeComponent G eA = c :=
    (mem_componentEdges_iff G c eA).1 heA
  let A := activeSubgraph G
  let eR : (A.restrictPhysical (componentEdges G c)).Edge :=
    (A.restrictedEdgeEquiv (componentEdges G c)).symm ⟨eA, heA⟩
  let q : (componentSupportPhysical G c).Edge :=
    (componentSupportEdgeEquiv G c).symm eR
  have hmap : componentCorridorEdgeToOriginal G c eR = e := by
    change (G.restrictedEdgeEquiv (activeEdges G)
      ((A.restrictedEdgeEquiv (componentEdges G c) eR).1)).1 = e
    simp [e, eR, A]
  have hW : (componentLocalWitnessPullback G c I).Nonempty := by
    refine ⟨q, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change componentCorridorEdgeToOriginal G c
      (componentSupportEdgeEquiv G c q) ∈ I.witnessEdges
    rw [(componentSupportEdgeEquiv G c).apply_symm_apply]
    simpa [hmap] using heW'
  obtain ⟨D, hnonempty, hendpoints, hP, hconn⟩ :=
    exists_component_local_corridor_partition_connected G c I eA hcomp hW
  have hrankSupport :
      (componentSupportPhysical G c).cycleRank =
        (A.restrictPhysical (componentEdges G c)).cycleRank :=
    componentSupport_cycleRank_eq G c
  have hrankSupport' :
      (componentSupportPhysical G c).cycleRank =
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
    simpa [A] using hrankSupport
  refine ⟨c, hc, D, hnonempty, hendpoints, hP, hconn, ?_⟩
  rw [hrankSupport']
  exact hshare












private theorem protectedIncidentEdges_union_local (Γ : FiniteMultiGraph)
    (P Q : Finset Γ.Vertex) :
    protectedIncidentEdges Γ (P ∪ Q) =
      protectedIncidentEdges Γ P ∪ protectedIncidentEdges Γ Q := by
  classical
  ext e
  simp only [protectedIncidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  tauto

/-- Witness edges incident to a physical vertex, with edge labels retained. -/
private def localWitnessStar (G : PhysicalGraph) (I : CleanupInput G)
    (v : G.Vertex) : Finset G.Edge :=
  by classical exact I.witnessEdges.filter fun e => G.incident e v

/-- Double-counting witness incidences: a loopless witness edge contributes at
most its two endpoints, even after restricting the vertex sum to an arbitrary
finite set. -/
private theorem localWitnessStar_sum_le (G : PhysicalGraph) (I : CleanupInput G)
    (P : Finset G.Vertex) :
    (∑ v ∈ P, (localWitnessStar G I v).card) ≤ 2 * I.witnessEdges.card := by
  classical
  let inc : G.Edge → G.Vertex → ℕ := fun e v =>
    if G.incident e v then 1 else 0
  have hrewrite :
      (∑ v ∈ P, (localWitnessStar G I v).card) =
        ∑ v ∈ P, ∑ e ∈ I.witnessEdges, inc e v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [localWitnessStar, Finset.card_filter]
  rw [hrewrite, Finset.sum_comm]
  calc
    (∑ e ∈ I.witnessEdges, ∑ v ∈ P, inc e v) ≤
        ∑ e ∈ I.witnessEdges, 2 := by
          apply Finset.sum_le_sum
          intro e he
          let ends : Finset G.Vertex := {G.src e, G.dst e}
          have hP : P.filter (fun v => G.incident e v) ⊆ ends := by
            intro v hv
            have hinc := (Finset.mem_filter.mp hv).2
            change G.src e = v ∨ G.dst e = v at hinc
            simp only [ends, Finset.mem_insert, Finset.mem_singleton]
            rcases hinc with hs | ht
            · exact Or.inl hs.symm
            · exact Or.inr ht.symm
          have hcard : (P.filter (fun v => G.incident e v)).card ≤ 2 := by
            calc
              (P.filter (fun v => G.incident e v)).card ≤ ends.card := Finset.card_le_card hP
              _ ≤ 2 := by simp [ends, G.noLoops e]
          have hsumcard : (∑ v ∈ P, inc e v) =
              (P.filter (fun v => G.incident e v)).card := by
            dsimp [inc]
            rw [Finset.card_filter]
          rw [hsumcard]
          exact hcard
    _ = 2 * I.witnessEdges.card := by simp [Nat.mul_comm]

/-- Every active star splits into its witness incidences and outside-witness
active incidences. This is the pointwise input to the protected degree sum. -/
private theorem active_degree_le_star_add_witness (G : PhysicalGraph)
    (I : CleanupInput G) (v : (activeSubgraph G).Vertex) :
    (activeSubgraph G).degree v ≤
      (activeOutsideIncidentEdges G I.witnessEdges v).card +
        (localWitnessStar G I v).card := by
  classical
  let A := activeSubgraph G
  let inc := PhysicalSimpleGraphDegreeBridge.incidentEdges A v
  let T := activeOutsideIncidentEdges G I.witnessEdges v
  let U := localWitnessStar G I v
  let edgeIso := G.restrictedEdgeEquiv (activeEdges G)
  let f : {e : A.Edge // e ∈ inc} → {e : G.Edge // e ∈ T ∪ U} := fun e =>
    ⟨(edgeIso e.1).1, by
    let g := edgeIso e.1
    have hinc : G.incident g.1 v := by
      simpa [A, inc, g, edgeIso, PhysicalGraph.incident,
        PhysicalGraph.restrictPhysical] using (Finset.mem_filter.mp e.2).2
    have hactive : Erdos1016.Proof.ActiveEdgeUniform.ActiveEdge G g.1 :=
      (mem_activeEdges_iff G g.1).1 g.2
    by_cases hw : g.1 ∈ I.witnessEdges
    · apply Finset.mem_union_right T
      change g.1 ∈ I.witnessEdges.filter (fun e => G.incident e v)
      exact Finset.mem_filter.mpr ⟨hw, hinc⟩
    · apply Finset.mem_union_left U
      change g.1 ∈ Finset.univ.filter
        (fun e => ActiveEdgeUniform.ActiveEdge G e ∧ e ∉ I.witnessEdges ∧ G.incident e v)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive, hw, hinc⟩
    ⟩
  have hinj : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have hval : (edgeIso e.1).1 = (edgeIso e'.1).1 := by
      have hh := congrArg (fun a : {e : G.Edge // e ∈ T ∪ U} => a.1) he
      dsimp [f] at hh
      change (edgeIso e.1).1 = (edgeIso e'.1).1 at hh
      exact hh
    exact edgeIso.injective (Subtype.ext hval)
  have hcard := Fintype.card_le_of_injective f hinj
  have hunion : (T ∪ U).card ≤ T.card + U.card := Finset.card_union_le _ _
  calc
    A.degree v = inc.card := active_degree_eq_incident_card G v
    _ = Fintype.card {e : A.Edge // e ∈ inc} := (Fintype.card_coe inc).symm
    _ ≤ Fintype.card {e : G.Edge // e ∈ T ∪ U} := hcard
    _ = (T ∪ U).card := Fintype.card_coe _
    _ ≤ T.card + U.card := hunion



/-- The exact aggregate degree-sum premise for the protected vertices of the
compressed support graph. The compressed map is injective, so witness-star
incidences remain globally bounded by twice the number of witness edges. -/
theorem componentSupport_compressed_degree_sum_le_cleanup_budget
    (G : PhysicalGraph) (c : ActiveComponent G) (I : CleanupInput G)
    {P : Finset (componentSupportPhysical G c).Vertex}
    {W : Finset (componentSupportPhysical G c).Edge}
    (D : CorridorPartition (componentSupportPhysical G c) P W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hend : ∀ C ∈ D.corridors,
      corridorStart C ∈ protectedOrBranch (componentSupportPhysical G c) P ∧
      corridorFinish C ∈ protectedOrBranch (componentSupportPhysical G c) P)
    (hR : 5 ≤ I.R) :
    (∑ q ∈ componentSupportCompressedProtectedVertices G c D hend,
      ambientDegree (compressedCorridorGraph D hend) q) ≤
        (I.R + 1) * (componentSupportCompressedProtectedVertices G c D hend).card +
          2 * I.witnessEdges.card := by
  classical
  let H := componentSupportPhysical G c
  let Γ := compressedCorridorGraph D hend
  let Q := componentSupportCompressedProtectedVertices G c D hend
  let φ := componentSupportVertexMap G c
  let ψ := compressedCorridorVertexMap D hend
  obtain ⟨hstar, _⟩ := active_degree_and_bad_vertex_bounds G I.witnessEdges
    I.R hR I.outside_probability I.graph_connected
  have hmapInj : Function.Injective (fun q : Γ.Vertex => φ (ψ q)) := by
    intro q q' h
    apply compressedCorridorVertexMap_injective D hend
    exact componentSupportVertexMap_injective G c h
  let S : Finset (activeSubgraph G).Vertex := Q.image (fun q => φ (ψ q))
  have hstarImage :
      (∑ q ∈ Q, (localWitnessStar G I (φ (ψ q))).card) =
        ∑ v ∈ S, (localWitnessStar G I v).card := by
    rw [Finset.sum_image (fun x hx y hy hxy => hmapInj hxy)]
  have hstarGlobal :
      (∑ q ∈ Q, (localWitnessStar G I (φ (ψ q))).card) ≤
        2 * I.witnessEdges.card := by
    rw [hstarImage]
    calc
      (∑ v ∈ S, (localWitnessStar G I v).card) ≤
          ∑ v ∈ Finset.univ, (localWitnessStar G I v).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by
          intro v hv hvS
          exact Nat.zero_le _)
      _ ≤ 2 * I.witnessEdges.card := localWitnessStar_sum_le G I Finset.univ
  calc
    (∑ q ∈ Q, ambientDegree Γ q) =
        ∑ q ∈ Q, (activeSubgraph G).degree (φ (ψ q)) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact component_support_compressed_degree_eq G c I D hnonempty hend q
    _ ≤ ∑ q ∈ Q,
        ((I.R + 1) + (localWitnessStar G I (φ (ψ q))).card) := by
          apply Finset.sum_le_sum
          intro q hq
          have hpoint := active_degree_le_star_add_witness G I (φ (ψ q))
          have hout := hstar (φ (ψ q))
          omega
    _ = (I.R + 1) * Q.card +
        ∑ q ∈ Q, (localWitnessStar G I (φ (ψ q))).card := by
          rw [Finset.sum_add_distrib]
          simp [Q, Nat.mul_comm]
    _ ≤ (I.R + 1) * Q.card + 2 * I.witnessEdges.card :=
      Nat.add_le_add_left hstarGlobal _



/-- Protected-edge budget from the useful aggregate degree estimate. The
initial protected vertices may have witness incidences in addition to their
outside-witness stars, so those incidences are charged globally by `2*m`.
The endpoint additions from parallel pairs cost at most `6*M₂`. -/
theorem protected_incident_budget_of_degree_sum_and_pair_count
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex)
    (R m M₂ : ℕ)
    (hP₀sum : (∑ v ∈ P₀, ambientDegree Γ v) ≤
      (R + 1) * P₀.card + 2 * m)
    (hdegreeOutside : ∀ v, v ∉ P₀ → ambientDegree Γ v = 2 ∨
      ambientDegree Γ v = 3)
    (hpair : (eligibleUnorderedParallelPairIndices Γ P₀).card ≤ M₂) :
    (protectedIncidentEdges Γ (P₀ ∪ protectParallelEndpoints Γ P₀)).card ≤
      (R + 1) * P₀.card + 2 * m + 6 * M₂ := by
  classical
  let P₁ := protectParallelEndpoints Γ P₀
  have hp1card : P₁.card ≤ 2 * M₂ := by
    dsimp [P₁]
    exact (protectParallelEndpoints_card_le_two_mul_unorderedPairCount Γ P₀).trans
      (Nat.mul_le_mul_left 2 hpair)
  have hp1degree : ∀ v ∈ P₁, ambientDegree Γ v ≤ 3 := by
    intro v hv
    exact ambientDegree_le_three_on_protectedEndpoints Γ P₀ hdegreeOutside v
      (by simpa [P₁] using hv)
  have hp1sum : (∑ v ∈ P₁, ambientDegree Γ v) ≤ 6 * M₂ := by
    calc
      (∑ v ∈ P₁, ambientDegree Γ v) ≤ ∑ _v ∈ P₁, 3 := by
        apply Finset.sum_le_sum
        intro v hv
        exact hp1degree v hv
      _ = 3 * P₁.card := by simp [Nat.mul_comm]
      _ ≤ 3 * (2 * M₂) := Nat.mul_le_mul_left 3 hp1card
      _ = 6 * M₂ := by ring
  have hset := protectedIncidentEdges_union_local Γ P₀ P₁
  calc
    (protectedIncidentEdges Γ (P₀ ∪ P₁)).card =
        (protectedIncidentEdges Γ P₀ ∪ protectedIncidentEdges Γ P₁).card :=
      congrArg Finset.card hset
    _ ≤ (protectedIncidentEdges Γ P₀).card +
        (protectedIncidentEdges Γ P₁).card := Finset.card_union_le _ _
    _ ≤ (∑ v ∈ P₀, ambientDegree Γ v) +
        (∑ v ∈ P₁, ambientDegree Γ v) :=
      Nat.add_le_add (protectedIncidentEdges_card_le_degree_sum Γ P₀)
        (protectedIncidentEdges_card_le_degree_sum Γ P₁)
    _ ≤ ((R + 1) * P₀.card + 2 * m) + 6 * M₂ := Nat.add_le_add hP₀sum hp1sum



end Erdos1016.Proof.ComponentWitnessCorridorGeometry

end

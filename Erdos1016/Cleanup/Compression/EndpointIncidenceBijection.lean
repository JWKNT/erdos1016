import Erdos1016.Cleanup.CleanupSpecification
import Erdos1016.Cleanup.Compression.CompressedRouteDecomposition
import Erdos1016.Cleanup.Paths.CorridorTerminalEdges
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.EndpointIncidenceBijection

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.CompressedRouteDecomposition
open Erdos1016.Proof.PartitionRouteDecomposition
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.CorridorTerminalEdges

/-- The labelled endpoint incidences at one auxiliary vertex. A loop has two
distinct slots, one for each of its endpoint maps. -/
def endpointIncidences (M : FiniteMultiGraph) (q : M.Vertex) :=
  Sum {e : M.Edge // M.src e = q} {e : M.Edge // M.dst e = q}

noncomputable instance endpointIncidencesFintype
    (M : FiniteMultiGraph) (q : M.Vertex) : Fintype (endpointIncidences M q) := by
  classical
  unfold endpointIncidences
  infer_instance

/-- The labelled physical edges incident to one physical vertex. -/
def physicalIncidences (G : PhysicalGraph) (v : G.Vertex) :=
  {e : G.Edge // G.incident e v}

noncomputable instance physicalIncidencesFintype
    (G : PhysicalGraph) (v : G.Vertex) : Fintype (physicalIncidences G v) := by
  classical
  unfold physicalIncidences
  infer_instance

/-- The number of endpoint slots is exactly the ambient multigraph degree,
including both slots of every auxiliary loop. -/
theorem endpointIncidences_card
    (M : FiniteMultiGraph) (q : M.Vertex) :
    Fintype.card (endpointIncidences M q) = ambientDegree M q := by
  classical
  unfold ambientDegree
  change Fintype.card
      ({e : M.Edge // M.src e = q} ⊕ {e : M.Edge // M.dst e = q}) =
    (Finset.univ.filter fun e : M.Edge => M.src e = q).card +
      (Finset.univ.filter fun e : M.Edge => M.dst e = q).card
  calc
    Fintype.card
        ({e : M.Edge // M.src e = q} ⊕ {e : M.Edge // M.dst e = q}) =
        Fintype.card {e : M.Edge // M.src e = q} +
          Fintype.card {e : M.Edge // M.dst e = q} := Fintype.card_sum
    _ = (Finset.univ.filter fun e : M.Edge => M.src e = q).card +
          Fintype.card {e : M.Edge // M.dst e = q} := by
      rw [Fintype.card_of_subtype (Finset.univ.filter fun e : M.Edge => M.src e = q)
        (by intro e; simp)]
    _ = (Finset.univ.filter fun e : M.Edge => M.src e = q).card +
          (Finset.univ.filter fun e : M.Edge => M.dst e = q).card := by
      rw [Fintype.card_of_subtype (Finset.univ.filter fun e : M.Edge => M.dst e = q)
        (by intro e; simp)]

/-- In a physical simple graph, incidence-label cardinality is the graph
degree. -/
theorem physicalIncidences_card
    (G : PhysicalGraph) (v : G.Vertex) :
    Fintype.card (physicalIncidences G v) = G.degree v := by
  classical
  let e : physicalIncidences G v ≃ {p : G.Edge // p ∈ incidentEdges G v} := {
    toFun := fun p => ⟨p.1, by simp [incidentEdges, p.2]⟩
    invFun := fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩
    left_inv := by intro p; apply Subtype.ext; rfl
    right_inv := by intro p; apply Subtype.ext; rfl }
  calc
    Fintype.card (physicalIncidences G v) =
        Fintype.card {p : G.Edge // p ∈ incidentEdges G v} := Fintype.card_congr e
    _ = (incidentEdges G v).card := Fintype.card_coe _
    _ = G.degree v := by
      unfold PhysicalGraph.degree PhysicalGraph.selectedDegree incidentEdges
      simp

/-- Exact degree preservation reduces to a bijection from auxiliary endpoint
slots to physical edges incident to the represented vertex. A corridor
partition supplies the intended map when each incident edge is owned by one
corridor and can occur only at that corridor's first or last step. -/
theorem ambientDegree_eq_physical_degree_of_endpointIncidenceEquiv
    (M : FiniteMultiGraph) (G : PhysicalGraph)
    (vertexMap : M.Vertex → G.Vertex) (q : M.Vertex)
    (hinc : endpointIncidences M q ≃ physicalIncidences G (vertexMap q)) :
    ambientDegree M q = G.degree (vertexMap q) := by
  calc
    ambientDegree M q = Fintype.card (endpointIncidences M q) :=
      (endpointIncidences_card M q).symm
    _ = Fintype.card (physicalIncidences G (vertexMap q)) := Fintype.card_congr hinc
    _ = G.degree (vertexMap q) := physicalIncidences_card G (vertexMap q)

/-- The first recorded corridor edge. -/
def corridorFirstEdge {G : PhysicalGraph} (C : PhysicalCorridor G)
    (hne : C.edges ≠ []) : G.Edge := C.edges.get ⟨0, by
  have hlen := C.vertices_length
  cases h : C.edges with
  | nil => exact (hne h).elim
  | cons e es => simp [h] at hlen ⊢
  ⟩

/-- The last recorded corridor edge. -/
def corridorLastEdge {G : PhysicalGraph} (C : PhysicalCorridor G)
    (hne : C.edges ≠ []) : G.Edge := C.edges.get ⟨C.edges.length - 1, by
  have hlen := C.vertices_length
  have hpos : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hne
  omega
  ⟩

private theorem corridorStart_eq_firstVertex {G : PhysicalGraph}
    (C : PhysicalCorridor G) :
    corridorStart C = C.vertices.get ⟨0, by
      have h := C.vertices_length
      omega⟩ := by
  simp [corridorStart, List.head_eq_getElem_zero]

private theorem corridorFinish_eq_lastVertex {G : PhysicalGraph}
    (C : PhysicalCorridor G) :
    corridorFinish C = C.vertices.get ⟨C.edges.length, by
      have h := C.vertices_length
      omega⟩ := by
  simp [corridorFinish, List.getLast_eq_getElem, C.vertices_length]

/-- If an edge of a corridor is incident to a retained vertex, it must be the
first or last edge of that corridor. Every internal vertex is outside P₀ and
has degree two, while a retained vertex belongs to P₀ or has degree three. -/
theorem incident_owned_corridor_edge_is_terminal
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W) (Q : Finset G.Vertex)
    (hQ : ∀ v, v ∈ Q → v ∈ P₀ ∨ G.degree v = 3)
    {C : PhysicalCorridor G} (hC : C ∈ D.corridors)
    (hne : C.edges ≠ []) {p : G.Edge} (hp : p ∈ C.support)
    {q : G.Vertex} (hq : q ∈ Q) (hinc : G.incident p q) :
    (p = corridorFirstEdge C hne ∧ corridorStart C = q) ∨
      (p = corridorLastEdge C hne ∧ corridorFinish C = q) := by
  classical
  have hpList : p ∈ C.edges := List.mem_toFinset.mp hp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpList
  have hstep := C.step i
  have hpos : C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩ = q ∨
      C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩ = q := by
    rcases hstep with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · rcases hinc with hpq | hpq
      · left
        calc
          C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩ = G.src p := by
            rw [← hi]
            exact hs.symm
          _ = q := hpq
      · right
        calc
          C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩ = G.dst p := by
            rw [← hi]
            exact ht.symm
          _ = q := hpq
    · rcases hinc with hpq | hpq
      · right
        calc
          C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩ = G.src p := by
            rw [← hi]
            exact hs.symm
          _ = q := hpq
      · left
        calc
          C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩ = G.dst p := by
            rw [← hi]
            exact ht.symm
          _ = q := hpq
  have hlen := C.vertices_length
  have hi_lt : i.val < C.edges.length := i.isLt
  rcases hpos with hleft | hright
  · by_cases hi0 : i.val = 0
    · left
      have heq : p = corridorFirstEdge C hne := by
        calc
          p = C.edges.get i := hi.symm
          _ = C.edges.get ⟨0, by
              have hp0 : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hne
              omega⟩ := by
            apply (List.Nodup.get_inj_iff C.edges_nodup).mpr
            exact Fin.ext hi0
          _ = corridorFirstEdge C hne := rfl
      refine ⟨heq, ?_⟩
      rw [corridorStart_eq_firstVertex]
      simpa [hi0] using hleft
    · have hiPos : 0 < i.val := by omega
      have hiEnd : i.val < C.edges.length := i.isLt
      have hidx : i.val - 1 < C.vertices.length - 2 := by omega
      have hinternal := D.internal_unprotected_degree_two C hC ⟨i.val - 1, hidx⟩
      have hvertex : C.vertices.get ⟨(i.val - 1) + 1, by
          rw [C.vertices_length]; omega⟩ = q := by
        simpa only [show i.val - 1 + 1 = i.val by omega] using hleft
      rcases hQ q hq with hqP | hq3
      · have hvP : C.vertices.get ⟨(i.val - 1) + 1, by
            rw [C.vertices_length]; omega⟩ ∈ P₀ := by
          rw [hvertex]
          exact hqP
        exact (hinternal.1 hvP).elim
      · have hq2 : G.degree q = 2 := by
          rw [← hvertex]
          exact hinternal.2
        omega
  · by_cases hiLast : i.val + 1 = C.edges.length
    · right
      have heq : p = corridorLastEdge C hne := by
        calc
          p = C.edges.get i := hi.symm
          _ = C.edges.get ⟨C.edges.length - 1, by
              have hp0 : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hne
              omega⟩ := by
            apply (List.Nodup.get_inj_iff C.edges_nodup).mpr
            apply Fin.ext
            have hlast : i.val = C.edges.length - 1 := by omega
            exact hlast
          _ = corridorLastEdge C hne := rfl
      refine ⟨heq, ?_⟩
      rw [corridorFinish_eq_lastVertex]
      simpa [hiLast] using hright
    · have hiEnd : i.val + 1 < C.edges.length := by omega
      have hiPos : 0 < i.val + 1 := by omega
      have hidx : i.val < C.vertices.length - 2 := by omega
      have hinternal := D.internal_unprotected_degree_two C hC ⟨i.val, hidx⟩
      have hvertex : C.vertices.get ⟨i.val + 1, by
          rw [C.vertices_length]; omega⟩ = q := hright
      rcases hQ q hq with hqP | hq3
      · have hvP : C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩ ∈ P₀ := by
          rw [hvertex]
          exact hqP
        exact (hinternal.1 hvP).elim
      · have hq2 : G.degree q = 2 := hvertex ▸ hinternal.2
        omega
theorem corridorFirstEdge_eq_head {G : PhysicalGraph}
    (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    corridorFirstEdge C hne = C.edges.head hne := by
  unfold corridorFirstEdge
  exact (List.head_eq_getElem_zero hne).symm

theorem corridorLastEdge_eq_getLast {G : PhysicalGraph}
    (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    corridorLastEdge C hne = C.edges.getLast hne := by
  unfold corridorLastEdge
  simpa using (List.getLast_eq_getElem hne).symm

theorem corridor_first_eq_last_length_one {G : PhysicalGraph}
    (C : PhysicalCorridor G) (hne : C.edges ≠ [])
    (heq : corridorFirstEdge C hne = corridorLastEdge C hne) :
    C.edges.length = 1 := by
  have hget : C.edges.get ⟨0, by
      have hp := List.length_pos_iff_ne_nil.mpr hne
      omega⟩ = C.edges.get ⟨C.edges.length - 1, by
      have hp := List.length_pos_iff_ne_nil.mpr hne
      omega⟩ := by
    calc
      C.edges.get ⟨0, by
          have hp := List.length_pos_iff_ne_nil.mpr hne
          omega⟩ = corridorFirstEdge C hne := rfl
      _ = corridorLastEdge C hne := heq
      _ = C.edges.get ⟨C.edges.length - 1, by
          have hp := List.length_pos_iff_ne_nil.mpr hne
          omega⟩ := rfl
  have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp hget
  have hval : 0 = C.edges.length - 1 := by
    simpa using congrArg Fin.val hidx
  have hpos : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hne
  omega

theorem corridor_start_ne_finish_of_length_one {G : PhysicalGraph}
    (C : PhysicalCorridor G) (hlen : C.edges.length = 1) :
    corridorStart C ≠ corridorFinish C := by
  intro heq
  have hi : 0 < C.edges.length := by omega
  have hstep := C.step ⟨0, hi⟩
  have hstart := corridorStart_eq_firstVertex C
  have hfinish := corridorFinish_eq_lastVertex C
  rcases hstep with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · apply G.noLoops (C.edges.get ⟨0, hi⟩)
    have hlast : C.vertices.get ⟨C.edges.length, by
        rw [C.vertices_length]; omega⟩ =
        C.vertices.get ⟨1, by rw [C.vertices_length, hlen]; omega⟩ := by
      apply congrArg C.vertices.get
      apply Fin.ext
      exact hlen
    have hdst : corridorFinish C = G.dst (C.edges.get ⟨0, hi⟩) := by
      calc
        corridorFinish C = C.vertices.get ⟨C.edges.length, by
            rw [C.vertices_length]; omega⟩ := corridorFinish_eq_lastVertex C
        _ = C.vertices.get ⟨1, by rw [C.vertices_length, hlen]; omega⟩ := hlast
        _ = G.dst (C.edges.get ⟨0, hi⟩) := by simpa using ht.symm
    calc
      G.src (C.edges.get ⟨0, hi⟩) = corridorStart C := hs.trans hstart.symm
      _ = corridorFinish C := heq
      _ = G.dst (C.edges.get ⟨0, hi⟩) := hdst
  · apply G.noLoops (C.edges.get ⟨0, hi⟩)
    have hlast : C.vertices.get ⟨1, by
        rw [C.vertices_length, hlen]; omega⟩ =
        C.vertices.get ⟨C.edges.length, by
          rw [C.vertices_length]; omega⟩ := by
      apply congrArg C.vertices.get
      apply Fin.ext
      exact hlen.symm
    have hsrc : G.src (C.edges.get ⟨0, hi⟩) = corridorFinish C := by
      calc
        G.src (C.edges.get ⟨0, hi⟩) = C.vertices.get ⟨1, by
            rw [C.vertices_length, hlen]; omega⟩ := hs
        _ = C.vertices.get ⟨C.edges.length, by
            rw [C.vertices_length]; omega⟩ := hlast
        _ = corridorFinish C := (corridorFinish_eq_lastVertex C).symm
    calc
      G.src (C.edges.get ⟨0, hi⟩) = corridorFinish C := hsrc
      _ = corridorStart C := heq.symm
      _ = G.dst (C.edges.get ⟨0, hi⟩) := hstart.trans ht.symm

/-- Convert an auxiliary endpoint slot to the physical edge at that corridor
end: source slots use the first edge and target slots use the last edge. -/
def corridorEndpointSlotEdge
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex}
    (i : endpointIncidences (compressedCorridorGraph D hendpoints) q) : G.Edge :=
  match i with
  | Sum.inl a =>
      let C := corridorAt D a.1
      corridorFirstEdge C (hnonempty C (corridorAt_mem D a.1))
  | Sum.inr a =>
      let C := corridorAt D a.1
      corridorLastEdge C (hnonempty C (corridorAt_mem D a.1))

def corridorEndpointSlotIndex
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex}
    (i : endpointIncidences (compressedCorridorGraph D hendpoints) q) :
    Fin (corridorFamily D).length :=
  match i with
  | Sum.inl a => a.1
  | Sum.inr a => a.1

theorem corridorEndpointSlotEdge_mem_support
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex}
    (i : endpointIncidences (compressedCorridorGraph D hendpoints) q) :
    corridorEndpointSlotEdge D hnonempty hendpoints i ∈
      (corridorAt D (corridorEndpointSlotIndex D hendpoints i)).support := by
  cases i with
  | inl a =>
      change corridorFirstEdge (corridorAt D a.1)
        (hnonempty _ (corridorAt_mem D a.1)) ∈ (corridorAt D a.1).support
      rw [PhysicalCorridor.support]
      apply List.mem_toFinset.mpr
      rw [corridorFirstEdge_eq_head]
      exact List.head_mem _
  | inr a =>
      change corridorLastEdge (corridorAt D a.1)
        (hnonempty _ (corridorAt_mem D a.1)) ∈ (corridorAt D a.1).support
      rw [PhysicalCorridor.support]
      apply List.mem_toFinset.mpr
      rw [corridorLastEdge_eq_getLast]
      exact List.getLast_mem _

private theorem corridorAt_injective {G : PhysicalGraph} {P₀ : Finset G.Vertex}
    {W : Finset G.Edge} (D : CorridorPartition G P₀ W) :
    Function.Injective (corridorAt D) := by
  classical
  intro e f hef
  have hget : Function.Injective (corridorFamily D).get :=
    (List.nodup_iff_injective_get).mp (Finset.nodup_toList D.corridors.toFinset)
  exact hget hef

private theorem corridorAt_eq_of_shared_edges
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    {e f : Fin (corridorFamily D).length} {p : G.Edge}
    (hp : p ∈ (corridorAt D e).support)
    (hf : p ∈ (corridorAt D f).support) :
    corridorAt D e = corridorAt D f := by
  classical
  by_contra hne
  have hdisj := D.edge_disjoint (corridorAt D e) (corridorAt_mem D e)
    (corridorAt D f) (corridorAt_mem D f) hne
  exact (Finset.disjoint_left.mp hdisj) hp hf

/-- Endpoint labels at one auxiliary vertex map injectively to physical edge
labels. Across corridors, edge-disjointness separates the labels. If both
ends of one corridor meet at q, its first and last edge labels still differ:
otherwise nodup makes it a one-edge corridor, whose endpoints cannot agree
because physical edges have no loops. -/
theorem corridorEndpointSlotEdge_injective
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex} :
    Function.Injective (corridorEndpointSlotEdge D hnonempty hendpoints
      (q := q)) := by
  intro i j hij
  cases i with
  | inl a =>
    cases j with
    | inl b =>
        have ha : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inl a) ∈
            (corridorAt D a.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inl a)
        have hb : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inl b) ∈
            (corridorAt D b.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inl b)
        have hcorr := corridorAt_eq_of_shared_edges D ha (by rw [hij]; exact hb)
        have hab : a.1 = b.1 := corridorAt_injective D hcorr
        apply congrArg Sum.inl
        exact Subtype.ext hab
    | inr b =>
        have ha : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inl a) ∈
            (corridorAt D a.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inl a)
        have hb : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inr b) ∈
            (corridorAt D b.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inr b)
        have hcorr := corridorAt_eq_of_shared_edges D ha (by rw [hij]; exact hb)
        have hab : a.1 = b.1 := corridorAt_injective D hcorr
        have hfirstlast : corridorFirstEdge (corridorAt D a.1)
            (hnonempty _ (corridorAt_mem D a.1)) =
            corridorLastEdge (corridorAt D a.1)
              (hnonempty _ (corridorAt_mem D a.1)) := by
          change corridorFirstEdge (corridorAt D a.1)
              (hnonempty _ (corridorAt_mem D a.1)) =
            corridorLastEdge (corridorAt D b.1)
              (hnonempty _ (corridorAt_mem D b.1)) at hij
          rw [← hab] at hij
          exact hij
        have hstart : corridorStart (corridorAt D a.1) =
            compressedCorridorVertexMap D hendpoints q := by
          calc
            corridorStart (corridorAt D a.1) =
                compressedCorridorVertexMap D hendpoints
                  ((compressedCorridorGraph D hendpoints).src a.1) := by simp
            _ = compressedCorridorVertexMap D hendpoints q :=
              congrArg (compressedCorridorVertexMap D hendpoints) a.2
        have hfinish : corridorFinish (corridorAt D a.1) =
            compressedCorridorVertexMap D hendpoints q := by
          calc
            corridorFinish (corridorAt D a.1) =
                corridorFinish (corridorAt D b.1) := by rw [hab]
            _ = compressedCorridorVertexMap D hendpoints
                  ((compressedCorridorGraph D hendpoints).dst b.1) := by simp
            _ = compressedCorridorVertexMap D hendpoints q :=
              congrArg (compressedCorridorVertexMap D hendpoints) b.2
        have hclosed : corridorStart (corridorAt D a.1) =
            corridorFinish (corridorAt D a.1) := hstart.trans hfinish.symm
        have hlen := corridor_first_eq_last_length_one _
          (hnonempty _ (corridorAt_mem D a.1)) hfirstlast
        exact (corridor_start_ne_finish_of_length_one _ hlen hclosed).elim
  | inr a =>
    cases j with
    | inl b =>
        have hb : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inl b) ∈
            (corridorAt D b.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inl b)
        have ha : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inr a) ∈
            (corridorAt D a.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inr a)
        have hcorr := corridorAt_eq_of_shared_edges D hb (by rw [hij.symm]; exact ha)
        have hba : b.1 = a.1 := corridorAt_injective D hcorr
        have hfirstlast : corridorFirstEdge (corridorAt D b.1)
            (hnonempty _ (corridorAt_mem D b.1)) =
            corridorLastEdge (corridorAt D b.1)
              (hnonempty _ (corridorAt_mem D b.1)) := by
          have hij' := hij.symm
          change corridorFirstEdge (corridorAt D b.1)
              (hnonempty _ (corridorAt_mem D b.1)) =
            corridorLastEdge (corridorAt D a.1)
              (hnonempty _ (corridorAt_mem D a.1)) at hij'
          rw [← hba] at hij'
          exact hij'
        have hstart : corridorStart (corridorAt D b.1) =
            compressedCorridorVertexMap D hendpoints q := by
          calc
            corridorStart (corridorAt D b.1) =
                compressedCorridorVertexMap D hendpoints
                  ((compressedCorridorGraph D hendpoints).src b.1) := by simp
            _ = compressedCorridorVertexMap D hendpoints q :=
              congrArg (compressedCorridorVertexMap D hendpoints) b.2
        have hfinish : corridorFinish (corridorAt D b.1) =
            compressedCorridorVertexMap D hendpoints q := by
          calc
            corridorFinish (corridorAt D b.1) =
                corridorFinish (corridorAt D a.1) := by rw [hba]
            _ = compressedCorridorVertexMap D hendpoints
                  ((compressedCorridorGraph D hendpoints).dst a.1) := by simp
            _ = compressedCorridorVertexMap D hendpoints q :=
              congrArg (compressedCorridorVertexMap D hendpoints) a.2
        have hclosed : corridorStart (corridorAt D b.1) =
            corridorFinish (corridorAt D b.1) := hstart.trans hfinish.symm
        have hlen := corridor_first_eq_last_length_one _
          (hnonempty _ (corridorAt_mem D b.1)) hfirstlast
        exact (corridor_start_ne_finish_of_length_one _ hlen hclosed).elim
    | inr b =>
        have ha : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inr a) ∈
            (corridorAt D a.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inr a)
        have hb : corridorEndpointSlotEdge D hnonempty hendpoints (Sum.inr b) ∈
            (corridorAt D b.1).support :=
          corridorEndpointSlotEdge_mem_support D hnonempty hendpoints (Sum.inr b)
        have hcorr := corridorAt_eq_of_shared_edges D ha (by rw [hij]; exact hb)
        have hab : a.1 = b.1 := corridorAt_injective D hcorr
        apply congrArg Sum.inr
        exact Subtype.ext hab

theorem corridorEndpointSlotEdge_incident
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex}
    (i : endpointIncidences (compressedCorridorGraph D hendpoints) q) :
    G.incident (corridorEndpointSlotEdge D hnonempty hendpoints i)
      (compressedCorridorVertexMap D hendpoints q) := by
  cases i with
  | inl a =>
      have hv : corridorStart (corridorAt D a.1) =
          compressedCorridorVertexMap D hendpoints q := by
        calc
          corridorStart (corridorAt D a.1) =
              compressedCorridorVertexMap D hendpoints
                ((compressedCorridorGraph D hendpoints).src a.1) := by simp
          _ = compressedCorridorVertexMap D hendpoints q :=
            congrArg (compressedCorridorVertexMap D hendpoints) a.2
      change G.incident (corridorFirstEdge (corridorAt D a.1)
        (hnonempty _ (corridorAt_mem D a.1)))
        (compressedCorridorVertexMap D hendpoints q)
      rw [corridorFirstEdge_eq_head, ← hv]
      exact corridor_first_edge_incident _ (hnonempty _ (corridorAt_mem D a.1))
  | inr a =>
      have hv : corridorFinish (corridorAt D a.1) =
          compressedCorridorVertexMap D hendpoints q := by
        calc
          corridorFinish (corridorAt D a.1) =
              compressedCorridorVertexMap D hendpoints
                ((compressedCorridorGraph D hendpoints).dst a.1) := by simp
          _ = compressedCorridorVertexMap D hendpoints q :=
            congrArg (compressedCorridorVertexMap D hendpoints) a.2
      change G.incident (corridorLastEdge (corridorAt D a.1)
        (hnonempty _ (corridorAt_mem D a.1)))
        (compressedCorridorVertexMap D hendpoints q)
      rw [corridorLastEdge_eq_getLast, ← hv]
      exact corridor_last_edge_incident _ (hnonempty _ (corridorAt_mem D a.1))

/-- Every physical edge incident to the represented retained vertex is one of
the endpoint-slot edges. Edge coverage chooses its unique owning corridor;
the internal degree-two condition forces the incidence to its first or last
step, and the corresponding indexed endpoint slot is then obtained by the
compressed vertex map. -/
theorem incident_edge_has_endpoint_slot
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    {q : (compressedCorridorGraph D hendpoints).Vertex}
    {p : G.Edge}
    (hp : G.incident p (compressedCorridorVertexMap D hendpoints q)) :
    ∃ i : endpointIncidences (compressedCorridorGraph D hendpoints) q,
      corridorEndpointSlotEdge D hnonempty hendpoints i = p := by
  classical
  obtain ⟨C, hC, hpC⟩ := D.edge_cover p
  have hCne := hnonempty C hC
  have hterminal := incident_owned_corridor_edge_is_terminal D
    (protectedOrBranch G P₀)
    (by
      intro v hv
      simpa [protectedOrBranch] using hv)
    hC hCne hpC (retainedVertexEquiv (G := G) (P₀ := P₀) q).2 hp
  have hmemFamily : C ∈ corridorFamily D := by
    change C ∈ D.corridors.toFinset.toList
    exact Finset.mem_toList.mpr (List.mem_toFinset.mpr hC)
  obtain ⟨a, he⟩ := List.mem_iff_get.mp hmemFamily
  have hCa : corridorAt D a = C := he
  rcases hterminal with ⟨hfirst, hstart⟩ | ⟨hlast, hfinish⟩
  · let i : endpointIncidences (compressedCorridorGraph D hendpoints) q :=
      Sum.inl ⟨a, by
        apply (compressedCorridorVertexMap_injective D hendpoints)
        calc
          compressedCorridorVertexMap D hendpoints
              ((compressedCorridorGraph D hendpoints).src a) =
              corridorStart (corridorAt D a) := by simp
          _ = corridorStart C := by rw [hCa]
          _ = compressedCorridorVertexMap D hendpoints q := by
            rw [hstart]
            rfl⟩
    refine ⟨i, ?_⟩
    have hfirstAt : corridorFirstEdge (corridorAt D a)
        (hnonempty (corridorAt D a) (corridorAt_mem D a)) =
          corridorFirstEdge C hCne := by
      simpa [hCa]
    exact hfirstAt.trans hfirst.symm
  · let i : endpointIncidences (compressedCorridorGraph D hendpoints) q :=
      Sum.inr ⟨a, by
        apply (compressedCorridorVertexMap_injective D hendpoints)
        calc
          compressedCorridorVertexMap D hendpoints
              ((compressedCorridorGraph D hendpoints).dst a) =
              corridorFinish (corridorAt D a) := by simp
          _ = corridorFinish C := by rw [hCa]
          _ = compressedCorridorVertexMap D hendpoints q := by
            rw [hfinish]
            rfl⟩
    refine ⟨i, ?_⟩
    have hlastAt : corridorLastEdge (corridorAt D a)
        (hnonempty (corridorAt D a) (corridorAt_mem D a)) =
          corridorLastEdge C hCne := by
      simpa [hCa]
    exact hlastAt.trans hlast.symm

def corridorEndpointIncidenceMap
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    (q : (compressedCorridorGraph D hendpoints).Vertex) :
    endpointIncidences (compressedCorridorGraph D hendpoints) q ≃
      physicalIncidences G (compressedCorridorVertexMap D hendpoints q) := by
  classical
  let f : endpointIncidences (compressedCorridorGraph D hendpoints) q →
      physicalIncidences G (compressedCorridorVertexMap D hendpoints q) := fun i =>
    ⟨corridorEndpointSlotEdge D hnonempty hendpoints i,
      corridorEndpointSlotEdge_incident D hnonempty hendpoints i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply corridorEndpointSlotEdge_injective D hnonempty hendpoints
      exact congrArg Subtype.val hij
    · intro p
      obtain ⟨i, hi⟩ := incident_edge_has_endpoint_slot D hnonempty hendpoints p.2
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
  exact Equiv.ofBijective f hf

theorem compressedCorridor_ambientDegree_eq_physical_degree
    {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P₀ W)
    (hnonempty : ∀ C ∈ D.corridors, C.edges ≠ [])
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
        corridorFinish C ∈ protectedOrBranch G P₀)
    (q : (compressedCorridorGraph D hendpoints).Vertex) :
    ambientDegree (compressedCorridorGraph D hendpoints) q =
      G.degree (compressedCorridorVertexMap D hendpoints q) :=
  ambientDegree_eq_physical_degree_of_endpointIncidenceEquiv
    (compressedCorridorGraph D hendpoints) G
    (compressedCorridorVertexMap D hendpoints) q
    (corridorEndpointIncidenceMap D hnonempty hendpoints q)




end Erdos1016.Proof.EndpointIncidenceBijection

end

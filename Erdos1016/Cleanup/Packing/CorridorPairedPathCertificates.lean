import Erdos1016.Cleanup.Packing.PairedPathRegions
import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

/-!
# From paired physical corridors to paired path certificates

This is the deterministic bridge between two route corridors with a common
pair of distinct ends and the region certificate used by the packing theorem.
The corridor hypotheses state the path facts forced by a degree-two corridor
decomposition: distinct vertices on each route, disjoint route interiors,
and coverage of the region.
-/

noncomputable section

namespace Erdos1016.Proof.CorridorPairedPathCertificates

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.PairedPathRegions
open Erdos1016.Proof.CleanupSpecification
open SimpleGraph

variable {G : PhysicalGraph}

/-- Canonical physical vertex region traced by two corridor routes. -/
def pairedRouteRegion (C₁ C₂ : PhysicalCorridor G) : Finset G.Vertex :=
  C₁.vertices.toFinset ∪ C₂.vertices.toFinset

def corridorStart (C : PhysicalCorridor G) : G.Vertex :=
  C.vertices.head (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))

def corridorFinish (C : PhysicalCorridor G) : G.Vertex :=
  C.vertices.getLast (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))

theorem corridorStart_head? (C : PhysicalCorridor G) :
    C.vertices.head? = some (corridorStart C) := by
  exact (List.head_eq_iff_head?_eq_some
    (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))).1 rfl

theorem corridorFinish_getLast? (C : PhysicalCorridor G) :
    C.vertices.getLast? = some (corridorFinish C) := by
  exact List.getLast?_eq_getLast_of_ne_nil
    (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))





/-- The endpoint list of a corridor gives a simple-graph walk. -/
private theorem corridor_walk_aux (G : PhysicalGraph) :
    ∀ (es : List G.Edge) (vs : List G.Vertex),
      (hlen : vs.length = es.length + 1) →
      (∀ i : Fin es.length,
        let e := es.get ⟨i.val, i.isLt⟩
        let u := vs.get ⟨i.val, by rw [hlen]; omega⟩
        let v := vs.get ⟨i.val + 1, by rw [hlen]; omega⟩
        (G.src e = u ∧ G.dst e = v) ∨ (G.dst e = u ∧ G.src e = v)) →
      ∃ p : G.toSimpleGraph.Walk (vs.head (List.length_pos_iff_ne_nil.mp (by rw [hlen]; omega)))
        (vs.getLast (List.length_pos_iff_ne_nil.mp (by rw [hlen]; omega))),
        p.support = vs ∧
          List.map (fun e : G.Edge => s(G.src e, G.dst e)) es = p.edges := by
  intro es
  induction es with
  | nil =>
      intro vs hlen hstep
      cases vs with
      | nil => simp at hlen
      | cons u vs =>
          cases vs with
          | nil => exact ⟨.nil, by simp, by simp⟩
          | cons v vs => simp at hlen
  | cons e es ih =>
      intro vs hlen hstep
      cases vs with
      | nil => simp at hlen
      | cons u vs =>
          cases vs with
          | nil => simp at hlen
          | cons v vs =>
              have htailLen : (v :: vs).length = es.length + 1 := by
                have hh : vs.length + 2 = es.length + 2 := by
                  simpa only [List.length_cons] using hlen
                have hh' : vs.length = es.length := by omega
                simp [hh']
              have hfirst := hstep ⟨0, by simp⟩
              change (G.src e = u ∧ G.dst e = v) ∨
                (G.dst e = u ∧ G.src e = v) at hfirst
              have hadj : G.toSimpleGraph.Adj u v := by
                rcases hfirst with h | h
                · exact ⟨e, one_ne_zero, Or.inl h⟩
                · exact ⟨e, one_ne_zero, Or.inr ⟨h.2, h.1⟩⟩
              have htail : ∀ i : Fin es.length,
                  let e' := es.get ⟨i.val, i.isLt⟩
                  let u' := (v :: vs).get ⟨i.val, by rw [htailLen]; omega⟩
                  let v' := (v :: vs).get ⟨i.val + 1, by rw [htailLen]; omega⟩
                  (G.src e' = u' ∧ G.dst e' = v') ∨
                    (G.dst e' = u' ∧ G.src e' = v') := by
                intro i
                have hi : i.val + 1 < (e :: es).length := by
                  rw [List.length_cons]
                  omega
                have h := hstep ⟨i.val + 1, hi⟩
                simpa only [List.get_cons_succ, Fin.val_mk] using h
              obtain ⟨q, hq, heq⟩ := ih (v :: vs) htailLen htail
              refine ⟨Walk.cons hadj q, ?_, ?_⟩
              · simp [Walk.support_cons, hq]
              · simp only [List.map_cons, Walk.edges_cons]
                rcases hfirst with h | h
                · rw [Sym2.eq_iff.mpr (Or.inl h)]
                  exact congrArg (List.cons s(u, v)) heq
                · rw [Sym2.eq_iff.mpr (Or.inr ⟨h.2, h.1⟩)]
                  exact congrArg (List.cons s(u, v)) heq

/-- Convert a physical corridor record into a graph walk, with exactly its
recorded vertex list as support. -/
theorem toWalk (C : PhysicalCorridor G) :
    ∃ p : G.toSimpleGraph.Walk
      (C.vertices.head (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)))
      (C.vertices.getLast (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))),
      p.support = C.vertices ∧
        List.map (fun e : G.Edge => s(G.src e, G.dst e)) C.edges = p.edges := by
  exact corridor_walk_aux G C.edges C.vertices C.vertices_length C.step

/-- Any ambient walk whose vertices all lie in `U` has a unique natural
realization as a walk in the induced subtype graph. The mapped support is
exactly the original support, so simplicity and support disjointness transfer
without further graph arguments. -/
theorem liftWalkToInduce {U : Finset G.Vertex} {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v)
    (hU : ∀ x ∈ p.support, x ∈ U) :
    ∃ q : (G.toSimpleGraph.induce (U : Set G.Vertex)).Walk
      ⟨u, hU u (Walk.start_mem_support p)⟩
      ⟨v, hU v (Walk.end_mem_support p)⟩,
      List.map Subtype.val q.support = p.support ∧
        List.map (Sym2.map Subtype.val) q.edges = p.edges := by
  induction p with
  | nil =>
      exact ⟨Walk.nil, rfl, rfl⟩
  | @cons a b c hab p ih =>
      have ha : a ∈ U := hU a (by simp)
      have hb : b ∈ U := hU b (by simp)
      have hc : c ∈ U := hU c (by simp)
      have htail : ∀ x ∈ p.support, x ∈ U := by
        intro x hx
        exact hU x (by simp [hx])
      obtain ⟨q, hq, heq⟩ := ih htail
      let x : {z : G.Vertex // z ∈ U} := ⟨a, ha⟩
      let y : {z : G.Vertex // z ∈ U} := ⟨b, hb⟩
      have hab' : (G.toSimpleGraph.induce (U : Set G.Vertex)).Adj x y := hab
      refine ⟨Walk.cons hab' q, ?_⟩
      constructor
      · simp only [Walk.support_cons, List.map_cons, Subtype.coe_mk]
        simpa [Walk.support_cons] using congrArg (List.cons b) hq
      · simp only [Walk.edges_cons, List.map_cons, Sym2.map_pair_eq]
        simpa [x, y] using congrArg (List.cons s(b, c)) heq

/-- Two simple ambient routes with common distinct endpoints, disjoint
interiors and edges, and full coverage of `U` produce the paired-path
certificate in the induced region. This packages the subtype lifting needed
after the route-to-walk step. -/
noncomputable def pairedCertificate_of_ambientPaths
    {U : Finset G.Vertex} {s t : G.Vertex}
    (hs : s ∈ U) (ht : t ∈ U) (hst : s ≠ t)
    (p₁ p₂ : G.toSimpleGraph.Walk s t)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hU₁ : ∀ x ∈ p₁.support, x ∈ U)
    (hU₂ : ∀ x ∈ p₂.support, x ∈ U)
    (hint : Disjoint p₁.support.tail.toFinset p₂.reverse.support.tail.toFinset)
    (hedge : Disjoint p₁.edges.toFinset p₂.edges.toFinset)
    (hcover : ∀ x ∈ U, x ∈ p₁.support ∨ x ∈ p₂.support) :
    PairedPathCertificate G U := by
  classical
  let q₁ := Classical.choose (liftWalkToInduce p₁ hU₁)
  have hq₁ := (Classical.choose_spec (liftWalkToInduce p₁ hU₁)).1
  have he₁ := (Classical.choose_spec (liftWalkToInduce p₁ hU₁)).2
  let q₂ := Classical.choose (liftWalkToInduce p₂ hU₂)
  have hq₂ := (Classical.choose_spec (liftWalkToInduce p₂ hU₂)).1
  have he₂ := (Classical.choose_spec (liftWalkToInduce p₂ hU₂)).2
  let source : {x : G.Vertex // x ∈ U} := ⟨s, hs⟩
  let target : {x : G.Vertex // x ∈ U} := ⟨t, ht⟩
  let P : PairedPathCertificate G U := {
    source := source
    target := target
    endpoints_ne := hst
    path₁ := q₁
    path₂ := q₂
    path₁_simple := by
      rw [Walk.isPath_def]
      exact (List.nodup_map_iff Subtype.val_injective).mp (by
        rw [hq₁]
        exact hp₁.support_nodup)
    path₂_simple := by
      rw [Walk.isPath_def]
      exact (List.nodup_map_iff Subtype.val_injective).mp (by
        rw [hq₂]
        exact hp₂.support_nodup)
    interiors_disjoint := by
      apply Finset.disjoint_left.mpr
      intro w hw₁ hw₂
      have htail₁ : List.map Subtype.val q₁.support.tail = p₁.support.tail := by
        simpa only [List.map_tail] using congrArg List.tail hq₁
      have hrev₂ : List.map Subtype.val q₂.reverse.support = p₂.reverse.support := by
        rw [Walk.support_reverse, List.map_reverse, hq₂, Walk.support_reverse]
      have htail₂ : List.map Subtype.val q₂.reverse.support.tail =
          p₂.reverse.support.tail := by
        simpa only [List.map_tail] using congrArg List.tail hrev₂
      have hmap₁ : (w : G.Vertex) ∈ p₁.support.tail := by
        have hw : w ∈ q₁.support.tail := List.mem_toFinset.mp hw₁
        have hm : (w : G.Vertex) ∈ List.map Subtype.val q₁.support.tail :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        rw [htail₁] at hm
        exact hm
      have hmap₂ : (w : G.Vertex) ∈ p₂.reverse.support.tail := by
        have hw : w ∈ q₂.reverse.support.tail := List.mem_toFinset.mp hw₂
        have hm : (w : G.Vertex) ∈ List.map Subtype.val q₂.reverse.support.tail :=
          List.mem_map.mpr ⟨w, hw, rfl⟩
        rw [htail₂] at hm
        exact hm
      exact (Finset.disjoint_left.mp hint) (List.mem_toFinset.mpr hmap₁)
        (List.mem_toFinset.mpr hmap₂)
    edges_disjoint := by
      apply Finset.disjoint_left.mpr
      intro e he₁' he₂'
      have hm₁ : Sym2.map Subtype.val e ∈ p₁.edges := by
        have hm : Sym2.map Subtype.val e ∈ List.map (Sym2.map Subtype.val) q₁.edges :=
          List.mem_map.mpr ⟨e, List.mem_toFinset.mp he₁', rfl⟩
        rw [he₁] at hm
        exact hm
      have hm₂ : Sym2.map Subtype.val e ∈ p₂.edges := by
        have hm : Sym2.map Subtype.val e ∈ List.map (Sym2.map Subtype.val) q₂.edges :=
          List.mem_map.mpr ⟨e, List.mem_toFinset.mp he₂', rfl⟩
        rw [he₂] at hm
        exact hm
      exact (Finset.disjoint_left.mp hedge) (List.mem_toFinset.mpr hm₁)
        (List.mem_toFinset.mpr hm₂)
    covers_region := by
      intro w
      rcases hcover w w.2 with hw | hw
      · have hm : (w : G.Vertex) ∈ List.map Subtype.val q₁.support := by
          rw [hq₁]
          exact hw
        obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hm
        exact Or.inl (Subtype.ext hzw ▸ hz)
      · have hm : (w : G.Vertex) ∈ List.map Subtype.val q₂.support := by
          rw [hq₂]
          exact hw
        obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hm
        exact Or.inr (Subtype.ext hzw ▸ hz)
  }
  exact P

/-- A canonical ambient walk read from a corridor after identifying its two
recorded endpoint entries with `s` and `t`. -/
noncomputable def corridorWalk (C : PhysicalCorridor G) (s t : G.Vertex)
    (hstart : C.vertices.head? = some s)
    (hfinish : C.vertices.getLast? = some t) :
    G.toSimpleGraph.Walk s t := by
  let raw := Classical.choose (toWalk C)
  have hraw := Classical.choose_spec (toWalk C)
  have hne : C.vertices ≠ [] := by
    intro h
    have hlen := C.vertices_length
    simp [h] at hlen
  have hstart' : C.vertices.head
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) = s := by
    exact (List.head_eq_iff_head?_eq_some hne).2 hstart
  have hfinish' : C.vertices.getLast
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) = t := by
    have hh := List.getLast?_eq_getLast_of_ne_nil hne
    rw [hfinish] at hh
    exact Option.some.inj hh.symm
  exact raw.copy hstart' hfinish'

theorem corridorWalk_support (C : PhysicalCorridor G) (s t : G.Vertex)
    (hstart : C.vertices.head? = some s)
    (hfinish : C.vertices.getLast? = some t) :
    (corridorWalk C s t hstart hfinish).support = C.vertices := by
  simpa only [corridorWalk, Walk.support_copy] using
    (Classical.choose_spec (toWalk C)).1

theorem corridorWalk_edgePairs (C : PhysicalCorridor G) (s t : G.Vertex)
    (hstart : C.vertices.head? = some s)
    (hfinish : C.vertices.getLast? = some t) :
    List.map (fun e : G.Edge => s(G.src e, G.dst e)) C.edges =
      (corridorWalk C s t hstart hfinish).edges := by
  simpa only [corridorWalk, Walk.edges_copy] using
    (Classical.choose_spec (toWalk C)).2

/-- Disjoint labels in the simple physical graph give disjoint graph-edge
lists on their corridor walks. The simple-graph hypothesis is what turns
equality of unordered endpoint pairs into equality of physical labels. -/
theorem corridorWalk_edges_disjoint_of_label_disjoint
    (C₁ C₂ : PhysicalCorridor G) (s₁ t₁ s₂ t₂ : G.Vertex)
    (hstart₁ : C₁.vertices.head? = some s₁)
    (hfinish₁ : C₁.vertices.getLast? = some t₁)
    (hstart₂ : C₂.vertices.head? = some s₂)
    (hfinish₂ : C₂.vertices.getLast? = some t₂)
    (hlabels : Disjoint C₁.support C₂.support) :
    Disjoint (corridorWalk C₁ s₁ t₁ hstart₁ hfinish₁).edges.toFinset
      (corridorWalk C₂ s₂ t₂ hstart₂ hfinish₂).edges.toFinset := by
  classical
  let edgePair : G.Edge → Sym2 G.Vertex := fun e => s(G.src e, G.dst e)
  have hinj : Function.Injective edgePair := by
    intro e f hef
    have hend := Sym2.eq_iff.mp hef
    apply G.simple
    rcases hend with hend | hend
    · exact Or.inl hend
    · exact Or.inr hend
  apply Finset.disjoint_left.mpr
  intro x hx₁ hx₂
  have hx₁' : x ∈ (corridorWalk C₁ s₁ t₁ hstart₁ hfinish₁).edges :=
    List.mem_toFinset.mp hx₁
  have hmap₁ : x ∈ List.map edgePair C₁.edges := by
    rw [corridorWalk_edgePairs C₁ s₁ t₁ hstart₁ hfinish₁]
    exact hx₁'
  obtain ⟨e₁, he₁, hxe₁⟩ := List.mem_map.mp hmap₁
  have hx₂' : x ∈ (corridorWalk C₂ s₂ t₂ hstart₂ hfinish₂).edges :=
    List.mem_toFinset.mp hx₂
  have hmap₂ : x ∈ List.map edgePair C₂.edges := by
    rw [corridorWalk_edgePairs C₂ s₂ t₂ hstart₂ hfinish₂]
    exact hx₂'
  obtain ⟨e₂, he₂, hxe₂⟩ := List.mem_map.mp hmap₂
  have heq : e₁ = e₂ := hinj (hxe₁.trans hxe₂.symm)
  exact (Finset.disjoint_left.mp hlabels)
    (List.mem_toFinset.mpr he₁) (heq ▸ List.mem_toFinset.mpr he₂)

/-- Convert two explicitly certified corridor routes into the exact region
certificate consumed by the Section Ten packing lemma. `hedge` is the
edge-disjointness statement after forgetting route labels to the physical
simple-graph edge pairs; this is the edge-disjointness required by the
paired-path certificate. -/
noncomputable def pairedCertificate_of_corridors
    {U : Finset G.Vertex} {s t : G.Vertex}
    (C₁ C₂ : PhysicalCorridor G)
    (hstart₁ : C₁.vertices.head? = some s)
    (hfinish₁ : C₁.vertices.getLast? = some t)
    (hstart₂ : C₂.vertices.head? = some s)
    (hfinish₂ : C₂.vertices.getLast? = some t)
    (hs : s ∈ U) (ht : t ∈ U) (hst : s ≠ t)
    (hvertices₁ : C₁.vertices.Nodup) (hvertices₂ : C₂.vertices.Nodup)
    (hU₁ : ∀ v ∈ C₁.vertices, v ∈ U)
    (hU₂ : ∀ v ∈ C₂.vertices, v ∈ U)
    (hint : Disjoint C₁.vertices.tail.toFinset
      C₂.vertices.reverse.tail.toFinset)
    (routeEdgeDisjoint : Disjoint C₁.support C₂.support)
    (hcover : ∀ v ∈ U, v ∈ C₁.vertices ∨ v ∈ C₂.vertices) :
    PairedPathCertificate G U := by
  let p₁ := corridorWalk C₁ s t hstart₁ hfinish₁
  let p₂ := corridorWalk C₂ s t hstart₂ hfinish₂
  have hsupport₁ : p₁.support = C₁.vertices := corridorWalk_support C₁ s t hstart₁ hfinish₁
  have hsupport₂ : p₂.support = C₂.vertices := corridorWalk_support C₂ s t hstart₂ hfinish₂
  have hn₁ : p₁.IsPath := by
    rw [Walk.isPath_def, hsupport₁]
    exact hvertices₁
  have hn₂ : p₂.IsPath := by
    rw [Walk.isPath_def, hsupport₂]
    exact hvertices₂
  have hsub₁ : ∀ v ∈ p₁.support, v ∈ U := by
    intro v hv
    rw [hsupport₁] at hv
    exact hU₁ v hv
  have hsub₂ : ∀ v ∈ p₂.support, v ∈ U := by
    intro v hv
    rw [hsupport₂] at hv
    exact hU₂ v hv
  have hint' : Disjoint p₁.support.tail.toFinset p₂.reverse.support.tail.toFinset := by
    simpa [p₁, p₂, hsupport₁, hsupport₂, Walk.support_reverse] using hint
  have hedge := corridorWalk_edges_disjoint_of_label_disjoint C₁ C₂ s t s t
    hstart₁ hfinish₁ hstart₂ hfinish₂ routeEdgeDisjoint
  exact pairedCertificate_of_ambientPaths hs ht hst p₁ p₂ hn₁ hn₂ hsub₁ hsub₂
    hint' hedge (by
      intro v hv
      rcases hcover v hv with h | h
      · exact Or.inl (by rw [hsupport₁]; exact h)
      · exact Or.inr (by rw [hsupport₂]; exact h))

/-- Same construction when the second corridor is recorded in the opposite
orientation. This is the common case when the auxiliary parallel labels use
opposite stored orientations. -/
noncomputable def pairedCertificate_of_oppositely_oriented_corridors
    {U : Finset G.Vertex} {s t : G.Vertex}
    (C₁ C₂ : PhysicalCorridor G)
    (hstart₁ : C₁.vertices.head? = some s)
    (hfinish₁ : C₁.vertices.getLast? = some t)
    (hstart₂ : C₂.vertices.head? = some t)
    (hfinish₂ : C₂.vertices.getLast? = some s)
    (hs : s ∈ U) (ht : t ∈ U) (hst : s ≠ t)
    (hvertices₁ : C₁.vertices.Nodup) (hvertices₂ : C₂.vertices.Nodup)
    (hU₁ : ∀ v ∈ C₁.vertices, v ∈ U)
    (hU₂ : ∀ v ∈ C₂.vertices, v ∈ U)
    (hint : Disjoint C₁.vertices.tail.toFinset C₂.vertices.tail.toFinset)
    (routeEdgeDisjoint : Disjoint C₁.support C₂.support)
    (hcover : ∀ v ∈ U, v ∈ C₁.vertices ∨ v ∈ C₂.vertices) :
    PairedPathCertificate G U := by
  let p₁ := corridorWalk C₁ s t hstart₁ hfinish₁
  let raw₂ := corridorWalk C₂ t s hstart₂ hfinish₂
  let p₂ := raw₂.reverse
  have hsupp₁ : p₁.support = C₁.vertices := corridorWalk_support C₁ s t hstart₁ hfinish₁
  have hsupp₂ : raw₂.support = C₂.vertices := corridorWalk_support C₂ t s hstart₂ hfinish₂
  have hp₁ : p₁.IsPath := by
    rw [Walk.isPath_def, hsupp₁]
    exact hvertices₁
  have hraw₂ : raw₂.IsPath := by
    rw [Walk.isPath_def, hsupp₂]
    exact hvertices₂
  have hp₂ : p₂.IsPath := hraw₂.reverse
  have hsub₁ : ∀ v ∈ p₁.support, v ∈ U := by
    intro v hv
    rw [hsupp₁] at hv
    exact hU₁ v hv
  have hsub₂ : ∀ v ∈ p₂.support, v ∈ U := by
    intro v hv
    rw [Walk.support_reverse] at hv
    rw [hsupp₂] at hv
    exact hU₂ v (List.mem_reverse.mp hv)
  have hint' : Disjoint p₁.support.tail.toFinset p₂.reverse.support.tail.toFinset := by
    simpa [p₁, p₂, raw₂, hsupp₁, hsupp₂, Walk.support_reverse] using hint
  have hedgeRaw := corridorWalk_edges_disjoint_of_label_disjoint C₁ C₂ s t t s
    hstart₁ hfinish₁ hstart₂ hfinish₂ routeEdgeDisjoint
  have hedge : Disjoint p₁.edges.toFinset p₂.edges.toFinset := by
    simpa [p₁, p₂, raw₂, Walk.edges_reverse] using hedgeRaw
  exact pairedCertificate_of_ambientPaths hs ht hst p₁ p₂ hp₁ hp₂ hsub₁ hsub₂
    hint' hedge (by
      intro v hv
      rcases hcover v hv with h | h
      · exact Or.inl (by rw [hsupp₁]; exact h)
      · exact Or.inr (by
          simpa only [p₂, Walk.support_reverse, hsupp₂] using
            (List.mem_reverse.mpr h)))







end Erdos1016.Proof.CorridorPairedPathCertificates

end

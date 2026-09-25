import Erdos1016.Cleanup.Corridors.InteriorOwnership
import Erdos1016.Cleanup.Packing.CorridorPairedPathCertificates
import Erdos1016.Cleanup.Compression.CompressedRouteDecomposition

set_option autoImplicit false

/-!
# Canonical corridor intersection bridge

The retained set contains every corridor endpoint. Every internal corridor
vertex lies outside that set and has degree two. Maximality and the
degree-two condition therefore prevent a different corridor from containing
an internal vertex. -/

noncomputable section

namespace Erdos1016.Proof.PairIntersectionEndpoints

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.CorridorPairedPathCertificates
open Erdos1016.Proof.InteriorOwnership
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.CompressedRouteDecomposition
open Erdos1016.Proof.PartitionRouteDecomposition

variable {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}

private theorem start_get (C : PhysicalCorridor G) :
    C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ = corridorStart C := by
  have hh : C.vertices.head? = some
      (C.vertices.get ⟨0, by have := C.vertices_length; omega⟩) := by
    rw [List.head?_eq_getElem?]
    simp
  have hs := (corridorStart_head? C).symm.trans hh
  exact Option.some.inj hs |>.symm

private theorem finish_get (C : PhysicalCorridor G) :
    C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ =
      corridorFinish C := by
  have hh : C.vertices.getLast? = some
      (C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩) := by
    rw [List.getLast?_eq_getElem?]
    simp [C.vertices_length]
  have hs := (corridorFinish_getLast? C).symm.trans hh
  exact Option.some.inj hs |>.symm

theorem interior_index_of_mem_ne_endpoints
    (C : PhysicalCorridor G) {x : G.Vertex}
    (hx : x ∈ C.vertices) (hstart : x ≠ corridorStart C)
    (hfinish : x ≠ corridorFinish C) :
    ∃ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ = x := by
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  have hjpos : 0 < j := by
    by_contra hzero
    have hzero' : j = 0 := by omega
    subst j
    exact hstart (hget.symm.trans (start_get C))
  have hjlast : j < C.edges.length := by
    have hjlt : j < C.vertices.length := hj
    by_contra hnot
    have heqj : j = C.edges.length := by
      have hlen := C.vertices_length
      omega
    subst j
    exact hfinish (hget.symm.trans (finish_get C))
  refine ⟨⟨j - 1, ?_⟩, ?_⟩
  · have hlen := C.vertices_length
    omega
  · have hlen := C.vertices_length
    have heq : j - 1 + 1 = j := by omega
    simpa [heq] using hget

/-- An internal vertex is absent from the retained protected-or-branch set. -/
theorem corridor_interior_not_mem_retained
    (D : CorridorPartition G P₀ W)
    (C : PhysicalCorridor G) (hC : C ∈ D.corridors)
    {x : G.Vertex} (i : Fin (C.vertices.length - 2))
    (hx : x = C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩) :
    x ∉ protectedOrBranch G P₀ := by
  have hfacts := D.internal_unprotected_degree_two C hC i
  have hnotP : x ∉ P₀ := by simpa [hx] using hfacts.1
  have hdegree : G.degree x = 2 := by simpa [hx] using hfacts.2
  simp [protectedOrBranch, hnotP, hdegree]

/-- Distinct corridors of the canonical partition cannot share a vertex that
is internal to either corridor. -/
theorem distinct_corridor_vertex_intersection_is_endpoint
    (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
      corridorFinish C ∈ protectedOrBranch G P₀)
    {C E : PhysicalCorridor G} (hC : C ∈ D.corridors)
    (hE : E ∈ D.corridors) (hCE : C ≠ E)
    {x : G.Vertex} (hxC : x ∈ C.vertices) (hxE : x ∈ E.vertices) :
    (x = corridorStart C ∨ x = corridorFinish C) ∧
      (x = corridorStart E ∨ x = corridorFinish E) := by
  classical
  have hCend : x = corridorStart C ∨ x = corridorFinish C := by
    by_contra hnot
    rcases not_or.mp hnot with ⟨hstart, hfinish⟩
    obtain ⟨i, hi⟩ := interior_index_of_mem_ne_endpoints C hxC hstart hfinish
    have hxNotQ : x ∉ protectedOrBranch G P₀ :=
      corridor_interior_not_mem_retained D C hC i hi.symm
    have hnotInteriorE : x ≠ corridorStart E ∧ x ≠ corridorFinish E := by
      constructor
      · intro h
        exact hxNotQ (h ▸ (hendpoints E hE).1)
      · intro h
        exact hxNotQ (h ▸ (hendpoints E hE).2)
    obtain ⟨j, hj⟩ := interior_index_of_mem_ne_endpoints E hxE
      hnotInteriorE.1 hnotInteriorE.2
    exact distinct_corridors_cannot_share_interior_index D hC hE hCE i j
      (hi.trans hj.symm)
  have hEend : x = corridorStart E ∨ x = corridorFinish E := by
    by_contra hnot
    rcases not_or.mp hnot with ⟨hstart, hfinish⟩
    obtain ⟨j, hj⟩ := interior_index_of_mem_ne_endpoints E hxE hstart hfinish
    have hxNotQ : x ∉ protectedOrBranch G P₀ :=
      corridor_interior_not_mem_retained D E hE j hj.symm
    rcases hCend with h | h
    · exact hxNotQ (h ▸ (hendpoints C hC).1)
    · exact hxNotQ (h ▸ (hendpoints C hC).2)
  exact ⟨hCend, hEend⟩

private theorem source_mem_parallel_endpoint_pair
    {V E : Type*} [DecidableEq V]
    (src dst : E → V) (a b : E)
    (hparallel : (src a = src b ∧ dst a = dst b) ∨
      (src a = dst b ∧ dst a = src b))
    {e : E} (he : e = a ∨ e = b) : src e ∈ ({src a, dst a} : Finset V) := by
  rcases he with rfl | rfl
  · simp
  · rcases hparallel with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp [hs.symm]
    · simp [ht.symm]

private theorem target_mem_parallel_endpoint_pair
    {V E : Type*} [DecidableEq V]
    (src dst : E → V) (a b : E)
    (hparallel : (src a = src b ∧ dst a = dst b) ∨
      (src a = dst b ∧ dst a = src b))
    {e : E} (he : e = a ∨ e = b) : dst e ∈ ({src a, dst a} : Finset V) := by
  rcases he with rfl | rfl
  · simp
  · rcases hparallel with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp [ht.symm]
    · simp [hs.symm]

private theorem canonical_route_corridors_pair_endpoints_intersect
    (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
      corridorFinish C ∈ protectedOrBranch G P₀)
    (a b c d : (compressedCorridorGraph D hendpoints).Edge)
    (hab : ((compressedCorridorGraph D hendpoints).src a =
        (compressedCorridorGraph D hendpoints).src b ∧
      (compressedCorridorGraph D hendpoints).dst a =
        (compressedCorridorGraph D hendpoints).dst b) ∨
      ((compressedCorridorGraph D hendpoints).src a =
        (compressedCorridorGraph D hendpoints).dst b ∧
      (compressedCorridorGraph D hendpoints).dst a =
        (compressedCorridorGraph D hendpoints).src b))
    (hcd : ((compressedCorridorGraph D hendpoints).src c =
        (compressedCorridorGraph D hendpoints).src d ∧
      (compressedCorridorGraph D hendpoints).dst c =
        (compressedCorridorGraph D hendpoints).dst d) ∨
      ((compressedCorridorGraph D hendpoints).src c =
        (compressedCorridorGraph D hendpoints).dst d ∧
      (compressedCorridorGraph D hendpoints).dst c =
        (compressedCorridorGraph D hendpoints).src d))
    {e f : (compressedCorridorGraph D hendpoints).Edge}
    (he : e = a ∨ e = b) (hf : f = c ∨ f = d)
    {x : G.Vertex} (hxe : x ∈ (corridorAt D e).vertices)
    (hxf : x ∈ (corridorAt D f).vertices) :
    ¬ Disjoint ({(compressedCorridorGraph D hendpoints).src a,
        (compressedCorridorGraph D hendpoints).dst a} :
          Finset (compressedCorridorGraph D hendpoints).Vertex)
      {(compressedCorridorGraph D hendpoints).src c,
        (compressedCorridorGraph D hendpoints).dst c} := by
  classical
  by_cases hef : e = f
  · apply Finset.not_disjoint_iff.mpr
    refine ⟨(compressedCorridorGraph D hendpoints).src e, ?_, ?_⟩
    · exact source_mem_parallel_endpoint_pair _ _ a b hab he
    · have hsource := source_mem_parallel_endpoint_pair _ _ c d hcd hf
      simpa [hef] using hsource
  · have hget : Function.Injective (corridorFamily D).get :=
      (List.nodup_iff_injective_get).mp (Finset.nodup_toList D.corridors.toFinset)
    have hcorr : corridorAt D e ≠ corridorAt D f := by
      intro heq
      exact hef (hget heq)
    have hend := distinct_corridor_vertex_intersection_is_endpoint D hendpoints
      (corridorAt_mem D e) (corridorAt_mem D f) hcorr hxe hxf
    have hφinj := compressedCorridorVertexMap_injective D hendpoints
    have hφstartE : compressedCorridorVertexMap D hendpoints
        ((compressedCorridorGraph D hendpoints).src e) = corridorStart (corridorAt D e) :=
      compressedCorridor_src_image D hendpoints e
    have hφfinishE : compressedCorridorVertexMap D hendpoints
        ((compressedCorridorGraph D hendpoints).dst e) = corridorFinish (corridorAt D e) :=
      compressedCorridor_dst_image D hendpoints e
    have hφstartF : compressedCorridorVertexMap D hendpoints
        ((compressedCorridorGraph D hendpoints).src f) = corridorStart (corridorAt D f) :=
      compressedCorridor_src_image D hendpoints f
    have hφfinishF : compressedCorridorVertexMap D hendpoints
        ((compressedCorridorGraph D hendpoints).dst f) = corridorFinish (corridorAt D f) :=
      compressedCorridor_dst_image D hendpoints f
    apply Finset.not_disjoint_iff.mpr
    rcases hend.1 with heStart | heFinish <;>
      rcases hend.2 with hfStart | hfFinish
    · have hEq := hφinj (calc
        compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).src e) = corridorStart (corridorAt D e) := hφstartE
        _ = x := heStart.symm
        _ = corridorStart (corridorAt D f) := hfStart
        _ = compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).src f) := hφstartF.symm)
      refine ⟨(compressedCorridorGraph D hendpoints).src e, ?_, ?_⟩
      · exact source_mem_parallel_endpoint_pair _ _ a b hab he
      · have hsource := source_mem_parallel_endpoint_pair _ _ c d hcd hf
        rw [hEq]
        exact hsource
    · have hEq := hφinj (calc
        compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).src e) = corridorStart (corridorAt D e) := hφstartE
        _ = x := heStart.symm
        _ = corridorFinish (corridorAt D f) := hfFinish
        _ = compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).dst f) := hφfinishF.symm)
      refine ⟨(compressedCorridorGraph D hendpoints).src e, ?_, ?_⟩
      · exact source_mem_parallel_endpoint_pair _ _ a b hab he
      · have htarget := target_mem_parallel_endpoint_pair _ _ c d hcd hf
        rw [hEq]
        exact htarget
    · have hEq := hφinj (calc
        compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).dst e) = corridorFinish (corridorAt D e) := hφfinishE
        _ = x := heFinish.symm
        _ = corridorStart (corridorAt D f) := hfStart
        _ = compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).src f) := hφstartF.symm)
      refine ⟨(compressedCorridorGraph D hendpoints).dst e, ?_, ?_⟩
      · exact target_mem_parallel_endpoint_pair _ _ a b hab he
      · have hsource := source_mem_parallel_endpoint_pair _ _ c d hcd hf
        rw [hEq]
        exact hsource
    · have hEq := hφinj (calc
        compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).dst e) = corridorFinish (corridorAt D e) := hφfinishE
        _ = x := heFinish.symm
        _ = corridorFinish (corridorAt D f) := hfFinish
        _ = compressedCorridorVertexMap D hendpoints
            ((compressedCorridorGraph D hendpoints).dst f) := hφfinishF.symm)
      refine ⟨(compressedCorridorGraph D hendpoints).dst e, ?_, ?_⟩
      · exact target_mem_parallel_endpoint_pair _ _ a b hab he
      · have htarget := target_mem_parallel_endpoint_pair _ _ c d hcd hf
        rw [hEq]
        exact htarget

/-- Intersecting unions of two canonical routes imply intersecting unordered
endpoint pairs in the compressed corridor graph. -/
theorem canonical_parallel_pair_route_intersection_implies_endpoint_intersection
    (D : CorridorPartition G P₀ W)
    (hendpoints : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ protectedOrBranch G P₀ ∧
      corridorFinish C ∈ protectedOrBranch G P₀)
    (a b c d : (compressedCorridorGraph D hendpoints).Edge)
    (hab : ((compressedCorridorGraph D hendpoints).src a =
        (compressedCorridorGraph D hendpoints).src b ∧
      (compressedCorridorGraph D hendpoints).dst a =
        (compressedCorridorGraph D hendpoints).dst b) ∨
      ((compressedCorridorGraph D hendpoints).src a =
        (compressedCorridorGraph D hendpoints).dst b ∧
      (compressedCorridorGraph D hendpoints).dst a =
        (compressedCorridorGraph D hendpoints).src b))
    (hcd : ((compressedCorridorGraph D hendpoints).src c =
        (compressedCorridorGraph D hendpoints).src d ∧
      (compressedCorridorGraph D hendpoints).dst c =
        (compressedCorridorGraph D hendpoints).dst d) ∨
      ((compressedCorridorGraph D hendpoints).src c =
        (compressedCorridorGraph D hendpoints).dst d ∧
      (compressedCorridorGraph D hendpoints).dst c =
        (compressedCorridorGraph D hendpoints).src d))
    (hoverlap : ¬ Disjoint
      ((corridorAt D a).vertices.toFinset ∪ (corridorAt D b).vertices.toFinset)
      ((corridorAt D c).vertices.toFinset ∪ (corridorAt D d).vertices.toFinset)) :
    ¬ Disjoint ({(compressedCorridorGraph D hendpoints).src a,
        (compressedCorridorGraph D hendpoints).dst a} :
          Finset (compressedCorridorGraph D hendpoints).Vertex)
      {(compressedCorridorGraph D hendpoints).src c,
        (compressedCorridorGraph D hendpoints).dst c} := by
  classical
  obtain ⟨x, hxab, hxcd⟩ := Finset.not_disjoint_iff.mp hoverlap
  rcases Finset.mem_union.mp hxab with hxa | hxb
  · rcases Finset.mem_union.mp hxcd with hxc | hxd
    · exact canonical_route_corridors_pair_endpoints_intersect D hendpoints a b c d hab hcd
        (Or.inl rfl) (Or.inl rfl) (List.mem_toFinset.mp hxa) (List.mem_toFinset.mp hxc)
    · exact canonical_route_corridors_pair_endpoints_intersect D hendpoints a b c d hab hcd
        (Or.inl rfl) (Or.inr rfl) (List.mem_toFinset.mp hxa) (List.mem_toFinset.mp hxd)
  · rcases Finset.mem_union.mp hxcd with hxc | hxd
    · exact canonical_route_corridors_pair_endpoints_intersect D hendpoints a b c d hab hcd
        (Or.inr rfl) (Or.inl rfl) (List.mem_toFinset.mp hxb) (List.mem_toFinset.mp hxc)
    · exact canonical_route_corridors_pair_endpoints_intersect D hendpoints a b c d hab hcd
        (Or.inr rfl) (Or.inr rfl) (List.mem_toFinset.mp hxb) (List.mem_toFinset.mp hxd)

end Erdos1016.Proof.PairIntersectionEndpoints

end

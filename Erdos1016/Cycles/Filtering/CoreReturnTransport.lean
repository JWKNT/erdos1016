import Erdos1016.Cycles.Geometry.PhysicalCycleRestriction
import Erdos1016.Cycles.Filtering.ReturnExclusion
import Erdos1016.Decomposition.TwoCore.PathConvexity

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Erdos1016.Proof.InducedCoreReturnTransport
open BoundaryDecay Nonbacktracking PhysicalCycleEmbedding ExternalReturnFilter

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A graph embedding that reflects adjacency transports the return filter
on the literal image of the safe region. -/
theorem noReturnWithin_map {H G : PhysicalGraph} (E : Embedding H G)
    (hreflect : ∀ u v, G.toSimpleGraph.Adj (E.vertex u) (E.vertex v) → H.toSimpleGraph.Adj u v)
    (V C : Finset H.Vertex) (q : ℕ)
    (hreturn : NoShortExternalReturnWithin H V C q) :
    NoShortExternalReturnWithin G (V.image E.vertex) (C.image E.vertex) q := by
  let f : ↑(V.image E.vertex) → H.Vertex := fun v => (Finset.mem_image.mp v.2).choose
  have hf (v : ↑(V.image E.vertex)) : f v ∈ V ∧ E.vertex (f v) = v.1 :=
    (Finset.mem_image.mp v.2).choose_spec
  let φ : G.toSimpleGraph.induce (↑(V.image E.vertex) : Set G.Vertex) →g H.toSimpleGraph :=
    { toFun := f
      map_rel' := by
        intro v w hvw
        apply hreflect
        simpa only [(hf v).2, (hf w).2] using hvw }
  have hφ : Function.Injective φ := by
    intro v w hvw
    apply Subtype.ext
    exact ((hf v).2.symm.trans (congrArg E.vertex hvw)).trans (hf w).2
  intro r s u v hu hv huv hru hsv p hp hpV hpC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  let p' := restrictWalk G.toSimpleGraph (↑(V.image E.vertex) : Set G.Vertex) p hpV
  let p₀ := p'.map φ
  have hpath : p₀.IsPath := by
    apply (SimpleGraph.Walk.map_isPath_iff_of_injective hφ).mpr
    apply (SimpleGraph.Walk.map_isPath_iff_of_injective
      (f := (SimpleGraph.Embedding.induce (G := G.toSimpleGraph) (↑(V.image E.vertex) : Set G.Vertex)).toHom)
      Subtype.val_injective).mp
    simpa only [p', restrictWalk_map] using hp
  have hreg : ∀ z ∈ p₀.support, z ∈ V := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp (show z ∈ p'.support.map φ from by
      simpa only [p₀, SimpleGraph.Walk.support_map] using hz)
    exact (hf w).1
  have hout : ∀ z ∈ p₀.support, z ∉ C := by
    intro z hz hzC
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (show z ∈ p'.support.map φ from by
      simpa only [p₀, SimpleGraph.Walk.support_map] using hz)
    have hwp : w.1 ∈ p.support := by
      rw [← restrictWalk_map G.toSimpleGraph (↑(V.image E.vertex) : Set G.Vertex) p hpV,
        SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨w, hw, rfl⟩
    apply hpC w.1 hwp
    exact Finset.mem_image.mpr ⟨φ w, hzC, (hf w).2⟩
  have h := hreturn (φ ⟨r, hpV r p.start_mem_support⟩)
    (φ ⟨s, hpV s p.end_mem_support⟩) a b ha hb
    (fun hab => huv (congrArg E.vertex hab))
    (hreflect _ _ (by simpa only [show E.vertex (φ ⟨r, hpV r p.start_mem_support⟩) = r from (hf _).2] using hru))
    (hreflect _ _ (by simpa only [show E.vertex (φ ⟨s, hpV s p.end_mem_support⟩) = s from (hf _).2] using hsv))
    p₀ hpath hreg hout
  have hlen : p'.length = p.length := by
    simpa only [SimpleGraph.Walk.length_map] using congrArg SimpleGraph.Walk.length
      (restrictWalk_map G.toSimpleGraph (↑(V.image E.vertex) : Set G.Vertex) p hpV)
  simpa only [p₀, SimpleGraph.Walk.length_map, hlen] using h

/-- Adding the two attachment edges of an external path produces a simple
core-to-core path, so maximality forces the entire external path into the
original two-core. The region is the original graph region throughout. -/
theorem external_path_subset_twoCore (G : PhysicalGraph) (U C : Finset G.Vertex)
    (hC : C ⊆ FiniteTwoCore.vertices G.toSimpleGraph U)
    {r s u v : G.Vertex} (hu : u ∈ C) (hv : v ∈ C) (huv : u ≠ v)
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v)
    (p : G.toSimpleGraph.Walk r s) (hp : p.IsPath)
    (hpU : ∀ z ∈ p.support, z ∈ U) (hpC : ∀ z ∈ p.support, z ∉ C) :
    ∀ z ∈ p.support, z ∈ FiniteTwoCore.vertices G.toSimpleGraph U := by
  have huq : u ∉ p.support := fun h => hpC u h hu
  have hvq : v ∉ p.support := fun h => hpC v h hv
  let tail : G.toSimpleGraph.Walk r v := p.concat hsv
  have htail : tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [tail, List.concat_eq_append] using
      (List.nodup_append.mpr ⟨hp.support_nodup, by simp,
        by
          rw [List.disjoint_left]
          intro z hz hzv
          have : z = v := by simpa using hzv
          exact hvq (this ▸ hz)⟩)
  let w : G.toSimpleGraph.Walk u v := .cons hru.symm tail
  have hw : w.IsPath := by
    apply htail.cons
    simpa only [tail, SimpleGraph.Walk.support_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton, not_or] using And.intro huq huv
  have hwU : ∀ z ∈ w.support, z ∈ U := by
    intro z hz
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons,
      tail, SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact FiniteTwoCore.vertices_subset G.toSimpleGraph U (hC hu)
    · exact hpU z hz
    · exact FiniteTwoCore.vertices_subset G.toSimpleGraph U (hC hv)
  have hc := TwoCorePathGeometry.path_support_subset_twoCore G.toSimpleGraph U w hw (hC hu) (hC hv) hwU
  intro z hz
  apply hc
  simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons,
    tail, SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton, List.not_mem_nil, or_false]
  exact Or.inr (Or.inl hz)

/-- The accepted return exclusion on the literal physical two-core extends
to the entire original region. Pruned trees cannot create an external return. -/
theorem noReturnWithin_of_induced_core (G : PhysicalGraph) (U : Finset G.Vertex)
    (C : (FiniteTwoCore.inducedPhysical G (FiniteTwoCore.vertices G.toSimpleGraph U)).CycleWord)
    (q : ℕ) (hreturn : NoShortExternalReturnWithin
      (FiniteTwoCore.inducedPhysical G (FiniteTwoCore.vertices G.toSimpleGraph U))
      Finset.univ (Cycle.vertices C) q) :
    NoShortExternalReturnWithin G U
      (Cycle.vertices ((induced G (FiniteTwoCore.vertices G.toSimpleGraph U)).liftCycle C)) q := by
  let K := FiniteTwoCore.vertices G.toSimpleGraph U
  let E := induced G K
  have himage : Finset.univ.image E.vertex = K := by
    ext v
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using induced_vertex_range G K v
  have hret := noReturnWithin_map E (fun u v h => (induced_adj_iff G K u v).mpr h)
    Finset.univ (Cycle.vertices C) q hreturn
  rw [himage, ← E.liftCycle_vertices] at hret
  intro r s u v hu hv huv hru hsv p hp hpU hpC
  exact hret r s u v hu hv huv hru hsv p hp
    (external_path_subset_twoCore G U _ (induced_liftCycle_subset G K C)
      hu hv huv hru hsv p hp hpU hpC) hpC

end Erdos1016.Proof.InducedCoreReturnTransport

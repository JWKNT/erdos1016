import Erdos1016.Graph.PathExpansion.Basic

set_option autoImplicit false

/-!
# Recorded arbitrary-length series routes

This experiment packages one designated auxiliary edge together with a
finite, oriented physical path that records its route support. The auxiliary
and physical graphs and the complete edge-disjoint route system are inputs;
this module does not construct the global suppressed graph from a host graph.
It proves exact cycle-rank transport when the recorded chain and retained
routes satisfy the path-constancy conditions needed by route expansion.
-/

noncomputable section

namespace Erdos1016.Proof.SingleSeriesRouteCompression

open Erdos1016
open Erdos1016.FiniteMultiGraph

/-- Label-counting degree in a finite multigraph. -/
def edgeIncidenceDegree (P : FiniteMultiGraph) (v : P.Vertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : P.Edge => P.src e = v ∨ P.dst e = v).card





/-- Physical labels not in the recorded route. -/
abbrev RetainedEdge (P : FiniteMultiGraph) (S : Finset P.Edge) :=
  {e : P.Edge // e ∉ S}

/-- Auxiliary labels are retained original edges together with one synthetic
edge representing the recorded route. -/
abbrev CompressedEdge (P : FiniteMultiGraph) (S : Finset P.Edge) :=
  Sum (RetainedEdge P S) Unit

/-- Reindex the retained labels and the synthetic route edge as a finite
multigraph on the original vertex set. -/
def compressedGraph (P : FiniteMultiGraph) (S : Finset P.Edge)
    (u v : P.Vertex) : FiniteMultiGraph := by
  classical
  exact {
    vertexCount := P.vertexCount
    edgeCount := Fintype.card (CompressedEdge P S)
    src := fun i => match (Fintype.equivFin (CompressedEdge P S)).symm i with
      | .inl e => P.src e.1
      | .inr _ => u
    dst := fun i => match (Fintype.equivFin (CompressedEdge P S)).symm i with
      | .inl e => P.dst e.1
      | .inr _ => v }



private theorem boundary_singleton (P : FiniteMultiGraph) (e : P.Edge) :
    P.boundary (edgeSetWord P {e}) = endpointDemand P P (fun w => w) e := by
  classical
  ext w
  simp only [FiniteMultiGraph.boundary, LinearMap.coe_mk, AddHom.coe_mk,
    edgeSetWord, endpointDemand]
  simp only [Finset.mem_singleton]
  change (∑ f : P.Edge,
      ((if P.src f = w then if f = e then (1 : F₂) else 0 else 0) +
       (if P.dst f = w then if f = e then (1 : F₂) else 0 else 0))) = _
  rw [Finset.sum_add_distrib]
  have hsrc : (∑ f : P.Edge,
      if P.src f = w then if f = e then (1 : F₂) else 0 else 0) =
      if P.src e = w then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro f _ hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ e)).elim
  have hdst : (∑ f : P.Edge,
      if P.dst f = w then if f = e then (1 : F₂) else 0 else 0) =
      if P.dst e = w then 1 else 0 := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro f _ hne
      simp [hne]
    · intro h
      exact (h (Finset.mem_univ e)).elim
  rw [hsrc, hdst]

/-- For an injectively labeled path, its support indicator is the sum of its
singleton-edge indicators. -/
private theorem edgeSetWord_image_eq_sum_singletons (P : FiniteMultiGraph)
    {n : ℕ} (path : Fin n → P.Edge) (hinj : Function.Injective path) :
    edgeSetWord P (Finset.univ.image path) =
      ∑ i : Fin n, edgeSetWord P {path i} := by
  classical
  ext e
  simp only [edgeSetWord, Finset.sum_apply]
  by_cases he : e ∈ Finset.univ.image path
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp he
    subst e
    simp only [if_pos (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hne : path j ≠ path i := fun h => hji (hinj h)
      have hne' : path i ≠ path j := Ne.symm hne
      simp [hne']
    · intro h
      exact (h (Finset.mem_univ i)).elim
  · simp only [if_neg he]
    symm
    simp only [Finset.mem_singleton]
    change (∑ i ∈ Finset.univ,
      if e = path i then (1 : F₂) else 0) = 0
    apply Finset.sum_eq_zero
    intro i hi
    have hne : path i ≠ e := by
      intro h
      apply he
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩
    have hne' : e ≠ path i := Ne.symm hne
    simp [hne']

/-- Boundary of the indicator of an injective path support is the sum of the
individual oriented endpoint demands. -/
theorem boundary_image_path_eq_endpoint_sum (P : FiniteMultiGraph)
    {n : ℕ} (path : Fin n → P.Edge) (hinj : Function.Injective path) :
    P.boundary (edgeSetWord P (Finset.univ.image path)) =
      ∑ i : Fin n, endpointDemand P P (fun w => w) (path i) := by
  rw [edgeSetWord_image_eq_sum_singletons P path hinj, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [boundary_singleton P (path i)]











/-- Number of physical edges in the recorded route is `n + 1`; it has `n`
internal vertices. -/
structure RecordedSeriesChain (A P : FiniteMultiGraph)
    (R : EdgeDisjointRouteSystem A P) where
  syntheticEdge : A.Edge
  internalCount : ℕ
  pathVertex : Fin (internalCount + 2) → P.Vertex
  pathEdge : Fin (internalCount + 1) → P.Edge
  vertices_injective : Function.Injective pathVertex
  edges_injective : Function.Injective pathEdge
  path_src : ∀ i : Fin (internalCount + 1),
    P.src (pathEdge i) = pathVertex ⟨i.val, by omega⟩
  path_dst : ∀ i : Fin (internalCount + 1),
    P.dst (pathEdge i) = pathVertex ⟨i.val + 1, by omega⟩
  interior_degree_two : ∀ i : Fin internalCount,
    edgeIncidenceDegree P (pathVertex ⟨i.val + 1, by omega⟩) = 2
  route_support : R.support syntheticEdge =
    Finset.univ.image pathEdge
  source_endpoint : R.vertexMap (A.src syntheticEdge) = pathVertex 0
  target_endpoint : R.vertexMap (A.dst syntheticEdge) =
    pathVertex ⟨internalCount + 1, by omega⟩
  protectedSet : Finset P.Vertex
  protected_nonempty : protectedSet.Nonempty
  source_protected : pathVertex 0 ∈ protectedSet
  target_protected : pathVertex ⟨internalCount + 1, by omega⟩ ∈ protectedSet
  internal_unprotected : ∀ i : Fin internalCount,
    pathVertex ⟨i.val + 1, by omega⟩ ∉ protectedSet
  /-- All other auxiliary edges are retained labels, so their routes are
  singleton supports and are constant tautologically. -/
  other_routes_singleton : ∀ e : A.Edge, e ≠ syntheticEdge →
    ∃ p : P.Edge, R.support e = {p}













end Erdos1016.Proof.SingleSeriesRouteCompression

import Erdos1016.Cleanup.Corridors.ComponentBoundaryCount
import Erdos1016.Cleanup.Paths.DegreeTwoSpanningPath

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidablePred (fun v : V => v ∈ c.supp) := fun v =>
    Classical.propDecidable _
  exact Subtype.fintype _

namespace Erdos1016.Proof.ComponentBoundaryEndpoints

open Erdos1016
open SimpleGraph

/-- In a spanning path of a degree-two region, every vertex incident to an
edge leaving the region is a path endpoint. -/
theorem boundary_vertex_is_endpoint
    (G : PhysicalGraph) (C : Finset G.Vertex) {a b : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ v, v ∈ C → v ∈ p.support)
    (hsubset : ∀ v, v ∈ p.support → v ∈ C)
    (hdegree : ∀ v ∈ C, (G.toSimpleGraph.neighborFinset v).card = 2)
    {x u : G.Vertex} (hx : x ∈ C) (hxu : G.toSimpleGraph.Adj x u)
    (hu : u ∉ C) : x = a ∨ x = b := by
  classical
  by_contra hend
  have hxa : x ≠ a := by
    intro h
    exact hend (Or.inl h)
  have hxb : x ≠ b := by
    intro h
    exact hend (Or.inr h)
  obtain ⟨v, w, hvw, hxv, hxw, hvpath, hwpath⟩ :=
    Erdos1016.Proof.FiniteTreeDegreeTwoPath.exists_two_path_neighbors_of_mem_support_of_ne_endpoints
      hp (hcover x hx) hxa hxb
  have huv : u ∈ G.toSimpleGraph.neighborFinset x :=
    (SimpleGraph.mem_neighborFinset _ _ _).2 hxu
  have hxv' : v ∈ G.toSimpleGraph.neighborFinset x :=
    (SimpleGraph.mem_neighborFinset _ _ _).2 hxv
  have hxw' : w ∈ G.toSimpleGraph.neighborFinset x :=
    (SimpleGraph.mem_neighborFinset _ _ _).2 hxw
  have hvC : v ∈ C := hsubset v hvpath
  have hwC : w ∈ C := hsubset w hwpath
  have hvu : v ≠ u := by
    intro h
    subst u
    exact hu hvC
  have hwu : w ≠ u := by
    intro h
    subst u
    exact hu hwC
  have hvw' : v ≠ w := hvw
  have hthree : ({v, w, u} : Finset G.Vertex).card = 3 := by
    simp [hvw', hvu, hwu]
  have hsub' : ({v, w, u} : Finset G.Vertex) ⊆
      G.toSimpleGraph.neighborFinset x := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hxv'
    · exact hxw'
    · exact huv
  have hle := Finset.card_le_card hsub'
  rw [hdegree x hx] at hle
  omega

/-- A spanning path through an unprotected degree-two component has all its
boundary adjacencies at its two path endpoints.  The endpoints may coincide,
which is exactly the singleton-component case. -/
theorem exists_spanning_path_with_boundary_at_endpoints
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent) :
    ∃ a b, ∃ p : ((G.toSimpleGraph.induce {v | v ∉ P}).induce c.supp).Walk a b,
      p.IsPath ∧ (∀ v, v ∈ p.support) ∧
      (∀ x y, x ∈ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) →
        y ∉ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) →
        G.toSimpleGraph.Adj x y → x = a.1.1 ∨ x = b.1.1) ∧
      DegreeTwoComponentCut.boundaryCount G.toSimpleGraph
        ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) = 2 := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let H : SimpleGraph U := G.toSimpleGraph.induce U
  let K : SimpleGraph c.supp := H.induce c.supp
  obtain ⟨a, b, p, hp, hspan⟩ :=
    Erdos1016.Proof.DegreeTwoSpanningPath.exists_component_spanning_path
      G P hconn hP hdegree c
  refine ⟨a, b, p, hp, hspan, ?_, ?_⟩
  · intro x y hxC hyout hxy
    by_contra hend
    have hxa : x ≠ a.1.1 := by
      intro h
      exact hend (Or.inl h)
    have hxb : x ≠ b.1.1 := by
      intro h
      exact hend (Or.inr h)
    have hxU : x ∈ U := by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hxC
      exact z.2
    let vx : c.supp := ⟨⟨x, hxU⟩, by
        rcases Finset.mem_map.mp hxC with ⟨z, hz, heq⟩
        have hzx : z.1 = x := congrArg (fun w : G.Vertex => w) heq
        subst x
        exact Set.mem_toFinset.mp hz⟩
    have hxSupp : vx ∈ p.support := hspan vx
    have hxa' : vx ≠ a := by
      intro h
      apply hxa
      exact congrArg (fun z : c.supp => z.1.1) h
    have hxb' : vx ≠ b := by
      intro h
      apply hxb
      exact congrArg (fun z : c.supp => z.1.1) h
    obtain ⟨u, w, huw, hvu, hvw, huPath, hwPath⟩ :=
      Erdos1016.Proof.FiniteTreeDegreeTwoPath.exists_two_path_neighbors_of_mem_support_of_ne_endpoints
        hp hxSupp hxa' hxb'
    have hux : K.Adj vx u := hvu
    have hwx : K.Adj vx w := hvw
    have huxH : H.Adj vx.1 u.1 := hux
    have hwxH : H.Adj vx.1 w.1 := hwx
    have huxG : G.toSimpleGraph.Adj x u.1.1 := huxH
    have hwxG : G.toSimpleGraph.Adj x w.1.1 := hwxH
    have huNeY : u.1.1 ≠ y := by
      intro h
      apply hyout
      have huC : u.1.1 ∈ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) := by
        exact Finset.mem_map.mpr ⟨u.1, Set.mem_toFinset.mpr u.2, rfl⟩
      simpa [h] using huC
    have hwNeY : w.1.1 ≠ y := by
      intro h
      apply hyout
      have hwC : w.1.1 ∈ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) := by
        exact Finset.mem_map.mpr ⟨w.1, Set.mem_toFinset.mpr w.2, rfl⟩
      simpa [h] using hwC
    have huxNeW : u.1.1 ≠ w.1.1 := by
      intro h
      apply huw
      exact Subtype.ext (Subtype.ext h)
    have hxyFin : y ∈ G.toSimpleGraph.neighborFinset x :=
      (SimpleGraph.mem_neighborFinset _ _ _).2 hxy
    have huxFin : u.1.1 ∈ G.toSimpleGraph.neighborFinset x :=
      (SimpleGraph.mem_neighborFinset _ _ _).2 huxG
    have hwxFin : w.1.1 ∈ G.toSimpleGraph.neighborFinset x :=
      (SimpleGraph.mem_neighborFinset _ _ _).2 hwxG
    have hthree : ({u.1.1, w.1.1, y} : Finset G.Vertex).card = 3 := by
      simp [huxNeW, huNeY, hwNeY]
    have hsub : ({u.1.1, w.1.1, y} : Finset G.Vertex) ⊆
        G.toSimpleGraph.neighborFinset x := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact huxFin
      · exact hwxFin
      · exact hxyFin
    have hdeg := hdegree x (by
      intro hxP
      have hxCinU : x ∈ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) := hxC
      obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp hxCinU
      have hzx : z.1 = x := congrArg (fun w : G.Vertex => w) heq
      subst x
      exact z.2 hxP)
    have hcard := PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G x
    rw [hdeg] at hcard
    have hle := Finset.card_le_card hsub
    have hthree_le : 3 ≤ (G.toSimpleGraph.neighborFinset x).card := by
      rw [← hthree]
      exact hle
    omega
  · exact ComponentBoundaryCount.component_boundaryCount_eq_two
      G P hconn hP hdegree c

/-- The component spanning path may be viewed directly in the ambient
physical simple graph; its support is exactly the component vertex set. -/
theorem component_ambient_spanning_path
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent) :
    ∃ a b : G.Vertex, ∃ p : G.toSimpleGraph.Walk a b, p.IsPath ∧
      (∀ v, v ∈ p.support → v ∈
        ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P}))) ∧
      (∀ v, v ∈ ((c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) → v ∈ p.support) := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let H : SimpleGraph U := G.toSimpleGraph.induce U
  let K : SimpleGraph c.supp := H.induce c.supp
  obtain ⟨a, b, p, hp, hspan, hboundary, hcount⟩ :=
    exists_spanning_path_with_boundary_at_endpoints G P hconn hP hdegree c
  let eU : H ↪g G.toSimpleGraph := @SimpleGraph.Embedding.induce G.Vertex G.toSimpleGraph U
  let eC : K ↪g H := @SimpleGraph.Embedding.induce U H c.supp
  let f : K ↪g G.toSimpleGraph := eC.trans eU
  let q : G.toSimpleGraph.Walk a.1.1 b.1.1 := p.map f.toHom
  have hq : q.IsPath := Walk.map_isPath_of_injective f.injective hp
  have hqSupport : q.support = List.map (fun z : c.supp => z.1.1) p.support := by
    change (p.map f.toHom).support = _
    rw [Walk.support_map]
    congr 1
  refine ⟨a.1.1, b.1.1, q, hq, ?_, ?_⟩
  · intro v hv
    rw [hqSupport] at hv
    have hv' : v ∈ List.map (fun z : c.supp => z.1.1) p.support := by
      exact hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv'
    have hzC : z.1.1 ∈ ((c.supp.toFinset).map
        (Function.Embedding.subtype U)) :=
      Finset.mem_map.mpr ⟨z.1, Set.mem_toFinset.mpr z.2, rfl⟩
    exact hzC
  · intro v hv
    obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp hv
    let z' : c.supp := ⟨z, Set.mem_toFinset.mp hz⟩
    have hz' : z' ∈ p.support := hspan z'
    have hmap : z'.1.1 ∈ List.map (fun w : c.supp => w.1.1) p.support :=
      List.mem_map.mpr ⟨z', hz', rfl⟩
    have hzv : z.1 = v := by
      change z.1 = v at heq
      exact heq
    have hv' : v ∈ List.map (fun w : c.supp => w.1.1) p.support := by
      rw [← hzv]
      simpa [z'] using hmap
    rw [hqSupport]
    exact hv'

end Erdos1016.Proof.ComponentBoundaryEndpoints

end

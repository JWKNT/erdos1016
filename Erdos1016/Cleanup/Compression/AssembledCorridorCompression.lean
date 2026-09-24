import Erdos1016.Cleanup.Corridors.CoreComponentAssembly

set_option autoImplicit false

noncomputable section

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _
local instance {V : Type*} [Finite V] (H : SimpleGraph V)
    (c : H.ConnectedComponent) : Fintype c.supp := Fintype.ofFinite _

namespace Erdos1016.Proof.AssembledCorridorCompression

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.EdgeSeedConstruction
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.PhysicalDegreeTwoCoreBoundaryAccounting
open Erdos1016.Proof.CoreComponentAssembly

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

def assembledPartition (G : PhysicalGraph) (P : Finset G.Vertex)
    (W : Finset G.Edge) (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) :
    CorridorPartition G P W :=
  exists_corridor_partition_of_degree_two_three G P W hconn hP hdegree hW

def retainedVertices (G : PhysicalGraph) (P : Finset G.Vertex) : Finset G.Vertex :=
  protectedOrBranch G P

def assembledCorridorFamily (D : CorridorPartition G P W) : List (PhysicalCorridor G) := by
  classical
  exact D.corridors.toFinset.toList

def assembledCorridorAt (D : CorridorPartition G P W)
    (e : Fin (assembledCorridorFamily D).length) : PhysicalCorridor G :=
  (assembledCorridorFamily D).get e

theorem assembledCorridorAt_mem (D : CorridorPartition G P W)
    (e : Fin (assembledCorridorFamily D).length) :
    assembledCorridorAt D e ∈ D.corridors := by
  classical
  have hmem := List.get_mem (assembledCorridorFamily D) e
  change assembledCorridorAt D e ∈ D.corridors.toFinset.toList at hmem
  exact List.mem_toFinset.mp (Finset.mem_toList.mp hmem)

def retainedIndex (Q : Finset G.Vertex) {v : G.Vertex} (hv : v ∈ Q) : Fin Q.card :=
  Finset.equivFin Q ⟨v, hv⟩

/-- The compressed finite multigraph has one vertex for each retained
protected-or-branch vertex and one edge for each distinct corridor. -/
def compressedCorridorGraph (D : CorridorPartition G P W)
    (Q : Finset G.Vertex)
    (hendpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q) : FiniteMultiGraph := by
  classical
  exact {
    vertexCount := Q.card
    edgeCount := (assembledCorridorFamily D).length
    src := fun e => retainedIndex Q
      (hendpoint (assembledCorridorAt D e) (assembledCorridorAt_mem D e)).1
    dst := fun e => retainedIndex Q
      (hendpoint (assembledCorridorAt D e) (assembledCorridorAt_mem D e)).2 }

def canonicalCompressedCorridorGraph
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) : FiniteMultiGraph := by
  let D := assembledPartition G P W hW hconn hP hdegree
  exact compressedCorridorGraph D (retainedVertices G P)
    (by
      intro C hC
      exact canonical_assembled_partition_endpoints_retained
        G P W hconn hP hdegree hW C hC)





theorem chosenCorridor_start_retained (S : CoreCorridorChoices G P)
    (c : CoreComponent G P) :
    corridorStart (S.corridor c) ∈ retainedVertices G P := by
  obtain ⟨u, w, hu, hw, huQ, hwQ⟩ := S.endpoints_protected c
  have h : corridorStart (S.corridor c) = u := by
    exact Option.some.inj ((corridorStart_head? (S.corridor c)).symm.trans hu)
  simpa [h] using huQ

theorem chosenCorridor_finish_retained (S : CoreCorridorChoices G P)
    (c : CoreComponent G P) :
    corridorFinish (S.corridor c) ∈ retainedVertices G P := by
  obtain ⟨u, w, hu, hw, huQ, hwQ⟩ := S.endpoints_protected c
  have h : corridorFinish (S.corridor c) = w := by
    exact Option.some.inj ((corridorFinish_getLast? (S.corridor c)).symm.trans hw)
  simpa [h] using hwQ

def coreComponentOf (G : PhysicalGraph) (P : Finset G.Vertex)
    (v : G.Vertex) (hv : v ∉ retainedVertices G P) : CoreComponent G P :=
  (G.toSimpleGraph.induce {x | x ∉ protectedOrBranch G P}).connectedComponentMk
    ⟨v, by simpa [retainedVertices] using hv⟩

theorem mem_coreComponentOf (v : G.Vertex)
    (hv : v ∉ retainedVertices G P) :
    v ∈ componentVertices G P (coreComponentOf G P v hv) := by
  classical
  let x : {x : G.Vertex // x ∉ protectedOrBranch G P} :=
    ⟨v, by simpa [retainedVertices] using hv⟩
  have hx : x ∈ (coreComponentOf G P v hv).supp := by
    exact ((coreComponentOf G P v hv).mem_supp_iff x).mpr rfl
  unfold componentVertices
  apply Finset.mem_map.mpr
  exact ⟨x, Set.mem_toFinset.mpr hx, rfl⟩

theorem coreComponentOf_eq_of_adj {u v : G.Vertex}
    (hu : u ∉ retainedVertices G P) (hv : v ∉ retainedVertices G P)
    (hadj : G.toSimpleGraph.Adj u v) :
    coreComponentOf G P u hu = coreComponentOf G P v hv := by
  let H := G.toSimpleGraph.induce {x | x ∉ protectedOrBranch G P}
  let x : {x : G.Vertex // x ∉ protectedOrBranch G P} :=
    ⟨u, by simpa [retainedVertices] using hu⟩
  let y : {x : G.Vertex // x ∉ protectedOrBranch G P} :=
    ⟨v, by simpa [retainedVertices] using hv⟩
  have hadjH : H.Adj x y := by
    show (G.toSimpleGraph.induce
      {x | x ∉ protectedOrBranch G P}).Adj x y
    exact hadj
  have hreach : H.Reachable x y := hadjH.reachable
  exact SimpleGraph.ConnectedComponent.eq.mpr hreach

def canonicalCorridorFiber
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) :
    G.Vertex → (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree).Vertex := by
  classical
  let S := canonicalCoreCorridorChoices G P hconn hP hdegree
  let Q := retainedVertices G P
  intro v
  by_cases hv : v ∈ Q
  · exact retainedIndex Q hv
  · let c : CoreComponent G P := coreComponentOf G P v hv
    exact retainedIndex Q (chosenCorridor_start_retained S c)

theorem canonicalCorridorFiber_surjective
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) :
    Function.Surjective (canonicalCorridorFiber G P W hW hconn hP hdegree) := by
  classical
  let Q := retainedVertices G P
  intro x
  let q := (Finset.equivFin Q).symm x
  refine ⟨q.1, ?_⟩
  simp [canonicalCorridorFiber, Q, q, retainedIndex]

theorem retainedIndex_eq_iff {Q : Finset G.Vertex}
    {u v : G.Vertex} (hu : u ∈ Q) (hv : v ∈ Q) :
    retainedIndex Q hu = retainedIndex Q hv ↔ u = v := by
  constructor
  · intro h
    have hsub : (⟨u, hu⟩ : {x // x ∈ Q}) = ⟨v, hv⟩ :=
      (Finset.equivFin Q).injective h
    exact congrArg Subtype.val hsub
  · rintro rfl
    rfl

theorem canonicalCorridorFiber_eq_of_adj_outside
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    {u v : G.Vertex} (hu : u ∉ retainedVertices G P)
    (hv : v ∉ retainedVertices G P) (hadj : G.toSimpleGraph.Adj u v) :
    canonicalCorridorFiber G P W hW hconn hP hdegree u =
      canonicalCorridorFiber G P W hW hconn hP hdegree v := by
  have hc := coreComponentOf_eq_of_adj (G := G) (P := P) hu hv hadj
  simp [canonicalCorridorFiber, hu, hv, hc]

private theorem physical_adj_has_edge (G : PhysicalGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) :
    ∃ e : G.Edge,
      (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u) := by
  simpa [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] using h

private theorem corridor_family_has_index (D : CorridorPartition G P W)
    {C : PhysicalCorridor G} (hC : C ∈ D.corridors) :
    ∃ i : Fin (assembledCorridorFamily D).length,
      assembledCorridorAt D i = C := by
  classical
  have hfin : C ∈ D.corridors.toFinset := List.mem_toFinset.mpr hC
  have hlist : C ∈ assembledCorridorFamily D := by
    exact Finset.mem_toList.mpr hfin
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hlist
  exact ⟨i, by simpa [assembledCorridorAt, assembledCorridorFamily] using hi⟩



/-- The simple graph underlying a finite labelled multigraph ignores loops and
forgets edge orientation while retaining parallel-edge adjacency. -/
def finiteMultiUnderlyingGraph (H : FiniteMultiGraph) : SimpleGraph H.Vertex where
  Adj u v := u ≠ v ∧ ∃ e,
    (H.src e = u ∧ H.dst e = v) ∨ (H.src e = v ∧ H.dst e = u)
  symm := by
    intro u v h
    rcases h with ⟨hne, e, hsrc | hdst⟩
    · exact ⟨hne.symm, e, Or.inr hsrc⟩
    · exact ⟨hne.symm, e, Or.inl hdst⟩
  loopless := by
    intro u h
    exact h.1 rfl

private theorem compressed_edge_adj
    (D : CorridorPartition G P W) (Q : Finset G.Vertex)
    (hendpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q)
    (i : Fin (assembledCorridorFamily D).length)
    (hne : (compressedCorridorGraph D Q hendpoint).src i ≠
      (compressedCorridorGraph D Q hendpoint).dst i) :
    (finiteMultiUnderlyingGraph
      (compressedCorridorGraph D Q hendpoint)).Adj
      ((compressedCorridorGraph D Q hendpoint).src i)
      ((compressedCorridorGraph D Q hendpoint).dst i) := by
  exact ⟨hne, i, Or.inl ⟨rfl, rfl⟩⟩

private theorem compressed_edge_endpoints_at
    (D : CorridorPartition G P W) (Q : Finset G.Vertex)
    (hendpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q)
    {C : PhysicalCorridor G} (hC : C ∈ D.corridors)
    (i : Fin (assembledCorridorFamily D).length)
    (hi : assembledCorridorAt D i = C) :
    (compressedCorridorGraph D Q hendpoint).src i =
        retainedIndex Q (hendpoint C hC).1 ∧
      (compressedCorridorGraph D Q hendpoint).dst i =
        retainedIndex Q (hendpoint C hC).2 := by
  constructor <;> simp [compressedCorridorGraph, hi]

private theorem singleton_corridor_mem_assembled
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    {e : G.Edge} (hs : G.src e ∈ retainedVertices G P)
    (ht : G.dst e ∈ retainedVertices G P) :
    singletonCorridor G e ∈
      (assembledPartition G P W hW hconn hP hdegree).corridors := by
  classical
  have he : e ∈ protectedProtectedEdges G P := by
    exact (protectedProtectedEdges_mem G P e).2 ⟨hs, ht⟩
  change singletonCorridor G e ∈
    (assembleCorridorPartition G P W hW
      ((canonicalCoreCorridorChoices G P hconn hP hdegree).toSystem G P)).corridors
  exact List.mem_append.mpr <| Or.inr <| List.mem_map.mpr
    ⟨e, Finset.mem_toList.mpr he, rfl⟩

private theorem compressed_adj_of_singleton_edge
    (D : CorridorPartition G P W) (Q : Finset G.Vertex)
    (hendpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q)
    {e : G.Edge} {u v : G.Vertex}
    (hu : u ∈ Q) (hv : v ∈ Q)
    (hlabels : (G.src e = u ∧ G.dst e = v) ∨
      (G.src e = v ∧ G.dst e = u))
    (hC : singletonCorridor G e ∈ D.corridors) :
    (finiteMultiUnderlyingGraph (compressedCorridorGraph D Q hendpoint)).Adj
      (retainedIndex Q hu) (retainedIndex Q hv) := by
  classical
  have hidx := corridor_family_has_index D hC
  obtain ⟨i, hi⟩ := hidx
  have hends := compressed_edge_endpoints_at D Q hendpoint hC i hi
  have hsC : corridorStart (singletonCorridor G e) = G.src e := by
    simp [corridorStart, singletonCorridor]
  have htC : corridorFinish (singletonCorridor G e) = G.dst e := by
    simp [corridorFinish, singletonCorridor]
  rcases hlabels with ⟨hs, ht⟩ | ⟨ht, hs⟩
  · have hsidx : (compressedCorridorGraph D Q hendpoint).src i =
        retainedIndex Q hu := by
      rw [hends.1]
      exact (retainedIndex_eq_iff _ _).2 (hsC.trans hs)
    have htidx : (compressedCorridorGraph D Q hendpoint).dst i =
        retainedIndex Q hv := by
      rw [hends.2]
      exact (retainedIndex_eq_iff _ _).2 (htC.trans ht)
    have hneq : (compressedCorridorGraph D Q hendpoint).src i ≠
        (compressedCorridorGraph D Q hendpoint).dst i := by
      intro h
      have huv : u = v := (retainedIndex_eq_iff hu hv).mp (by
        rw [← hsidx, ← htidx]
        exact h)
      exact G.noLoops e (by rw [hs, ht, huv])
    have hadj := compressed_edge_adj D Q hendpoint i hneq
    simpa [hsidx, htidx] using hadj
  · have hsidx : (compressedCorridorGraph D Q hendpoint).src i =
        retainedIndex Q hv := by
      rw [hends.1]
      exact (retainedIndex_eq_iff _ _).2 (hsC.trans ht)
    have htidx : (compressedCorridorGraph D Q hendpoint).dst i =
        retainedIndex Q hu := by
      rw [hends.2]
      exact (retainedIndex_eq_iff _ _).2 (htC.trans hs)
    have hneq : (compressedCorridorGraph D Q hendpoint).src i ≠
        (compressedCorridorGraph D Q hendpoint).dst i := by
      intro h
      have hvu : v = u := (retainedIndex_eq_iff hv hu).mp (by
        rw [← hsidx, ← htidx]
        exact h)
      exact G.noLoops e (by rw [hs, ht, hvu.symm])
    have hadj := compressed_edge_adj D Q hendpoint i hneq
    simpa [hsidx, htidx] using hadj.symm

private theorem canonical_fiber_step_retained_core
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    {u q : G.Vertex} (hu : u ∉ retainedVertices G P)
    (hq : q ∈ retainedVertices G P)
    {e : G.Edge} (hlabels : (G.src e = u ∧ G.dst e = q) ∨
      (G.src e = q ∧ G.dst e = u)) :
    canonicalCorridorFiber G P W hW hconn hP hdegree u =
        canonicalCorridorFiber G P W hW hconn hP hdegree q ∨
      (finiteMultiUnderlyingGraph
        (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj
        (canonicalCorridorFiber G P W hW hconn hP hdegree u)
        (canonicalCorridorFiber G P W hW hconn hP hdegree q) := by
  classical
  let Q := retainedVertices G P
  let S := canonicalCoreCorridorChoices G P hconn hP hdegree
  let D := assembledPartition G P W hW hconn hP hdegree
  let endpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q := by
    intro C hC
    simpa [D, assembledPartition] using
      (canonical_assembled_partition_endpoints_retained
        G P W hconn hP hdegree hW C (by simpa [D, assembledPartition] using hC))
  let c := coreComponentOf G P u hu
  let C := S.corridor c
  have huC : u ∈ componentVertices G P c := mem_coreComponentOf u hu
  have heC : e ∈ C.support := by
    rcases hlabels with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact S.incident_edge_cover c e (Or.inl (hs ▸ huC))
    · exact S.incident_edge_cover c e (Or.inr (ht ▸ huC))
  have hC : C ∈ D.corridors := by
    change C ∈ (S.toSystem G P).corridors ++
      (protectedProtectedEdges G P).toList.map (singletonCorridor G)
    apply List.mem_append.mpr
    left
    change S.corridor c ∈ Finset.univ.toList.map S.corridor
    exact List.mem_map.mpr ⟨c, Finset.mem_toList.mpr (Finset.mem_univ c), rfl⟩
  obtain ⟨i, hi⟩ := corridor_family_has_index D hC
  have hends := compressed_edge_endpoints_at D Q endpoint hC i hi
  have hstartQ : corridorStart C ∈ Q := chosenCorridor_start_retained S c
  have hfinishQ : corridorFinish C ∈ Q := chosenCorridor_finish_retained S c
  have hstartFiber : canonicalCorridorFiber G P W hW hconn hP hdegree u =
      retainedIndex Q hstartQ := by
    simp [canonicalCorridorFiber, hu, coreComponentOf, C, S, Q]
  have hqFiber : canonicalCorridorFiber G P W hW hconn hP hdegree q =
      retainedIndex Q hq := by
    simp [canonicalCorridorFiber, hq, Q]
  have hsrcFiber : (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree).src i =
      retainedIndex Q hstartQ := by
    change (compressedCorridorGraph D Q endpoint).src i = _
    rw [hends.1]
  have hdstFiber : (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree).dst i =
      retainedIndex Q hfinishQ := by
    change (compressedCorridorGraph D Q endpoint).dst i = _
    rw [hends.2]
  have hqEndpoint : q = corridorStart C ∨ q = corridorFinish C := by
    rcases hlabels with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have h := (S.protected_support_endpoints c e heC).2 (ht ▸ hq)
      rcases h with h | h
      · exact Or.inl (ht.symm.trans h)
      · exact Or.inr (ht.symm.trans h)
    · have h := (S.protected_support_endpoints c e heC).1 (hs ▸ hq)
      rcases h with h | h
      · exact Or.inl (hs.symm.trans h)
      · exact Or.inr (hs.symm.trans h)
  rcases hqEndpoint with hqStart | hqFinish
  · left
    rw [hstartFiber, hqFiber]
    exact (retainedIndex_eq_iff hstartQ hq).2 hqStart.symm
  · by_cases hloop : corridorStart C = corridorFinish C
    · left
      rw [hstartFiber, hqFiber]
      exact (retainedIndex_eq_iff hstartQ hq).2 (hloop.trans hqFinish.symm)
    · right
      have hneq : (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree).src i ≠
          (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree).dst i := by
        rw [hsrcFiber, hdstFiber]
        intro h
        exact hloop ((retainedIndex_eq_iff hstartQ hfinishQ).mp h)
      have hadj := compressed_edge_adj D Q endpoint i hneq
      change (finiteMultiUnderlyingGraph
        (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj
        _ _ at hadj
      have hadjCore : (finiteMultiUnderlyingGraph
          (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj
          (retainedIndex Q hstartQ) (retainedIndex Q hfinishQ) := by
        rw [← hsrcFiber, ← hdstFiber]
        exact hadj
      have hfinishEq : retainedIndex Q hfinishQ = retainedIndex Q hq :=
        (retainedIndex_eq_iff hfinishQ hq).2 hqFinish.symm
      rw [hstartFiber, hqFiber]
      simpa [hfinishEq] using hadjCore

theorem canonicalCorridorFiber_respects_adjacency
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    {u v : G.Vertex} (hadj : G.toSimpleGraph.Adj u v) :
    canonicalCorridorFiber G P W hW hconn hP hdegree u =
      canonicalCorridorFiber G P W hW hconn hP hdegree v ∨
    (finiteMultiUnderlyingGraph
      (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj
      (canonicalCorridorFiber G P W hW hconn hP hdegree u)
      (canonicalCorridorFiber G P W hW hconn hP hdegree v) := by
  classical
  let Q := retainedVertices G P
  let D := assembledPartition G P W hW hconn hP hdegree
  let endpoint : ∀ C, C ∈ D.corridors →
      corridorStart C ∈ Q ∧ corridorFinish C ∈ Q := by
    intro C hC
    simpa [D, assembledPartition] using
      (canonical_assembled_partition_endpoints_retained
        G P W hconn hP hdegree hW C (by simpa [D, assembledPartition] using hC))
  by_cases hu : u ∈ Q <;> by_cases hv : v ∈ Q
  · obtain ⟨e, hlabels⟩ := physical_adj_has_edge G hadj
    have hC : singletonCorridor G e ∈
        (assembledPartition G P W hW hconn hP hdegree).corridors := by
      rcases hlabels with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact singleton_corridor_mem_assembled G P W hW hconn hP hdegree
          (e := e) (hs ▸ hu) (ht ▸ hv)
      · exact singleton_corridor_mem_assembled G P W hW hconn hP hdegree
          (e := e) (hs ▸ hv) (ht ▸ hu)
    have hC' : singletonCorridor G e ∈ D.corridors := by
      simpa [D, assembledPartition] using hC
    have hresult := compressed_adj_of_singleton_edge D Q endpoint hu hv hlabels hC'
    change (finiteMultiUnderlyingGraph
      (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj _ _ at hresult
    right
    simpa [canonicalCorridorFiber, hu, hv, D, Q] using hresult
  · obtain ⟨e, hlabels⟩ := physical_adj_has_edge G hadj
    have hlabels' : (G.src e = v ∧ G.dst e = u) ∨
        (G.src e = u ∧ G.dst e = v) := by
      rcases hlabels with ⟨hsu, htv⟩ | ⟨hsv, htu⟩
      · exact Or.inr ⟨hsu, htv⟩
      · exact Or.inl ⟨hsv, htu⟩
    have hresult := canonical_fiber_step_retained_core G P W hW hconn hP hdegree
      hv hu hlabels'
    rcases hresult with heq | hadj'
    · exact Or.inl heq.symm
    · exact Or.inr hadj'.symm
  · obtain ⟨e, hlabels⟩ := physical_adj_has_edge G hadj
    exact canonical_fiber_step_retained_core G P W hW hconn hP hdegree hu hv hlabels
  · exact Or.inl (canonicalCorridorFiber_eq_of_adj_outside
      G P W hW hconn hP hdegree hu hv hadj)

/-- Connectedness descends along a surjective vertex map when each original
edge either collapses to one vertex or maps to an edge of the target graph. -/
theorem SimpleGraph.connected_of_surjective_step
    {α β : Type*} (J : SimpleGraph α) (K : SimpleGraph β)
    (f : α → β) (hsurj : Function.Surjective f)
    (hstep : ∀ ⦃u v⦄, J.Adj u v → f u = f v ∨ K.Adj (f u) (f v))
    (hconn : J.Connected) : K.Connected := by
  classical
  letI : Nonempty β := ⟨f (Classical.choice hconn.nonempty)⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  obtain ⟨p⟩ := hconn.preconnected u v
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab tail ih =>
      have hhead : K.Reachable (f a) (f b) := by
        rcases hstep hab with heq | hadj
        · rw [heq]
        · exact hadj.reachable
      exact hhead.trans ih



/-- The corridor compression of the assembled partition is connected. -/
theorem canonicalCompressedCorridorGraph_connected
    (G : PhysicalGraph) (P : Finset G.Vertex) (W : Finset G.Edge)
    (hW : ∀ e ∈ W, G.src e ∈ P ∧ G.dst e ∈ P)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3) :
    (finiteMultiUnderlyingGraph
      (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Connected := by
  classical
  let f := canonicalCorridorFiber G P W hW hconn hP hdegree
  have hsurj : Function.Surjective f := by
    exact canonicalCorridorFiber_surjective G P W hW hconn hP hdegree
  have hstep : ∀ ⦃u v⦄, G.toSimpleGraph.Adj u v →
      f u = f v ∨
        (finiteMultiUnderlyingGraph
          (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)).Adj
          (f u) (f v) := by
    intro u v hadj
    exact canonicalCorridorFiber_respects_adjacency
      G P W hW hconn hP hdegree hadj
  exact SimpleGraph.connected_of_surjective_step G.toSimpleGraph
    (finiteMultiUnderlyingGraph
      (canonicalCompressedCorridorGraph G P W hW hconn hP hdegree)) f
    hsurj hstep hconn

end Erdos1016.Proof.AssembledCorridorCompression

end

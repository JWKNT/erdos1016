import Erdos1016.Graph.Multigraph.ConnectedContraction
import Erdos1016.Graph.Multigraph.RegionDegrees
import Erdos1016.Graph.Multigraph.SubcubicOrder
import Erdos1016.Graph.Multigraph.ForestCharacterization

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Localization of a multigraph region

The projection used for localization must retain loops in the region.
This module first extends connected contraction to retain selected loop
labels. The existing contraction and its shared imports remain unchanged.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.FiniteMultiGraph.RegionLocalization
open BoundaryTrace

local instance localizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- An underlying simple-graph walk never selects a physical loop. -/
theorem walkWord_loop_eq_zero (G : FiniteMultiGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) (e : G.Edge) (he : G.src e = G.dst e) :
    G.walkWord p e = 0 := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      have hne : e ≠ G.edgeForAdj hab := by
        intro hh
        have hloop : G.src (G.edgeForAdj hab) = G.dst (G.edgeForAdj hab) := hh ▸ he
        rcases G.edgeForAdj_endpoints hab with ht | ht
        · exact hab.1 (ht.1.symm.trans (hloop.trans ht.2))
        · exact hab.1 (ht.2.symm.trans (hloop.symm.trans ht.1))
      rw [walkWord]
      change (Pi.single (G.edgeForAdj hab) (1 : F₂) : G.EdgeWord) e + _ = 0
      simp [Pi.single_apply, hne, ih]

/-- The sum of all binary boundary equations is zero, including physical loops. -/
theorem sum_boundary_eq_zero (G : FiniteMultiGraph) (x : G.EdgeWord) :
    (∑ v, G.boundary x v) = 0 := by
  have hh := ConnectedContraction.fiberSum_boundary G (fun _ => ()) x ()
  simpa [ConnectedContraction.fiberSum, bit_add_self] using hh

namespace LoopPreservingContraction

variable (G : FiniteMultiGraph) {Q : Type*} [Fintype Q]
  (fiber : G.Vertex → Q) (L : Finset G.Edge)

/-- Keep all crossing labels, and also the designated physical loop labels. -/
abbrev RetainedEdge := {e : G.Edge // fiber (G.src e) ≠ fiber (G.dst e) ∨ e ∈ L}

def vertexEquiv : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

def edgeEquiv : RetainedEdge G fiber L ≃ Fin (Fintype.card (RetainedEdge G fiber L)) :=
  Fintype.equivFin _

def quotient : FiniteMultiGraph where
  vertexCount := Fintype.card Q
  edgeCount := Fintype.card (RetainedEdge G fiber L)
  src e := vertexEquiv (fiber (G.src ((edgeEquiv G fiber L).symm e).1))
  dst e := vertexEquiv (fiber (G.dst ((edgeEquiv G fiber L).symm e).1))

def projectWord : G.EdgeWord →ₗ[F₂] (quotient G fiber L).EdgeWord where
  toFun x e := x ((edgeEquiv G fiber L).symm e).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient boundary equals the sum of the original boundary in each fiber. -/
theorem boundary_projectWord (x : G.EdgeWord) (q : Q) :
    (quotient G fiber L).boundary (projectWord G fiber L x) (vertexEquiv q) =
      ConnectedContraction.fiberSum G fiber (G.boundary x) q := by
  rw [ConnectedContraction.fiberSum_boundary]
  let term : G.Edge → F₂ := fun e =>
    (if fiber (G.src e) = q then x e else 0) +
    (if fiber (G.dst e) = q then x e else 0)
  have hremoved :
      (∑ e : {e : G.Edge // ¬ (fiber (G.src e) ≠ fiber (G.dst e) ∨ e ∈ L)}, term e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hs : fiber (G.src e.1) = fiber (G.dst e.1) := by
      by_contra hh
      exact e.2 (Or.inl hh)
    simp [term, hs, bit_add_self]
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun e : G.Edge => fiber (G.src e) ≠ fiber (G.dst e) ∨ e ∈ L) term
  rw [hremoved, add_zero] at hsum
  calc
    _ = ∑ e : RetainedEdge G fiber L, term e.1 := by
      change (∑ e : (quotient G fiber L).Edge, _) = _
      apply Fintype.sum_equiv (edgeEquiv G fiber L).symm
      intro e
      simp [quotient, projectWord, term]
    _ = _ := hsum

/-- Project an actual even word, retaining the chosen loop coordinates. -/
def project : G.CycleSpace →ₗ[F₂] (quotient G fiber L).CycleSpace where
  toFun x := ⟨projectWord G fiber L x.1, by
    rw [LinearMap.mem_ker]
    funext q
    obtain ⟨q, rfl⟩ := vertexEquiv.surjective q
    rw [boundary_projectWord]
    have hx : G.boundary x.1 = 0 := x.2
    simp [hx, ConnectedContraction.fiberSum]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend target coordinates by zero on omitted physical labels. -/
def extendWord (y : (quotient G fiber L).EdgeWord) : G.EdgeWord :=
  fun e => if h : fiber (G.src e) ≠ fiber (G.dst e) ∨ e ∈ L
    then y (edgeEquiv G fiber L ⟨e, h⟩) else 0

@[simp] theorem projectWord_extendWord (y : (quotient G fiber L).EdgeWord) :
    projectWord G fiber L (extendWord G fiber L y) = y := by
  funext e
  simp [projectWord, extendWord, ((edgeEquiv G fiber L).symm e).2]

/-- Boundary repair uses neither crossing coordinates nor any physical loop. -/
theorem projectWord_repairWord
    (hL : ∀ e ∈ L, G.src e = G.dst e)
    (h : ConnectedContraction.ConnectedFibers G fiber) (b : G.Demand) :
    projectWord G fiber L (ConnectedContraction.repairWord G fiber h b) = 0 := by
  funext e
  let a := (edgeEquiv G fiber L).symm e
  change ConnectedContraction.repairWord G fiber h b a.1 = 0
  rcases a.2 with ha | ha
  · have hz := congrFun (ConnectedContraction.projectWord_repairWord G fiber h b)
      (ConnectedContraction.edgeEquiv G fiber ⟨a.1, ha⟩)
    simpa [ConnectedContraction.projectWord] using hz
  · unfold ConnectedContraction.repairWord
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro v hv
    rw [walkWord_loop_eq_zero G _ a.1 (hL a.1 ha), smul_zero]

/-- Connected fibers allow every quotient even word, with all retained loops. -/
theorem project_surjective
    (hL : ∀ e ∈ L, G.src e = G.dst e)
    (h : ConnectedContraction.ConnectedFibers G fiber) :
    Function.Surjective (project G fiber L) := by
  intro y
  let x := extendWord G fiber L y.1
  let b := G.boundary x
  have hb : ∀ q, ConnectedContraction.fiberSum G fiber b q = 0 := by
    intro q
    rw [← boundary_projectWord]
    change (quotient G fiber L).boundary
      (projectWord G fiber L (extendWord G fiber L y.1)) _ = 0
    rw [projectWord_extendWord]
    exact congrFun y.2 _
  have heven : G.boundary (x + ConnectedContraction.repairWord G fiber h b) = 0 := by
    rw [map_add, ConnectedContraction.boundary_repairWord G fiber h b hb]
    exact word_add_self b
  refine ⟨⟨x + ConnectedContraction.repairWord G fiber h b, heven⟩, ?_⟩
  apply Subtype.ext
  change projectWord G fiber L (x + ConnectedContraction.repairWord G fiber h b) = y.1
  rw [map_add, projectWord_repairWord G fiber L hL h b, add_zero]
  exact projectWord_extendWord G fiber L y.1

/-- Every event on the retained quotient has its exact uniform law. -/
theorem density_project
    (hL : ∀ e ∈ L, G.src e = G.dst e)
    (h : ConnectedContraction.ConnectedFibers G fiber)
    (P : (quotient G fiber L).CycleSpace → Prop) :
    Finite.density (fun x : G.CycleSpace => P (project G fiber L x)) = Finite.density P :=
  density_surjective_linear (project G fiber L) (project_surjective G fiber L hL h) P

/-- A source walk projects to quotient reachability; internal steps vanish. -/
theorem reachable_of_walk {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) :
    (quotient G fiber L).toSimpleGraph.Reachable (vertexEquiv (fiber u))
      (vertexEquiv (fiber v)) := by
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
      have hstep : (quotient G fiber L).toSimpleGraph.Reachable
          (vertexEquiv (fiber a)) (vertexEquiv (fiber b)) := by
        by_cases hsame : fiber a = fiber b
        · rw [hsame]
        · obtain ⟨e, he⟩ := hab.2
          have hcross : fiber (G.src e) ≠ fiber (G.dst e) := by
            rcases he with h | h
            · simpa only [h.1, h.2] using hsame
            · simpa only [h.1, h.2] using Ne.symm hsame
          apply SimpleGraph.Adj.reachable
          refine ⟨fun heq => hsame (vertexEquiv.injective heq), edgeEquiv G fiber L ⟨e, Or.inl hcross⟩, ?_⟩
          rcases he with h | h
          · left
            simp [quotient, h.1, h.2]
          · right
            simp [quotient, h.1, h.2]
      exact hstep.trans ih

/-- Contracting nonempty connected fibers preserves source connectedness. -/
theorem quotient_connected (hG : G.toSimpleGraph.Connected)
    (h : ConnectedContraction.ConnectedFibers G fiber) : (quotient G fiber L).toSimpleGraph.Connected := by
  letI : Nonempty (quotient G fiber L).Vertex := by
    obtain ⟨v⟩ := hG.nonempty
    exact ⟨vertexEquiv (fiber v)⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨qa, rfl⟩ := vertexEquiv.surjective a
  obtain ⟨qb, rfl⟩ := vertexEquiv.surjective b
  obtain ⟨p⟩ := hG.preconnected (ConnectedContraction.fiberRoot G fiber h qa).1 (ConnectedContraction.fiberRoot G fiber h qb).1
  have hp := reachable_of_walk G fiber L p
  simpa only [(ConnectedContraction.fiberRoot G fiber h qa).2, (ConnectedContraction.fiberRoot G fiber h qb).2] using hp

end LoopPreservingContraction

namespace OutsideContraction

variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

abbrev RegionVertex := {v : G.Vertex // v ∈ X}
abbrev QuotientVertex := Option (RegionVertex G X)

/-- Each region vertex is a singleton fiber; the outside is one fiber. -/
def fiber (v : G.Vertex) : QuotientVertex G X :=
  if hv : v ∈ X then some ⟨v, hv⟩ else none

@[simp] theorem fiber_eq_none_iff (v : G.Vertex) :
    fiber G X v = none ↔ v ∉ X := by
  by_cases hv : v ∈ X <;> simp [fiber, hv]

@[simp] theorem fiber_eq_some_iff (v : G.Vertex) (a : RegionVertex G X) :
    fiber G X v = some a ↔ v = a.1 := by
  by_cases hv : v ∈ X
  · simp [fiber, hv, Subtype.ext_iff]
  · have hne : v ≠ a.1 := by intro hh; exact hv (hh ▸ a.2)
    simp [fiber, hv, hne]

/-- The original loops inside the region are retained as physical labels. -/
def keptLoops : Finset G.Edge :=
  Finset.univ.filter fun e => G.src e = G.dst e ∧ G.src e ∈ X

theorem keptLoops_are_loops : ∀ e ∈ keptLoops G X, G.src e = G.dst e := by
  intro e he
  exact (Finset.mem_filter.mp he).2.1

/-- Precisely the edges touching X survive this quotient, including loops. -/
theorem retained_iff (e : G.Edge) :
    (fiber G X (G.src e) ≠ fiber G X (G.dst e) ∨ e ∈ keptLoops G X) ↔
      G.src e ∈ X ∨ G.dst e ∈ X := by
  by_cases hs : G.src e ∈ X <;> by_cases ht : G.dst e ∈ X
  · simp only [fiber, hs, ht, ↓reduceDIte, ne_eq, Option.some.injEq,
      Subtype.mk.injEq, keptLoops, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true, or_true]
    tauto
  · simp [fiber, hs, ht, keptLoops]
  · simp [fiber, hs, ht, keptLoops]
  · simp [fiber, hs, ht, keptLoops]

/-- No connectivity of the region itself is required. -/
theorem connectedFibers
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) :
    ConnectedContraction.ConnectedFibers G (fiber G X) := by
  intro q
  cases q with
  | none =>
      have heq : {v : G.Vertex | fiber G X v = none} = (↑(Xᶜ) : Set G.Vertex) := by
        ext v
        simp
      change (G.toSimpleGraph.induce {v : G.Vertex | fiber G X v = none}).Connected
      rw [heq]
      exact houtside
  | some a =>
      let a' : {v : G.Vertex // fiber G X v = some a} := ⟨a.1, by simp⟩
      refine { nonempty := ⟨a'⟩, preconnected := ?_ }
      intro u v
      have hu : u.1 = a.1 := (fiber_eq_some_iff G X u.1 a).mp u.2
      have hv : v.1 = a.1 := (fiber_eq_some_iff G X v.1 a).mp v.2
      have huv : u = v := Subtype.ext (hu.trans hv.symm)
      subst v
      exact SimpleGraph.Reachable.refl _

abbrev quotient : FiniteMultiGraph :=
  LoopPreservingContraction.quotient G (fiber G X) (keptLoops G X)

abbrev project : G.CycleSpace →ₗ[F₂] (quotient G X).CycleSpace :=
  LoopPreservingContraction.project G (fiber G X) (keptLoops G X)

theorem project_surjective
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) :
    Function.Surjective (project G X) :=
  LoopPreservingContraction.project_surjective G (fiber G X) (keptLoops G X)
    (keptLoops_are_loops G X) (connectedFibers G X houtside)

theorem density_project
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected)
    (P : (quotient G X).CycleSpace → Prop) :
    Finite.density (fun z : G.CycleSpace => P (project G X z)) = Finite.density P :=
  BoundaryTrace.density_surjective_linear (project G X) (project_surjective G X houtside) P

theorem quotient_connected (hG : G.toSimpleGraph.Connected)
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) :
    (quotient G X).toSimpleGraph.Connected :=
  LoopPreservingContraction.quotient_connected G (fiber G X) (keptLoops G X)
    hG (connectedFibers G X houtside)

/-- Vanishing boundary inside the region implies vanishing boundary on the hub quotient. -/
theorem fiberSum_boundary_zero (x : G.EdgeWord)
    (hx : ∀ v ∈ X, G.boundary x v = 0) (q : QuotientVertex G X) :
    ConnectedContraction.fiberSum G (fiber G X) (G.boundary x) q = 0 := by
  cases q with
  | some a =>
      simp only [ConnectedContraction.fiberSum, fiber_eq_some_iff]
      simpa using hx a.1 a.2
  | none =>
      have hp (v : G.Vertex) :
          (if fiber G X v = none then G.boundary x v else 0) = G.boundary x v := by
        by_cases hv : v ∈ X
        · simp [fiber, hv, hx v hv]
        · simp [fiber, hv]
      calc
        _ = ∑ v, G.boundary x v := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hh : fiber G X v = none
          · simp only [hh, if_true]
          · simpa only [hh, if_false] using hp v
        _ = 0 := sum_boundary_eq_zero G x

end OutsideContraction

namespace CycleCap

variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

abbrev OldVertex := {v : G.Vertex // v ∈ X}
abbrev InternalEdge := {e : G.Edge // e ∈ G.internalEdges X}
abbrev BoundaryEdge := {e : G.Edge // e ∈ G.cutEdges X}

def capSize : ℕ := max (Fintype.card (BoundaryEdge G X)) 3

theorem capSize_ge_three : 3 ≤ capSize G X := Nat.le_max_right _ _
theorem capSize_pos : 0 < capSize G X := by have := capSize_ge_three G X; omega

abbrev VertexLabel := OldVertex G X ⊕ Fin (capSize G X)
abbrev EdgeLabel := InternalEdge G X ⊕ (BoundaryEdge G X ⊕ Fin (capSize G X))

def vertexEquiv : VertexLabel G X ≃ Fin (Fintype.card (VertexLabel G X)) := Fintype.equivFin _
def edgeEquiv : EdgeLabel G X ≃ Fin (Fintype.card (EdgeLabel G X)) := Fintype.equivFin _

theorem internal_src_mem (e : InternalEdge G X) : G.src e.1 ∈ X :=
  (Finset.mem_filter.mp e.2).2.1

theorem internal_dst_mem (e : InternalEdge G X) : G.dst e.1 ∈ X :=
  (Finset.mem_filter.mp e.2).2.2

/-- The endpoint of a cut edge that lies in the retained region. -/
def insideEnd (e : BoundaryEdge G X) : OldVertex G X :=
  if hs : G.src e.1 ∈ X then ⟨G.src e.1, hs⟩
  else ⟨G.dst e.1, by
    have hh := (Finset.mem_filter.mp e.2).2
    rcases hh with hh | hh
    · exact (hs hh.1).elim
    · exact hh.2⟩

def spokeIndex (e : BoundaryEdge G X) : Fin (capSize G X) :=
  ⟨(Fintype.equivFin (BoundaryEdge G X) e).1,
    lt_of_lt_of_le (Fintype.equivFin (BoundaryEdge G X) e).2 (Nat.le_max_left _ _)⟩

theorem spokeIndex_injective : Function.Injective (spokeIndex G X) := by
  intro a b hab
  apply (Fintype.equivFin (BoundaryEdge G X)).injective
  apply Fin.ext
  exact congrArg (fun i : Fin (capSize G X) => i.val) hab

def next (i : Fin (capSize G X)) : Fin (capSize G X) :=
  ⟨(i.1 + 1) % capSize G X, Nat.mod_lt _ (capSize_pos G X)⟩

def source : EdgeLabel G X → VertexLabel G X
  | Sum.inl e => Sum.inl ⟨G.src e.1, internal_src_mem G X e⟩
  | Sum.inr (Sum.inl e) => Sum.inl (insideEnd G X e)
  | Sum.inr (Sum.inr i) => Sum.inr i

def target : EdgeLabel G X → VertexLabel G X
  | Sum.inl e => Sum.inl ⟨G.dst e.1, internal_dst_mem G X e⟩
  | Sum.inr (Sum.inl e) => Sum.inr (spokeIndex G X e)
  | Sum.inr (Sum.inr i) => Sum.inr (next G X i)

/-- The actual localized multigraph, with a cap cycle of at least three edges. -/
def graph : FiniteMultiGraph where
  vertexCount := Fintype.card (VertexLabel G X)
  edgeCount := Fintype.card (EdgeLabel G X)
  src e := vertexEquiv G X (source G X ((edgeEquiv G X).symm e))
  dst e := vertexEquiv G X (target G X ((edgeEquiv G X).symm e))

@[simp] theorem graph_src (e : EdgeLabel G X) :
    (graph G X).src (edgeEquiv G X e) = vertexEquiv G X (source G X e) := by simp [graph]

@[simp] theorem graph_dst (e : EdgeLabel G X) :
    (graph G X).dst (edgeEquiv G X e) = vertexEquiv G X (target G X e) := by simp [graph]

@[simp] theorem graph_vertexCount : (graph G X).vertexCount = X.card + capSize G X := by
  simp [graph, VertexLabel, OldVertex]

@[simp] theorem graph_edgeCount :
    (graph G X).edgeCount = (G.internalEdges X).card + (G.cutEdges X).card + capSize G X := by
  simp [graph, EdgeLabel, InternalEdge, BoundaryEdge, Nat.add_assoc]

def oldVertex (v : OldVertex G X) : (graph G X).Vertex := vertexEquiv G X (Sum.inl v)
def capVertex (i : Fin (capSize G X)) : (graph G X).Vertex := vertexEquiv G X (Sum.inr i)
def zeroIndex : Fin (capSize G X) := ⟨0, capSize_pos G X⟩

/-- A physical edge always joins reachable vertices, even if it is a loop. -/
theorem label_reachable (e : EdgeLabel G X) :
    (graph G X).toSimpleGraph.Reachable
      (vertexEquiv G X (source G X e)) (vertexEquiv G X (target G X e)) := by
  by_cases hh : vertexEquiv G X (source G X e) = vertexEquiv G X (target G X e)
  · rw [hh]
  · exact SimpleGraph.Adj.reachable ⟨hh, edgeEquiv G X e, Or.inl ⟨graph_src G X e, graph_dst G X e⟩⟩

/-- The padded cap cycle connects all of its vertices. -/
theorem cap_reachable (i j : Fin (capSize G X)) :
    (graph G X).toSimpleGraph.Reachable (capVertex G X i) (capVertex G X j) := by
  have hzero : ∀ k (hk : k < capSize G X),
      (graph G X).toSimpleGraph.Reachable (capVertex G X (zeroIndex G X))
        (capVertex G X ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        intro hk
        have hk' : k < capSize G X := by omega
        have he := label_reachable G X (Sum.inr (Sum.inr ⟨k, hk'⟩))
        have hn : next G X ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hk
        change (graph G X).toSimpleGraph.Reachable (capVertex G X ⟨k, hk'⟩)
          (capVertex G X (next G X ⟨k, hk'⟩)) at he
        rw [hn] at he
        exact (ih hk').trans he
  exact (hzero i.1 i.2).symm.trans (hzero j.1 j.2)


/-- Map all original outside vertices to one cap vertex. -/
def vertexImage (v : G.Vertex) : (graph G X).Vertex :=
  if hv : v ∈ X then oldVertex G X ⟨v, hv⟩ else capVertex G X (zeroIndex G X)

theorem edge_image_reachable (e : G.Edge) :
    (graph G X).toSimpleGraph.Reachable (vertexImage G X (G.src e))
      (vertexImage G X (G.dst e)) := by
  by_cases hs : G.src e ∈ X <;> by_cases ht : G.dst e ∈ X
  · let a : InternalEdge G X := ⟨e, by simp [internalEdges, hs, ht]⟩
    simpa [vertexImage, oldVertex, source, target, hs, ht, a] using
      label_reachable G X (Sum.inl a)
  · let a : BoundaryEdge G X := ⟨e, by simp [cutEdges, hs, ht]⟩
    have hfirst := label_reachable G X (Sum.inr (Sum.inl a))
    have hlast := cap_reachable G X (spokeIndex G X a) (zeroIndex G X)
    have hfirst' : (graph G X).toSimpleGraph.Reachable
        (oldVertex G X ⟨G.src e, hs⟩) (capVertex G X (spokeIndex G X a)) := by
      simpa [source, target, insideEnd, oldVertex, capVertex, a, hs] using hfirst
    simpa [vertexImage, hs, ht] using hfirst'.trans hlast
  · let a : BoundaryEdge G X := ⟨e, by simp [cutEdges, hs, ht]⟩
    have hfirst := label_reachable G X (Sum.inr (Sum.inl a))
    have hlast := cap_reachable G X (spokeIndex G X a) (zeroIndex G X)
    have hfirst' : (graph G X).toSimpleGraph.Reachable
        (oldVertex G X ⟨G.dst e, ht⟩) (capVertex G X (spokeIndex G X a)) := by
      simpa [source, target, insideEnd, oldVertex, capVertex, a, hs] using hfirst
    simpa [vertexImage, hs, ht] using (hfirst'.trans hlast).symm
  · simp only [vertexImage, hs, ht, ↓reduceDIte]
    exact SimpleGraph.Reachable.refl _

theorem walk_image_reachable {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) :
    (graph G X).toSimpleGraph.Reachable (vertexImage G X u) (vertexImage G X v) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
      obtain ⟨e, he⟩ := hab.2
      have hh : (graph G X).toSimpleGraph.Reachable (vertexImage G X a) (vertexImage G X b) := by
        rcases he with he | he
        · simpa [he.1, he.2] using edge_image_reachable G X e
        · simpa [he.1, he.2] using (edge_image_reachable G X e).symm
      exact hh.trans ih

/-- A connected ambient graph gives a connected cap, even for disconnected X. -/
theorem graph_connected (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ) :
    (graph G X).toSimpleGraph.Connected := by
  have hex : ∃ v : G.Vertex, v ∉ X := by
    by_contra hh
    apply hproper
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    exact hh ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  have hroot : ∀ a : (graph G X).Vertex,
      (graph G X).toSimpleGraph.Reachable a (capVertex G X (zeroIndex G X)) := by
    intro a
    obtain ⟨a, rfl⟩ := (vertexEquiv G X).surjective a
    cases a with
    | inl a =>
        obtain ⟨p⟩ := hG.preconnected a.1 v
        simpa [vertexImage, oldVertex, a.2, hv] using walk_image_reachable G X p
    | inr i => exact cap_reachable G X i (zeroIndex G X)
  refine { nonempty := ⟨capVertex G X (zeroIndex G X)⟩, preconnected := ?_ }
  intro a b
  exact (hroot a).trans (hroot b).symm

/-- The rank ledger is independent of the number of components of X. -/
theorem rank_ledger (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ) :
    (graph G X).cycleRank + X.card = (G.internalEdges X).card + (G.cutEdges X).card + 1 := by
  have he := (graph G X).connected_euler (graph_connected G X hG hproper)
  rw [graph_vertexCount, graph_edgeCount] at he
  omega

/-- For a cubic region, twice rank-minus-one equals its order plus boundary. -/
theorem cubic_rank_ledger (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (hcubic : ∀ v ∈ X, G.degree v = 3) :
    2 * (graph G X).cycleRank = X.card + (G.cutEdges X).card + 2 := by
  have he := rank_ledger G X hG hproper
  have hd := G.sum_region_degree X
  have hs : (∑ v ∈ X, G.degree v) = 3 * X.card := by
    rw [Finset.sum_congr rfl (fun v hv => hcubic v hv)]
    simp [Nat.mul_comm]
  rw [hs] at hd
  omega


/-- Split a sum over the three physical label classes of the cap. -/
theorem sum_edges {A : Type*} [AddCommMonoid A] (f : (graph G X).Edge → A) :
    (∑ e, f e) =
      (∑ e : InternalEdge G X, f (edgeEquiv G X (Sum.inl e))) +
      (∑ e : BoundaryEdge G X, f (edgeEquiv G X (Sum.inr (Sum.inl e)))) +
      ∑ i : Fin (capSize G X), f (edgeEquiv G X (Sum.inr (Sum.inr i))) := by
  calc
    _ = ∑ e : EdgeLabel G X, f (edgeEquiv G X e) := by
      symm
      exact Fintype.sum_equiv (edgeEquiv G X) _ _ (by intro e; rfl)
    _ = _ := by rw [Fintype.sum_sum_type, Fintype.sum_sum_type]; exact (add_assoc _ _ _).symm

/-- Internal edges and boundary edges are disjoint physical label sets. -/
theorem internal_cut_disjoint : Disjoint (G.internalEdges X) (G.cutEdges X) := by
  apply Finset.disjoint_left.mpr
  intro e hi hb
  have hi' := (Finset.mem_filter.mp hi).2
  have hb' := (Finset.mem_filter.mp hb).2
  rcases hb' with hb' | hb'
  · exact hb'.2 hi'.2
  · exact hb'.1 hi'.1

/-- A cut edge contributes just its retained endpoint to a local boundary. -/
theorem cut_boundary_term {A : Type*} [AddZeroClass A]
    (e : BoundaryEdge G X) (v : OldVertex G X) (z : A) :
    (if G.src e.1 = v.1 then z else 0) + (if G.dst e.1 = v.1 then z else 0) =
      if insideEnd G X e = v then z else 0 := by
  rcases (Finset.mem_filter.mp e.2).2 with he | he
  · have ht : G.dst e.1 ≠ v.1 := by intro hh; exact he.2 (hh ▸ v.2)
    simp [insideEnd, he.1, ht, Subtype.ext_iff]
  · have hs : G.src e.1 ≠ v.1 := by intro hh; exact he.1 (hh ▸ v.2)
    simp [insideEnd, he.1, hs, Subtype.ext_iff]

/-- Read cap internal edges and spokes on the original labels; omit outside edges. -/
def readWord : (graph G X).EdgeWord →ₗ[F₂] G.EdgeWord where
  toFun z e := if hi : e ∈ G.internalEdges X then z (edgeEquiv G X (Sum.inl ⟨e, hi⟩))
    else if hb : e ∈ G.cutEdges X then z (edgeEquiv G X (Sum.inr (Sum.inl ⟨e, hb⟩))) else 0
  map_add' z w := by
    funext e
    by_cases hi : e ∈ G.internalEdges X <;> by_cases hb : e ∈ G.cutEdges X <;> simp [hi, hb]
  map_smul' z w := by
    funext e
    by_cases hi : e ∈ G.internalEdges X <;> by_cases hb : e ∈ G.cutEdges X <;> simp [hi, hb]

@[simp] theorem readWord_internal (z : (graph G X).EdgeWord) (e : InternalEdge G X) :
    readWord G X z e.1 = z (edgeEquiv G X (Sum.inl e)) := by simp [readWord, e.2]

@[simp] theorem readWord_cut (z : (graph G X).EdgeWord) (e : BoundaryEdge G X) :
    readWord G X z e.1 = z (edgeEquiv G X (Sum.inr (Sum.inl e))) := by
  have hi : e.1 ∉ G.internalEdges X := by
    intro hi
    exact Finset.disjoint_left.mp (internal_cut_disjoint G X) hi e.2
  simp [readWord, hi, e.2]

@[simp] theorem readWord_outside (z : (graph G X).EdgeWord) (e : G.Edge)
    (hi : e ∉ G.internalEdges X) (hb : e ∉ G.cutEdges X) : readWord G X z e = 0 := by
  simp [readWord, hi, hb]

/-- Boundary at an old vertex is the internal sum plus its incident spokes. -/
theorem cap_boundary_old (z : (graph G X).EdgeWord) (v : OldVertex G X) :
    (graph G X).boundary z (oldVertex G X v) =
      (∑ e : InternalEdge G X,
        ((if G.src e.1 = v.1 then z (edgeEquiv G X (Sum.inl e)) else 0) +
         (if G.dst e.1 = v.1 then z (edgeEquiv G X (Sum.inl e)) else 0))) +
      ∑ e : BoundaryEdge G X,
        if insideEnd G X e = v then z (edgeEquiv G X (Sum.inr (Sum.inl e))) else 0 := by
  change (∑ e : (graph G X).Edge,
    ((if (graph G X).src e = oldVertex G X v then z e else 0) +
     (if (graph G X).dst e = oldVertex G X v then z e else 0))) = _
  rw [sum_edges]
  simp only [graph_src, graph_dst, source, target, oldVertex,
    (vertexEquiv G X).injective.eq_iff, Sum.inl.injEq, Subtype.mk.injEq,
    Sum.inr_ne_inl, ↓reduceIte, add_zero, zero_add, Finset.sum_const_zero, Subtype.ext_iff]

private theorem sum_on_two_disjoint {A : Type*} [AddCommMonoid A]
    (I B : Finset G.Edge) (hd : Disjoint I B) (f : G.Edge → A)
    (hz : ∀ e, e ∉ I → e ∉ B → f e = 0) :
    (∑ e, f e) = (∑ e : I, f e.1) + ∑ e : B, f e.1 := by
  have hp (e : G.Edge) : f e = (if e ∈ I then f e else 0) + (if e ∈ B then f e else 0) := by
    by_cases hi : e ∈ I <;> by_cases hb : e ∈ B
    · exact (Finset.disjoint_left.mp hd hi hb).elim
    · simp [hi, hb]
    · simp [hi, hb]
    · simp [hi, hb, hz e hi hb]
  calc
    _ = ∑ e, ((if e ∈ I then f e else 0) + (if e ∈ B then f e else 0)) :=
      Finset.sum_congr rfl (fun e _ => hp e)
    _ = (∑ e ∈ I, f e) + ∑ e ∈ B, f e := by
      rw [Finset.sum_add_distrib, Fintype.sum_extend_by_zero, Fintype.sum_extend_by_zero]
    _ = _ := by rw [Finset.sum_coe_sort, Finset.sum_coe_sort]

/-- The read-back map preserves every boundary equation inside X. -/
theorem boundary_readWord (z : (graph G X).EdgeWord) (v : OldVertex G X) :
    G.boundary (readWord G X z) v.1 = (graph G X).boundary z (oldVertex G X v) := by
  rw [cap_boundary_old]
  change (∑ e : G.Edge,
    ((if G.src e = v.1 then readWord G X z e else 0) +
     (if G.dst e = v.1 then readWord G X z e else 0))) = _
  rw [sum_on_two_disjoint G (G.internalEdges X) (G.cutEdges X) (internal_cut_disjoint G X) _ (by
    intro e hi hb
    simp [readWord_outside G X z e hi hb])]
  congr 1
  · apply Finset.sum_congr rfl
    intro e he
    rw [readWord_internal]
  · apply Finset.sum_congr rfl
    intro e he
    rw [readWord_cut]
    exact cut_boundary_term G X e v _

/-- Contract the padded cycle to the same hub used for the original outside. -/
def fiber (v : (graph G X).Vertex) : OutsideContraction.QuotientVertex G X :=
  match (vertexEquiv G X).symm v with
  | Sum.inl a => some a
  | Sum.inr _ => none

@[simp] theorem fiber_old (v : OldVertex G X) : fiber G X (oldVertex G X v) = some v := by
  simp [fiber, oldVertex]

@[simp] theorem fiber_cap (i : Fin (capSize G X)) : fiber G X (capVertex G X i) = none := by
  simp [fiber, capVertex]

@[simp] theorem fiber_eq_some_iff (v : (graph G X).Vertex) (a : OldVertex G X) :
    fiber G X v = some a ↔ v = oldVertex G X a := by
  obtain ⟨v, rfl⟩ := (vertexEquiv G X).surjective v
  cases v with
  | inl b => simp [fiber, oldVertex, (vertexEquiv G X).injective.eq_iff]
  | inr i => simp [fiber, oldVertex, (vertexEquiv G X).injective.eq_iff]

/-- All cap fibers are connected, without any assumption on the region. -/
theorem connectedFibers : ConnectedContraction.ConnectedFibers (graph G X) (fiber G X) := by
  intro q
  cases q with
  | some a =>
      let a' : {v : (graph G X).Vertex // fiber G X v = some a} := ⟨oldVertex G X a, by simp⟩
      refine { nonempty := ⟨a'⟩, preconnected := ?_ }
      intro u v
      have hu := (fiber_eq_some_iff G X u.1 a).mp u.2
      have hv := (fiber_eq_some_iff G X v.1 a).mp v.2
      have he : u = v := Subtype.ext (hu.trans hv.symm)
      subst v
      exact .refl _
  | none =>
      let V := {v : (graph G X).Vertex // fiber G X v = none}
      let cv (i : Fin (capSize G X)) : V := ⟨capVertex G X i, by simp⟩
      let H := (graph G X).toSimpleGraph.induce {v | fiber G X v = none}
      have hstep (i : Fin (capSize G X)) : H.Reachable (cv i) (cv (next G X i)) := by
        by_cases he : cv i = cv (next G X i)
        · rw [he]
        · apply SimpleGraph.Adj.reachable
          change (graph G X).toSimpleGraph.Adj (capVertex G X i) (capVertex G X (next G X i))
          refine ⟨?_, edgeEquiv G X (Sum.inr (Sum.inr i)), Or.inl ?_⟩
          · intro hh; exact he (Subtype.ext hh)
          · simp [source, target, capVertex]
      have hzero : ∀ k (hk : k < capSize G X), H.Reachable (cv (zeroIndex G X)) (cv ⟨k, hk⟩) := by
        intro k
        induction k with
        | zero => intro hk; exact .refl _
        | succ k ih =>
            intro hk
            have hk' : k < capSize G X := by omega
            have hn : next G X ⟨k, hk'⟩ = ⟨k+1, hk⟩ := by
              apply Fin.ext
              exact Nat.mod_eq_of_lt hk
            have hh := hstep ⟨k, hk'⟩
            rw [hn] at hh
            exact (ih hk').trans hh
      have hrepr (v : V) : ∃ i, cv i = v := by
        obtain ⟨v', hv'⟩ := (vertexEquiv G X).surjective v.1
        cases v' with
        | inl a =>
            have hh := v.2
            rw [← hv'] at hh
            simp [fiber] at hh
        | inr i => exact ⟨i, Subtype.ext hv'⟩
      refine { nonempty := ⟨cv (zeroIndex G X)⟩, preconnected := ?_ }
      intro u v
      obtain ⟨i, rfl⟩ := hrepr u
      obtain ⟨j, rfl⟩ := hrepr v
      exact (hzero i.1 i.2).symm.trans (hzero j.1 j.2)

/-- Read cap cycles onto the common loop-preserving quotient. -/
def project : (graph G X).CycleSpace →ₗ[F₂] (OutsideContraction.quotient G X).CycleSpace where
  toFun z := ⟨LoopPreservingContraction.projectWord G (OutsideContraction.fiber G X)
    (OutsideContraction.keptLoops G X) (readWord G X z.1), by
      rw [LinearMap.mem_ker]
      funext q
      obtain ⟨q, rfl⟩ := LoopPreservingContraction.vertexEquiv.surjective q
      rw [LoopPreservingContraction.boundary_projectWord]
      apply OutsideContraction.fiberSum_boundary_zero
      intro v hv
      rw [boundary_readWord G X z.1 ⟨v, hv⟩]
      exact congrFun z.2 _⟩
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

/-- Extend original coordinates to internal labels and spokes, with a zero cap cycle. -/
def extendWord (x : G.EdgeWord) : (graph G X).EdgeWord := fun e =>
  match (edgeEquiv G X).symm e with
  | Sum.inl a => x a.1
  | Sum.inr (Sum.inl a) => x a.1
  | Sum.inr (Sum.inr _) => 0

/-- The extension reads back exactly when the original word is supported on retained labels. -/
theorem readWord_extendWord (x : G.EdgeWord)
    (hx : ∀ e, e ∉ G.internalEdges X → e ∉ G.cutEdges X → x e = 0) :
    readWord G X (extendWord G X x) = x := by
  funext e
  by_cases hi : e ∈ G.internalEdges X
  · simp [readWord, hi, extendWord]
  · by_cases hb : e ∈ G.cutEdges X
    · simp [readWord, hi, hb, extendWord]
    · simp [readWord, hi, hb, hx e hi hb]

/-- Zero old-vertex boundary leaves a fiber-even defect on the cap. -/
theorem fiberSum_boundary_zero (z : (graph G X).EdgeWord)
    (hz : ∀ a : OldVertex G X, (graph G X).boundary z (oldVertex G X a) = 0)
    (q : OutsideContraction.QuotientVertex G X) :
    ConnectedContraction.fiberSum (graph G X) (fiber G X) ((graph G X).boundary z) q = 0 := by
  cases q with
  | some a =>
      simp only [ConnectedContraction.fiberSum, fiber_eq_some_iff]
      simpa using hz a
  | none =>
      have hp (v : (graph G X).Vertex) :
          (if fiber G X v = none then (graph G X).boundary z v else 0) = (graph G X).boundary z v := by
        obtain ⟨a, rfl⟩ := (vertexEquiv G X).surjective v
        cases a with
        | inl a => simpa [fiber] using (hz a).symm
        | inr i => simp [fiber]
      calc
        _ = ∑ v, (graph G X).boundary z v := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases hh : fiber G X v = none
          · simp only [hh, if_true]
          · simpa only [hh, if_false] using hp v
        _ = 0 := sum_boundary_eq_zero (graph G X) z

private theorem repairWord_edge_zero (b : (graph G X).Demand) (e : (graph G X).Edge)
    (he : fiber G X ((graph G X).src e) ≠ fiber G X ((graph G X).dst e) ∨
      (graph G X).src e = (graph G X).dst e) :
    ConnectedContraction.repairWord (graph G X) (fiber G X) (connectedFibers G X) b e = 0 := by
  rcases he with he | he
  · have hh := congrFun (ConnectedContraction.projectWord_repairWord
        (graph G X) (fiber G X) (connectedFibers G X) b)
        (ConnectedContraction.edgeEquiv (graph G X) (fiber G X) ⟨e, he⟩)
    simpa [ConnectedContraction.projectWord] using hh
  · unfold ConnectedContraction.repairWord
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro v hv
    rw [walkWord_loop_eq_zero (graph G X) _ e he, smul_zero]

/-- Parity repair on the cap changes neither internal coordinates nor spokes. -/
theorem readWord_repairWord (b : (graph G X).Demand) :
    readWord G X (ConnectedContraction.repairWord (graph G X) (fiber G X)
      (connectedFibers G X) b) = 0 := by
  funext e
  by_cases hi : e ∈ G.internalEdges X
  · rw [readWord_internal G X _ ⟨e, hi⟩]
    apply repairWord_edge_zero
    by_cases hh : G.src e = G.dst e
    · right
      simp [source, target, hh, Subtype.ext_iff]
    · left
      simp [source, target, fiber, hh, Subtype.ext_iff]
  · by_cases hb : e ∈ G.cutEdges X
    · rw [readWord_cut G X _ ⟨e, hb⟩]
      apply repairWord_edge_zero
      left
      simp [source, target, fiber]
    · exact readWord_outside G X _ e hi hb

/-- Every even word on the common quotient has an even extension to the cycle cap. -/
theorem project_surjective : Function.Surjective (project G X) := by
  intro y
  let x := LoopPreservingContraction.extendWord G (OutsideContraction.fiber G X)
    (OutsideContraction.keptLoops G X) y.1
  have hx (e : G.Edge) (hi : e ∉ G.internalEdges X) (hb : e ∉ G.cutEdges X) : x e = 0 := by
    have hn : ¬ (G.src e ∈ X ∨ G.dst e ∈ X) := by
      intro hh
      rcases hh with hs | ht
      · by_cases ht : G.dst e ∈ X
        · exact hi (by simp [internalEdges, hs, ht])
        · exact hb (by simp [cutEdges, hs, ht])
      · by_cases hs : G.src e ∈ X
        · exact hi (by simp [internalEdges, hs, ht])
        · exact hb (by simp [cutEdges, hs, ht])
    have hh := mt (OutsideContraction.retained_iff G X e).mp hn
    simp [x, LoopPreservingContraction.extendWord, hh]
  have hread : readWord G X (extendWord G X x) = x := readWord_extendWord G X x hx
  have hxold (a : OldVertex G X) : G.boundary x a.1 = 0 := by
    have hh := LoopPreservingContraction.boundary_projectWord G
      (OutsideContraction.fiber G X) (OutsideContraction.keptLoops G X) x (some a)
    have hp : LoopPreservingContraction.projectWord G (OutsideContraction.fiber G X)
        (OutsideContraction.keptLoops G X) x = y.1 :=
      LoopPreservingContraction.projectWord_extendWord _ _ _ _
    rw [hp] at hh
    have hy := congrFun y.2 (LoopPreservingContraction.vertexEquiv (some a))
    rw [hh] at hy
    simpa [ConnectedContraction.fiberSum, OutsideContraction.fiber_eq_some_iff] using hy
  let z := extendWord G X x
  let b := (graph G X).boundary z
  have hzold (a : OldVertex G X) : (graph G X).boundary z (oldVertex G X a) = 0 := by
    rw [← boundary_readWord]
    change G.boundary (readWord G X (extendWord G X x)) a.1 = 0
    rw [hread]
    exact hxold a
  have heven : (graph G X).boundary
      (z + ConnectedContraction.repairWord (graph G X) (fiber G X) (connectedFibers G X) b) = 0 := by
    rw [map_add, ConnectedContraction.boundary_repairWord _ _ _ _
      (fiberSum_boundary_zero G X z hzold)]
    exact word_add_self b
  refine ⟨⟨z + ConnectedContraction.repairWord (graph G X) (fiber G X) (connectedFibers G X) b, heven⟩, ?_⟩
  apply Subtype.ext
  change LoopPreservingContraction.projectWord G (OutsideContraction.fiber G X)
    (OutsideContraction.keptLoops G X)
    (readWord G X (z + ConnectedContraction.repairWord (graph G X) (fiber G X)
      (connectedFibers G X) b)) = y.1
  rw [map_add, readWord_repairWord, add_zero]
  change LoopPreservingContraction.projectWord G (OutsideContraction.fiber G X)
    (OutsideContraction.keptLoops G X) (readWord G X (extendWord G X x)) = y.1
  rw [hread]
  exact LoopPreservingContraction.projectWord_extendWord _ _ _ _

/-- The cap has the exact uniform law on the common quotient. -/
theorem density_project (P : (OutsideContraction.quotient G X).CycleSpace → Prop) :
    Finite.density (fun z : (graph G X).CycleSpace => P (project G X z)) = Finite.density P :=
  density_surjective_linear (project G X) (project_surjective G X) P

/-- The retained label in the hub quotient corresponding to an internal physical edge. -/
def quotientInternalEdge (e : InternalEdge G X) : (OutsideContraction.quotient G X).Edge :=
  LoopPreservingContraction.edgeEquiv G (OutsideContraction.fiber G X)
    (OutsideContraction.keptLoops G X) ⟨e.1,
      (OutsideContraction.retained_iff G X e.1).mpr (Or.inl (internal_src_mem G X e))⟩

@[simp] theorem original_project_internal (z : G.CycleSpace) (e : InternalEdge G X) :
    (OutsideContraction.project G X z).1 (quotientInternalEdge G X e) = z.1 e.1 := by
  simp [OutsideContraction.project, LoopPreservingContraction.project,
    LoopPreservingContraction.projectWord, quotientInternalEdge]

@[simp] theorem cap_project_internal (z : (graph G X).CycleSpace) (e : InternalEdge G X) :
    (project G X z).1 (quotientInternalEdge G X e) = z.1 (edgeEquiv G X (Sum.inl e)) := by
  simp [project, LoopPreservingContraction.projectWord, quotientInternalEdge]

/-- Every joint event on the retained internal labels has the same probability.
The region may be disconnected and may contain loops or parallel labels. -/
theorem internal_event_law
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected)
    (P : (InternalEdge G X → F₂) → Prop) :
    Finite.density (fun z : G.CycleSpace => P (fun e => z.1 e.1)) =
      Finite.density (fun z : (graph G X).CycleSpace =>
        P (fun e => z.1 (edgeEquiv G X (Sum.inl e)))) := by
  let Q : (OutsideContraction.quotient G X).CycleSpace → Prop :=
    fun y => P (fun e => y.1 (quotientInternalEdge G X e))
  have ho := OutsideContraction.density_project G X houtside Q
  have hc := density_project G X Q
  simpa [Q] using ho.trans hc.symm

/-- Every old vertex keeps its ambient incidence degree, including loop incidences. -/
theorem degree_old (v : OldVertex G X) :
    (graph G X).degree (oldVertex G X v) = G.degree v.1 := by
  unfold degree
  rw [(graph G X).selectedDegree_eq_sum_endpoints, G.selectedDegree_eq_sum_endpoints]
  change (∑ e : (graph G X).Edge,
    ((if (graph G X).src e = oldVertex G X v then (1 : ℕ) else 0) +
     (if (graph G X).dst e = oldVertex G X v then 1 else 0))) =
    ∑ e : G.Edge, ((if G.src e = v.1 then (1 : ℕ) else 0) + (if G.dst e = v.1 then 1 else 0))
  rw [sum_edges]
  simp only [graph_src, graph_dst, source, target, oldVertex,
    (vertexEquiv G X).injective.eq_iff, Sum.inl.injEq, Subtype.mk.injEq,
    Sum.inr_ne_inl, if_false, add_zero, zero_add, Finset.sum_const_zero, Subtype.ext_iff,
    show (1 : Erdos1016.F₂) ≠ 0 from one_ne_zero, ↓reduceIte]
  symm
  rw [sum_on_two_disjoint G (G.internalEdges X) (G.cutEdges X) (internal_cut_disjoint G X) _ (by
    intro e hi hb
    have hs : G.src e ≠ v.1 := by
      intro hh
      have hv := hh ▸ v.2
      by_cases ht : G.dst e ∈ X
      · exact hi (by simp [internalEdges, hv, ht])
      · exact hb (by simp [cutEdges, hv, ht])
    have ht : G.dst e ≠ v.1 := by
      intro hh
      have hv := hh ▸ v.2
      by_cases hs : G.src e ∈ X
      · exact hi (by simp [internalEdges, hs, hv])
      · exact hb (by simp [cutEdges, hs, hv])
    simp [hs, ht])]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  simpa only [Subtype.ext_iff] using cut_boundary_term G X e v (1 : ℕ)

/-- Rotation around the padded cycle is a bijection. -/
theorem next_injective : Function.Injective (next G X) := by
  intro a b hab
  have hh : (a.1+1) % capSize G X = (b.1+1) % capSize G X := congrArg Fin.val hab
  apply Fin.ext
  have ha := a.2
  have hb := b.2
  by_cases ha' : a.1+1 = capSize G X <;> by_cases hb' : b.1+1 = capSize G X
  · omega
  · rw [ha', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hh
    omega
  · rw [hb', Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hh
    omega
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hh
    omega

def nextEquiv : Fin (capSize G X) ≃ Fin (capSize G X) :=
  Equiv.ofBijective (next G X) (Finite.injective_iff_bijective.mp (next_injective G X))

/-- A cap vertex has two cycle incidences and at most one spoke. -/
theorem degree_cap (i : Fin (capSize G X)) :
    (graph G X).degree (capVertex G X i) =
      2 + (Finset.univ.filter fun e : BoundaryEdge G X => spokeIndex G X e = i).card := by
  unfold degree
  rw [(graph G X).selectedDegree_eq_sum_endpoints]
  change (∑ e : (graph G X).Edge,
    ((if (graph G X).src e = capVertex G X i then (1 : ℕ) else 0) +
     (if (graph G X).dst e = capVertex G X i then 1 else 0))) = _
  rw [sum_edges]
  simp only [graph_src, graph_dst, source, target, capVertex,
    (vertexEquiv G X).injective.eq_iff, Sum.inr.injEq, Sum.inl_ne_inr,
    if_false, zero_add, Finset.sum_const_zero,
    show (1 : Erdos1016.F₂) ≠ 0 from one_ne_zero, ↓reduceIte]
  rw [Finset.sum_add_distrib]
  have hn : (∑ k : Fin (capSize G X), if next G X k = i then (1 : ℕ) else 0) = 1 := by
    calc
      _ = ∑ k : Fin (capSize G X), if k = i then (1 : ℕ) else 0 :=
        Fintype.sum_equiv (nextEquiv G X) _ _ (by intro k; rfl)
      _ = 1 := by simp
  rw [hn]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_filter]
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem degree_cap_le_three (i : Fin (capSize G X)) :
    (graph G X).degree (capVertex G X i) ≤ 3 := by
  rw [degree_cap]
  have hh : (Finset.univ.filter fun e : BoundaryEdge G X => spokeIndex G X e = i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply spokeIndex_injective G X
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  omega

/-- Local cubic vertices and a simple cap cycle give a subcubic graph. -/
theorem subcubic (hdegree : ∀ v ∈ X, G.degree v ≤ 3) :
    ∀ v, (graph G X).degree v ≤ 3 := by
  intro v
  obtain ⟨v, rfl⟩ := (vertexEquiv G X).surjective v
  cases v with
  | inl a => exact (degree_old G X a).trans_le (hdegree a.1 a.2)
  | inr i => exact degree_cap_le_three G X i

/-- Keep just the original internal labels in the cap graph. -/
def internalLift (x : G.EdgeWord) : (graph G X).EdgeWord := fun e =>
  match (edgeEquiv G X).symm e with
  | Sum.inl a => x a.1
  | Sum.inr _ => 0

@[simp] theorem internalLift_internal (x : G.EdgeWord) (e : InternalEdge G X) :
    internalLift G X x (edgeEquiv G X (Sum.inl e)) = x e.1 := by simp [internalLift]

@[simp] theorem internalLift_spoke (x : G.EdgeWord) (e : BoundaryEdge G X) :
    internalLift G X x (edgeEquiv G X (Sum.inr (Sum.inl e))) = 0 := by simp [internalLift]

@[simp] theorem internalLift_cycle (x : G.EdgeWord) (i : Fin (capSize G X)) :
    internalLift G X x (edgeEquiv G X (Sum.inr (Sum.inr i))) = 0 := by simp [internalLift]

@[simp] theorem readWord_internalLift (x : G.EdgeWord) :
    readWord G X (internalLift G X x) = G.restrictEdges (G.internalEdges X) x := by
  funext e
  by_cases hi : e ∈ G.internalEdges X
  · simp [readWord, hi, restrictEdges]
  · by_cases hb : e ∈ G.cutEdges X <;> simp [readWord, hi, hb, internalLift, restrictEdges]

/-- An internally supported word has zero boundary at every exterior vertex. -/
theorem boundary_outside_of_internal_support (x : G.EdgeWord)
    (hx : ∀ e, e ∉ G.internalEdges X → x e = 0) (v : G.Vertex) (hv : v ∉ X) :
    G.boundary x v = 0 := by
  change (∑ e, ((if G.src e = v then x e else 0) + (if G.dst e = v then x e else 0))) = 0
  apply Finset.sum_eq_zero
  intro e he
  by_cases hi : e ∈ G.internalEdges X
  · have hs : G.src e ≠ v := by
      intro hh; exact hv (hh ▸ (Finset.mem_filter.mp hi).2.1)
    have ht : G.dst e ≠ v := by
      intro hh; exact hv (hh ▸ (Finset.mem_filter.mp hi).2.2)
    simp [hs, ht]
  · simp [hx e hi]

/-- A word without spokes is even after readback whenever it was even on the cap. -/
theorem boundary_readWord_zero (z : (graph G X).EdgeWord)
    (hz : (graph G X).boundary z = 0)
    (hspoke : ∀ e : BoundaryEdge G X, z (edgeEquiv G X (Sum.inr (Sum.inl e))) = 0) :
    G.boundary (readWord G X z) = 0 := by
  funext v
  by_cases hv : v ∈ X
  · rw [boundary_readWord G X z ⟨v, hv⟩]
    exact congrFun hz _
  · apply boundary_outside_of_internal_support G X _ _ v hv
    intro e hi
    by_cases hb : e ∈ G.cutEdges X
    · rw [readWord_cut G X z ⟨e, hb⟩]
      exact hspoke ⟨e, hb⟩
    · exact readWord_outside G X z e hi hb

/-- A cap word vanishes if its readback and cap-cycle coordinates vanish. -/
theorem eq_zero_of_readWord_zero (z : (graph G X).EdgeWord)
    (hr : readWord G X z = 0)
    (hc : ∀ i : Fin (capSize G X), z (edgeEquiv G X (Sum.inr (Sum.inr i))) = 0) : z = 0 := by
  funext e
  obtain ⟨a, rfl⟩ := (edgeEquiv G X).surjective e
  cases a with
  | inl a => simpa using congrFun hr a.1
  | inr a =>
      cases a with
      | inl a => simpa using congrFun hr a.1
      | inr i => exact hc i

/-- Internally supported even words lift to even cap words. -/
theorem boundary_internalLift_zero (x : G.EdgeWord) (hx : G.boundary x = 0)
    (hs : ∀ e, e ∉ G.internalEdges X → x e = 0) :
    (graph G X).boundary (internalLift G X x) = 0 := by
  have hr : G.restrictEdges (G.internalEdges X) x = x := by
    funext e
    by_cases hi : e ∈ G.internalEdges X <;> simp [restrictEdges, hi, hs e]
  funext v
  obtain ⟨a, rfl⟩ := (vertexEquiv G X).surjective v
  cases a with
  | inl a =>
      change (graph G X).boundary (internalLift G X x) (oldVertex G X a) = 0
      rw [← boundary_readWord, readWord_internalLift, hr]
      exact congrFun hx a.1
  | inr i =>
      change (∑ e : (graph G X).Edge,
        ((if (graph G X).src e = capVertex G X i then internalLift G X x e else 0) +
         (if (graph G X).dst e = capVertex G X i then internalLift G X x e else 0))) = 0
      rw [sum_edges]
      simp [source, target, capVertex, (vertexEquiv G X).injective.eq_iff]

/-- Foresthood on internal physical labels is unchanged by the cap construction. -/
theorem internalLift_forest_iff (x : G.EdgeWord) :
    (graph G X).IsForestWord (internalLift G X x) ↔
      G.IsForestWord (G.restrictEdges (G.internalEdges X) x) := by
  rw [(graph G X).isForestWord_iff_no_even_support,
    G.isForestWord_iff_no_even_support]
  constructor
  · intro h seed hsub
    have hs (e : G.Edge) (hi : e ∉ G.internalEdges X) : seed.1 e = 0 := by
      by_contra hh
      have hz := hsub e hh
      simp [restrictEdges, hi] at hz
    let z : (graph G X).CycleSpace := ⟨internalLift G X seed.1,
      boundary_internalLift_zero G X seed.1 seed.2 hs⟩
    have hh : z.1 = 0 := h z (by
      intro e he
      obtain ⟨a, rfl⟩ := (edgeEquiv G X).surjective e
      cases a with
      | inl a =>
          have hne : seed.1 a.1 ≠ 0 := by simpa [z] using he
          have hx := hsub a.1 hne
          simpa [restrictEdges, a.2] using hx
      | inr a =>
          cases a <;> simp [z] at he)
    funext e
    by_cases hi : e ∈ G.internalEdges X
    · simpa [z] using congrFun hh (edgeEquiv G X (Sum.inl ⟨e, hi⟩))
    · exact hs e hi
  · intro h seed hsub
    have hb (e : BoundaryEdge G X) : seed.1 (edgeEquiv G X (Sum.inr (Sum.inl e))) = 0 := by
      by_contra hh
      have hz := hsub _ hh
      simp at hz
    have hc (i : Fin (capSize G X)) : seed.1 (edgeEquiv G X (Sum.inr (Sum.inr i))) = 0 := by
      by_contra hh
      have hz := hsub _ hh
      simp at hz
    let z : G.CycleSpace := ⟨readWord G X seed.1, boundary_readWord_zero G X seed.1 seed.2 hb⟩
    have hz : z.1 = 0 := h z (by
      intro e he
      by_cases hi : e ∈ G.internalEdges X
      · have hh : seed.1 (edgeEquiv G X (Sum.inl ⟨e, hi⟩)) ≠ 0 := by simpa [z, readWord, hi] using he
        have hn := hsub _ hh
        simpa [restrictEdges, hi] using hn
      · by_cases hb' : e ∈ G.cutEdges X
        · have hh := hb ⟨e, hb'⟩
          simp [z, readWord, hi, hb', hh] at he
        · simp [z, readWord, hi, hb'] at he)
    exact eq_zero_of_readWord_zero G X seed.1 hz hc

/-- The marked set is the complete padded cycle. -/
def markedVertices : Finset (graph G X).Vertex := Finset.univ.filter fun v => fiber G X v = none

def oldVertices : Finset (graph G X).Vertex := (markedVertices G X)ᶜ

@[simp] theorem old_mem_marked (a : OldVertex G X) : oldVertex G X a ∉ markedVertices G X := by
  simp [markedVertices]

@[simp] theorem cap_mem_marked (i : Fin (capSize G X)) : capVertex G X i ∈ markedVertices G X := by
  simp [markedVertices]

@[simp] theorem old_mem_old (a : OldVertex G X) : oldVertex G X a ∈ oldVertices G X := by
  simp [oldVertices]

@[simp] theorem cap_not_mem_old (i : Fin (capSize G X)) : capVertex G X i ∉ oldVertices G X := by
  simp [oldVertices]

theorem marked_connected :
    ((graph G X).toSimpleGraph.induce (↑(markedVertices G X) : Set (graph G X).Vertex)).Connected := by
  have hh := connectedFibers G X none
  have he : (↑(markedVertices G X) : Set (graph G X).Vertex) = {v | fiber G X v = none} := by
    ext v; simp [markedVertices]
  rw [he]
  exact hh

theorem marked_card : (markedVertices G X).card = capSize G X := by
  unfold markedVertices
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ a : VertexLabel G X, if fiber G X (vertexEquiv G X a) = none then (1 : ℕ) else 0 := by
      symm
      exact Fintype.sum_equiv (vertexEquiv G X) _ _ (by intro a; simp [markedVertices])
    _ = _ := by rw [Fintype.sum_sum_type]; simp [fiber]

/-- The unmarked vertices retain cubic degree whenever the original region was cubic. -/
theorem cubic_outside_marked (hcubic : ∀ v ∈ X, G.degree v = 3) :
    ∀ v, v ∉ markedVertices G X → (graph G X).degree v = 3 := by
  intro v hv
  obtain ⟨a, rfl⟩ := (vertexEquiv G X).surjective v
  cases a with
  | inl a => exact (degree_old G X a).trans (hcubic a.1 a.2)
  | inr i => exact (hv (cap_mem_marked G X i)).elim

/-- Deleting the marked vertices leaves exactly the internal lift. -/
theorem restrict_old_eq (z : (graph G X).EdgeWord) :
    (graph G X).restrictEdges ((graph G X).internalEdges (oldVertices G X)) z =
      internalLift G X (readWord G X z) := by
  funext e
  obtain ⟨a, rfl⟩ := (edgeEquiv G X).surjective e
  cases a with
  | inl a =>
      simp [restrictEdges, internalEdges, source, target, oldVertex, oldVertices,
        markedVertices, fiber, internalLift]
  | inr a =>
      cases a with
      | inl a => simp [restrictEdges, internalEdges, source, target, oldVertices, markedVertices, fiber, internalLift]
      | inr i => simp [restrictEdges, internalEdges, source, target, oldVertices, markedVertices, fiber, internalLift]

/-- Exact forest law on a disconnected region with connected complement. -/
theorem forest_event_law
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) :
    Finite.density (fun z : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges X) z.1)) =
    Finite.density (fun z : (graph G X).CycleSpace =>
      (graph G X).IsForestWord
        ((graph G X).restrictEdges ((graph G X).internalEdges (oldVertices G X)) z.1)) := by
  let P : (InternalEdge G X → F₂) → Prop := fun f =>
    G.IsForestWord (fun e => if hi : e ∈ G.internalEdges X then f ⟨e, hi⟩ else 0)
  have hh := internal_event_law G X houtside P
  have hright (z : (graph G X).CycleSpace) :
      P (fun e => z.1 (edgeEquiv G X (Sum.inl e))) ↔
      (graph G X).IsForestWord
        ((graph G X).restrictEdges ((graph G X).internalEdges (oldVertices G X)) z.1) := by
    rw [restrict_old_eq, internalLift_forest_iff]
    have he : (fun e => if hi : e ∈ G.internalEdges X then
        z.1 (edgeEquiv G X (Sum.inl ⟨e, hi⟩)) else 0) =
        G.restrictEdges (G.internalEdges X) (readWord G X z.1) := by
      funext e
      by_cases hi : e ∈ G.internalEdges X <;> simp [restrictEdges, readWord, hi]
    change G.IsForestWord _ ↔ _
    rw [he]
  simpa only [P, restrictEdges, hright] using hh

/-- Probability form of the exact localized forest law. -/
theorem regionForestProbability_eq
    (houtside : (G.toSimpleGraph.induce (↑(Xᶜ) : Set G.Vertex)).Connected) :
    G.regionForestProbability X = (graph G X).regionForestProbability (markedVertices G X)ᶜ := by
  have hh := forest_event_law G X houtside
  simpa only [regionForestProbability, Finite.density, Finite.count,
    G.cycleSpace_card, (graph G X).cycleSpace_card, Nat.cast_pow, Nat.cast_ofNat,
    oldVertices, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh

end CycleCap
end Erdos1016.FiniteMultiGraph.RegionLocalization

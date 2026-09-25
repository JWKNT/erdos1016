import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Probability.Finite.LinearImages

set_option autoImplicit false

/-!
# Contracting connected vertex fibers

The quotient retains precisely the physical edges crossing between fibers.
Connectedness of every induced fiber makes projection of binary cycle spaces
surjective, and therefore preserves all joint cut laws.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.FiniteMultiGraph.ConnectedContraction

open BoundaryTrace

variable (G : FiniteMultiGraph) {Q : Type*} [Fintype Q] (fiber : G.Vertex → Q)

local instance contractionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev CrossingEdge := {e : G.Edge // fiber (G.src e) ≠ fiber (G.dst e)}

def vertexEquiv : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q

def edgeEquiv : CrossingEdge G fiber ≃ Fin (Fintype.card (CrossingEdge G fiber)) :=
  Fintype.equivFin _

def quotient : FiniteMultiGraph where
  vertexCount := Fintype.card Q
  edgeCount := Fintype.card (CrossingEdge G fiber)
  src e := vertexEquiv (fiber (G.src ((edgeEquiv G fiber).symm e).1))
  dst e := vertexEquiv (fiber (G.dst ((edgeEquiv G fiber).symm e).1))

def projectWord : G.EdgeWord →ₗ[F₂] (quotient G fiber).EdgeWord where
  toFun x e := x ((edgeEquiv G fiber).symm e).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fiberSum (y : G.Demand) (q : Q) : F₂ :=
  ∑ v, if fiber v = q then y v else 0

omit [Fintype Q] in
private theorem endpoint_fiber_sum (a : G.Vertex) (z : F₂) (q : Q) :
    (∑ v, if fiber v = q then (if a = v then z else 0) else 0) =
      if fiber a = q then z else 0 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Ne.symm hba]
  · simp

theorem fiberSum_boundary (x : G.EdgeWord) (q : Q) :
    fiberSum G fiber (G.boundary x) q =
      ∑ e, ((if fiber (G.src e) = q then x e else 0) +
        (if fiber (G.dst e) = q then x e else 0)) := by
  unfold fiberSum boundary
  dsimp
  have hpoint (v : G.Vertex) :
      (if fiber v = q then ∑ e, ((if G.src e = v then x e else 0) +
        (if G.dst e = v then x e else 0)) else 0) =
      ∑ e, ((if fiber v = q then (if G.src e = v then x e else 0) else 0) +
        (if fiber v = q then (if G.dst e = v then x e else 0) else 0)) := by
    by_cases h : fiber v = q <;> simp [h]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, endpoint_fiber_sum]

/-- The quotient boundary is the total original boundary in each fiber. -/
theorem boundary_projectWord (x : G.EdgeWord) (q : Q) :
    (quotient G fiber).boundary (projectWord G fiber x) (vertexEquiv q) =
      fiberSum G fiber (G.boundary x) q := by
  rw [fiberSum_boundary]
  let term : G.Edge → F₂ := fun e =>
    (if fiber (G.src e) = q then x e else 0) +
    (if fiber (G.dst e) = q then x e else 0)
  have hinternal : (∑ e : {e : G.Edge // ¬ fiber (G.src e) ≠ fiber (G.dst e)}, term e.1) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hs : fiber (G.src e.1) = fiber (G.dst e.1) := not_not.mp e.2
    simp [term, hs, bit_add_self]
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun e : G.Edge => fiber (G.src e) ≠ fiber (G.dst e)) term
  rw [hinternal, add_zero] at hsum
  calc
    _ = ∑ e : CrossingEdge G fiber, term e.1 := by
      change (∑ e : (quotient G fiber).Edge, _) = _
      apply Fintype.sum_equiv (edgeEquiv G fiber).symm
      intro e
      simp [quotient, projectWord, term]
    _ = _ := hsum

/-- Restrict an even word to the crossing physical edge labels. -/
def project : G.CycleSpace →ₗ[F₂] (quotient G fiber).CycleSpace where
  toFun x := ⟨projectWord G fiber x.1, by
    rw [LinearMap.mem_ker]
    funext q
    obtain ⟨q, rfl⟩ := vertexEquiv.surjective q
    rw [boundary_projectWord]
    have hx : G.boundary x.1 = 0 := x.2
    simp [hx, fiberSum]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every class is represented by a nonempty connected induced region. -/
def ConnectedFibers : Prop :=
  ∀ q : Q, (G.toSimpleGraph.induce {v | fiber v = q}).Connected

def fiberRoot (h : ConnectedFibers G fiber) (q : Q) : {v : G.Vertex // fiber v = q} :=
  Classical.choice (h q).nonempty

def fiberRoute (h : ConnectedFibers G fiber) (v : G.Vertex) :
    (G.toSimpleGraph.induce {u | fiber u = fiber v}).Walk
      (fiberRoot G fiber h (fiber v)) ⟨v, rfl⟩ :=
  Classical.choice ((h (fiber v)).preconnected _ _)

def includeFiber (q : Q) : G.toSimpleGraph.induce {v | fiber v = q} →g G.toSimpleGraph :=
  (SimpleGraph.Embedding.induce (G := G.toSimpleGraph) {v | fiber v = q}).toHom

/-- A path contained in a fiber uses no crossing edge coordinate. -/
theorem walkWord_fiber_crossing (q : Q) {u v : {v : G.Vertex // fiber v = q}}
    (p : (G.toSimpleGraph.induce {v | fiber v = q}).Walk u v)
    (e : CrossingEdge G fiber) :
    G.walkWord (p.map (includeFiber G fiber q)) e.1 = 0 := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      let ha := (includeFiber G fiber q).map_adj hab
      have hc : fiber (G.src (G.edgeForAdj ha)) = fiber (G.dst (G.edgeForAdj ha)) := by
        rcases G.edgeForAdj_endpoints ha with ht | ht
        · rw [ht.1, ht.2]
          exact a.2.trans b.2.symm
        · rw [ht.1, ht.2]
          exact b.2.trans a.2.symm
      have he : e.1 ≠ G.edgeForAdj ha := fun he => e.2 (he ▸ hc)
      rw [SimpleGraph.Walk.map_cons, walkWord]
      change (Pi.single (G.edgeForAdj ha) (1 : F₂) : G.EdgeWord) e.1 + _ = (0 : F₂)
      simp [Pi.single_apply, he, ih]

/-- Extend quotient coordinates by zero on internal edges. The extension
need not itself be even; its defect is repaired inside the fibers. -/
def extendWord (y : (quotient G fiber).EdgeWord) : G.EdgeWord :=
  fun e => if h : fiber (G.src e) ≠ fiber (G.dst e) then y (edgeEquiv G fiber ⟨e, h⟩) else 0

@[simp] theorem projectWord_extendWord (y : (quotient G fiber).EdgeWord) :
    projectWord G fiber (extendWord G fiber y) = y := by
  funext e
  simp [projectWord, extendWord, ((edgeEquiv G fiber).symm e).2]

/-- Repair a fiber-even demand using root-to-vertex paths within the fibers. -/
def repairWord (h : ConnectedFibers G fiber) (b : G.Demand) : G.EdgeWord :=
  ∑ v, b v • G.walkWord ((fiberRoute G fiber h v).map (includeFiber G fiber (fiber v)))

theorem projectWord_repairWord (h : ConnectedFibers G fiber) (b : G.Demand) :
    projectWord G fiber (repairWord G fiber h b) = 0 := by
  funext e
  change (∑ v, b v • G.walkWord ((fiberRoute G fiber h v).map
    (includeFiber G fiber (fiber v)))) ((edgeEquiv G fiber).symm e).1 = 0
  simp only [Finset.sum_apply, Pi.smul_apply, walkWord_fiber_crossing, smul_zero,
    Finset.sum_const_zero]

theorem boundary_repairWord (h : ConnectedFibers G fiber) (b : G.Demand)
    (hb : ∀ q, fiberSum G fiber b q = 0) :
    G.boundary (repairWord G fiber h b) = b := by
  have hroot : (∑ v, b v • G.vertexUnit (fiberRoot G fiber h (fiber v)).1) =
      ∑ q, fiberSum G fiber b q • G.vertexUnit (fiberRoot G fiber h q).1 := by
    unfold fiberSum
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.sum_eq_single (fiber v)]
    · simp
    · intro q hq hqv
      simp [Ne.symm hqv]
    · simp
  have hunits : (∑ v, b v • G.vertexUnit v) = b := by
    funext u
    simp [vertexUnit, Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold repairWord
  rw [map_sum]
  simp_rw [map_smul, boundary_walkWord, smul_add]
  rw [Finset.sum_add_distrib]
  change (∑ v, b v • G.vertexUnit (fiberRoot G fiber h (fiber v)).1) +
    (∑ v, b v • G.vertexUnit v) = b
  rw [hroot, hunits]
  simp [hb]

/-- Connected fibers suffice to lift every quotient even word. -/
theorem project_surjective (h : ConnectedFibers G fiber) :
    Function.Surjective (project G fiber) := by
  intro y
  let x := extendWord G fiber y.1
  let b := G.boundary x
  have hb : ∀ q, fiberSum G fiber b q = 0 := by
    intro q
    rw [← boundary_projectWord]
    change (quotient G fiber).boundary (projectWord G fiber (extendWord G fiber y.1)) _ = 0
    rw [projectWord_extendWord]
    exact congrFun y.2 _
  have heven : G.boundary (x + repairWord G fiber h b) = 0 := by
    rw [map_add, boundary_repairWord G fiber h b hb]
    exact word_add_self b
  refine ⟨⟨x + repairWord G fiber h b, heven⟩, ?_⟩
  apply Subtype.ext
  change projectWord G fiber (x + repairWord G fiber h b) = y.1
  rw [map_add, projectWord_repairWord, add_zero]
  exact projectWord_extendWord G fiber y.1

/-- All joint laws depending on crossing coordinates are preserved. -/
theorem density_project (h : ConnectedFibers G fiber)
    (P : (quotient G fiber).CycleSpace → Prop) :
    Finite.density (fun x : G.CycleSpace => P (project G fiber x)) = Finite.density P :=
  density_surjective_linear (project G fiber) (project_surjective G fiber h) P

/-- A source walk projects to quotient reachability; internal steps vanish. -/
theorem reachable_of_walk {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) :
    (quotient G fiber).toSimpleGraph.Reachable (vertexEquiv (fiber u))
      (vertexEquiv (fiber v)) := by
  induction p with
  | nil => exact .refl _
  | @cons a b c hab p ih =>
      have hstep : (quotient G fiber).toSimpleGraph.Reachable
          (vertexEquiv (fiber a)) (vertexEquiv (fiber b)) := by
        by_cases hsame : fiber a = fiber b
        · rw [hsame]
        · obtain ⟨e, he⟩ := hab.2
          have hcross : fiber (G.src e) ≠ fiber (G.dst e) := by
            rcases he with h | h
            · simpa only [h.1, h.2] using hsame
            · simpa only [h.1, h.2] using Ne.symm hsame
          apply SimpleGraph.Adj.reachable
          refine ⟨fun heq => hsame (vertexEquiv.injective heq), edgeEquiv G fiber ⟨e, hcross⟩, ?_⟩
          rcases he with h | h
          · left
            simp [quotient, h.1, h.2]
          · right
            simp [quotient, h.1, h.2]
      exact hstep.trans ih

/-- Contracting nonempty connected fibers preserves source connectedness. -/
theorem quotient_connected (hG : G.toSimpleGraph.Connected)
    (h : ConnectedFibers G fiber) : (quotient G fiber).toSimpleGraph.Connected := by
  letI : Nonempty (quotient G fiber).Vertex := by
    obtain ⟨v⟩ := hG.nonempty
    exact ⟨vertexEquiv (fiber v)⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨qa, rfl⟩ := vertexEquiv.surjective a
  obtain ⟨qb, rfl⟩ := vertexEquiv.surjective b
  obtain ⟨p⟩ := hG.preconnected (fiberRoot G fiber h qa).1 (fiberRoot G fiber h qb).1
  have hp := reachable_of_walk G fiber p
  simpa only [(fiberRoot G fiber h qa).2, (fiberRoot G fiber h qb).2] using hp

end Erdos1016.FiniteMultiGraph.ConnectedContraction

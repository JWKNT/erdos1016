import Erdos1016.Graph.Cubicization.IncidenceNetwork

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Cycle-space preservation under incidence-path expansion

Restriction to the original edge labels is a linear bijection. Existence is
the incidence-solvability theorem applied to the connected internal paths;
uniqueness follows by summing boundary over each path prefix. Neither claim
uses a rank formula or assumes the expansion preserves cycle space.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ShortProof.IncidencePaths

open BoundaryTrace
local instance incidenceCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph) (W : Finset G.Edge)

def pathNetwork : Network (Vertex G W) (PathEdge G W) where
  src := pathSource G W
  dst := pathTarget G W
  noLoops := pathSource_ne_target G W

def externalNetwork : Network (Vertex G W) G.Edge where
  src := source G W
  dst := target G W
  noLoops := source_ne_target G W

theorem boundary_parts (x : (network G W).Word) :
    (network G W).boundary x =
      (pathNetwork G W).boundary (fun e => x (Sum.inl e)) +
      (externalNetwork G W).boundary (fun e => x (Sum.inr e)) := by
  funext v
  simp only [Network.boundary_apply, network, pathNetwork, externalNetwork,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
  abel

lemma original_boundary_push (x : G.Word) :
    G.boundary x = push G.src x + push G.dst x := by
  funext v
  simp only [PhysicalGraph.boundary, LinearMap.coe_mk, AddHom.coe_mk,
    push_apply, Pi.add_apply, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
  · by_cases h : G.src e = v <;> simp [h]
  · by_cases h : G.dst e = v <;> simp [h]

lemma push_contract_path_boundary (x : (pathNetwork G W).Word) :
    push (contract G W) ((pathNetwork G W).boundary x) = 0 := by
  rw [Network.boundary, LinearMap.add_apply, map_add, push_comp, push_comp]
  change push (fun e : PathEdge G W => e.1) x + push (fun e : PathEdge G W => e.1) x = 0
  exact word_add_self _

lemma push_contract_external_boundary (x : G.Word) :
    push (contract G W) ((externalNetwork G W).boundary x) = G.boundary x := by
  rw [Network.boundary, LinearMap.add_apply, map_add, push_comp, push_comp,
    original_boundary_push]
  rfl

/-- Summing expanded vertex equations in a row gives the original equation. -/
theorem boundary_original_projection (x : (network G W).Word) :
    G.boundary (fun e => x (Sum.inr e)) = push (contract G W) ((network G W).boundary x) := by
  rw [boundary_parts, map_add, push_contract_path_boundary,
    push_contract_external_boundary, zero_add]

/-- Restrict an even expanded word to the original physical edges. -/
def projectCycles : (network G W).CycleSpace →ₗ[F₂] G.CycleSpace where
  toFun x := ⟨fun e => x.1 (Sum.inr e), by
    rw [LinearMap.mem_ker, boundary_original_projection]
    have hx : (network G W).boundary x.1 = 0 := x.2
    rw [hx, map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def internalRowHom (v : G.Vertex) :
    SimpleGraph.pathGraph (pathSize G W v) →g (pathNetwork G W).graph where
  toFun i := ⟨v, i⟩
  map_rel' := by
    intro i j hij
    rcases SimpleGraph.pathGraph_adj.mp hij with h | h
    · have hi : i.val < pathSize G W v - 1 := by have hj := j.isLt; omega
      exact ⟨⟨v, ⟨i.val, hi⟩⟩, Or.inl ⟨rfl, vertex_ext G W rfl h⟩⟩
    · have hj : j.val < pathSize G W v - 1 := by have hi := i.isLt; omega
      exact ⟨⟨v, ⟨j.val, hj⟩⟩, Or.inr ⟨rfl, vertex_ext G W rfl h⟩⟩

lemma internal_row_reachable {a b : Vertex G W} (h : a.1 = b.1) :
    (pathNetwork G W).graph.Reachable a b := by
  rcases a with ⟨v, i⟩
  rcases b with ⟨w, j⟩
  dsimp at h
  subst w
  exact (SimpleGraph.pathGraph_preconnected _ i j).map (internalRowHom G W v)

lemma path_component_representative (a : Vertex G W) :
    (pathNetwork G W).component a =
      (pathNetwork G W).component (representative G W a.1) :=
  SimpleGraph.ConnectedComponent.sound (internal_row_reachable G W rfl)

/-- The external demand of an original even word has zero total on every
internal path component, so it has an internal completion. -/
lemma external_boundary_mem_range (x : G.CycleSpace) :
    (externalNetwork G W).boundary x.1 ∈ LinearMap.range (pathNetwork G W).boundary := by
  apply ((pathNetwork G W).mem_range_boundary_iff _).mpr
  let f : G.Vertex → (pathNetwork G W).Component :=
    fun v => (pathNetwork G W).component (representative G W v)
  have hs : (pathNetwork G W).component ∘ (externalNetwork G W).src = f ∘ G.src := by
    funext e
    exact path_component_representative G W (source G W e)
  have ht : (pathNetwork G W).component ∘ (externalNetwork G W).dst = f ∘ G.dst := by
    funext e
    exact path_component_representative G W (target G W e)
  change push (pathNetwork G W).component ((externalNetwork G W).boundary x.1) = 0
  rw [Network.boundary, LinearMap.add_apply, map_add, push_comp, push_comp, hs, ht,
    ← push_comp, ← push_comp, ← map_add, ← original_boundary_push]
  have hx : G.boundary x.1 = 0 := x.2
  rw [hx, map_zero]

theorem projectCycles_surjective : Function.Surjective (projectCycles G W) := by
  intro x
  obtain ⟨y, hy⟩ := external_boundary_mem_range G W x
  let z : (network G W).Word := Sum.elim y x.1
  have hz : (network G W).boundary z = 0 := by
    rw [boundary_parts]
    change (pathNetwork G W).boundary y + (externalNetwork G W).boundary x.1 = 0
    rw [hy, word_add_self]
  exact ⟨⟨z, hz⟩, rfl⟩

/-- A prefix boundary sum recovers its unique departing internal edge. -/
lemma path_prefix_boundary (x : (pathNetwork G W).Word) (e : PathEdge G W) :
    push (fun a : Vertex G W => decide (a.1 = e.1 ∧ a.2.val ≤ e.2.val))
      ((pathNetwork G W).boundary x) true = x e := by
  let f : Vertex G W → Bool := fun a => decide (a.1 = e.1 ∧ a.2.val ≤ e.2.val)
  change push f ((pathNetwork G W).boundary x) true = x e
  rw [Network.boundary, LinearMap.add_apply, map_add, push_comp, push_comp]
  simp only [Pi.add_apply, push_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single e]
  · simp [f, pathNetwork, pathSource, pathTarget]
  · intro k hk hke
    by_cases hv : k.1 = e.1
    · have hi : k.2.val ≠ e.2.val := by
        intro h
        apply hke
        rcases k with ⟨v, i⟩
        rcases e with ⟨w, j⟩
        dsimp at hv h
        subst w
        exact congrArg (Sigma.mk v) (Fin.ext h)
      by_cases hle : k.2.val ≤ e.2.val
      · have hle' : k.2.val + 1 ≤ e.2.val := by omega
        simp [f, pathNetwork, pathSource, pathTarget, hv, hle, hle', bit_add_self]
      · have hle' : ¬ k.2.val + 1 ≤ e.2.val := by omega
        simp [f, pathNetwork, pathSource, pathTarget, hv, hle, hle']
    · simp [f, pathNetwork, pathSource, pathTarget, hv]
  · simp

/-- An even word supported on the internal paths is zero. -/
theorem internal_boundary_injective : Function.Injective (pathNetwork G W).boundary := by
  intro x y h
  funext e
  rw [← path_prefix_boundary G W x e, ← path_prefix_boundary G W y e, h]

theorem projectCycles_injective : Function.Injective (projectCycles G W) := by
  intro x y h
  have hext : (fun e => x.1 (Sum.inr e)) = (fun e => y.1 (Sum.inr e)) :=
    congrArg Subtype.val h
  have hx : (network G W).boundary x.1 = 0 := x.2
  have hy : (network G W).boundary y.1 = 0 := y.2
  rw [boundary_parts] at hx hy
  rw [hext] at hx
  have hint : (fun e => x.1 (Sum.inl e)) = (fun e => y.1 (Sum.inl e)) := by
    apply internal_boundary_injective G W
    exact add_right_cancel (hx.trans hy.symm)
  apply Subtype.ext
  funext e
  cases e with
  | inl e => exact congrFun hint e
  | inr e => exact congrFun hext e

/-- The actual binary cycle spaces are linearly equivalent, with original
edge coordinates unchanged. -/
def cycleSpaceEquiv : (network G W).CycleSpace ≃ₗ[F₂] G.CycleSpace :=
  LinearEquiv.ofBijective (projectCycles G W)
    ⟨projectCycles_injective G W, projectCycles_surjective G W⟩

@[simp] theorem cycleSpaceEquiv_original_edge (x : (network G W).CycleSpace) (e : G.Edge) :
    (cycleSpaceEquiv G W x).1 e = x.1 (Sum.inr e) := rfl

/-- Uniform counting transports every event on original edge coordinates. -/
theorem density_original_projection (P : G.CycleSpace → Prop) :
    Finite.density (fun x : (network G W).CycleSpace => P (cycleSpaceEquiv G W x)) =
      Finite.density P := by
  apply Finite.density_equiv (cycleSpaceEquiv G W).toEquiv
  intro x
  rfl

end Erdos1016.ShortProof.IncidencePaths

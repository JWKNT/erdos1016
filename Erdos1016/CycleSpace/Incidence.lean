import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Erdos1016.Linear.Pushforward

set_option autoImplicit false

/-!
# Incidence solvability on an actual finite labelled network

Parallel edges are permitted; loops are not. The boundary map is formed from
the actual endpoint maps. Its image is PROVED to be the demands summing to
zero in each connected component. No Euler formula, dimension formula, or
untranslated graph-theoretic input is used for that assertion.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure Network (V E : Type*) where
  src : E → V
  dst : E → V
  noLoops : ∀ e, src e ≠ dst e

namespace Network

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev Word (_N : Network V E) := E → Bit
abbrev Demand (_N : Network V E) := V → Bit

def graph (N : Network V E) : SimpleGraph V where
  Adj u v := ∃ e, (N.src e = u ∧ N.dst e = v) ∨
    (N.src e = v ∧ N.dst e = u)
  symm := by
    rintro u v ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  loopless := by
    rintro v ⟨e, h | h⟩ <;> exact N.noLoops e (h.1.trans h.2.symm)

def selectedGraph (N : Network V E) (x : N.Word) : SimpleGraph V where
  Adj u v := ∃ e, x e ≠ 0 ∧
    ((N.src e = u ∧ N.dst e = v) ∨ (N.src e = v ∧ N.dst e = u))
  symm := by
    rintro u v ⟨e, hx, h | h⟩
    · exact ⟨e, hx, Or.inr h⟩
    · exact ⟨e, hx, Or.inl h⟩
  loopless := by
    rintro v ⟨e, _, h | h⟩ <;> exact N.noLoops e (h.1.trans h.2.symm)

def IsForest (N : Network V E) (x : N.Word) : Prop :=
  (N.selectedGraph x).IsAcyclic

def boundary (N : Network V E) : N.Word →ₗ[Bit] N.Demand :=
  push N.src + push N.dst

@[simp] theorem boundary_apply (N : Network V E) (x : N.Word) (v : V) :
    N.boundary x v =
      (∑ e, if N.src e = v then x e else 0) +
      (∑ e, if N.dst e = v then x e else 0) := by
  simp only [boundary, LinearMap.add_apply, Pi.add_apply, push_apply]



@[simp] theorem boundary_unit (N : Network V E) (e : E) :
    N.boundary (unitWord e) = unitWord (N.src e) + unitWord (N.dst e) := by
  simp [boundary]

@[simp] theorem total_boundary (N : Network V E) (x : N.Word) :
    total (N.boundary x) = 0 := by
  change total (push N.src x + push N.dst x) = 0
  rw [map_add, total_push, total_push, bit_add_self]

abbrev CycleSpace (N : Network V E) := LinearMap.ker N.boundary

noncomputable instance cycleSpaceFintype (N : Network V E) :
    Fintype N.CycleSpace := Fintype.ofFinite _

abbrev Component (N : Network V E) := N.graph.ConnectedComponent

noncomputable instance componentFintype (N : Network V E) :
    Fintype N.Component := Fintype.ofFinite _

def component (N : Network V E) (v : V) : N.Component :=
  N.graph.connectedComponentMk v

@[simp] theorem component_src_eq_dst (N : Network V E) (e : E) :
    N.component (N.src e) = N.component (N.dst e) := by
  apply SimpleGraph.ConnectedComponent.sound
  exact SimpleGraph.Adj.reachable (show N.graph.Adj (N.src e) (N.dst e) from
    ⟨e, Or.inl ⟨rfl, rfl⟩⟩)

/-- One equation per actual component, including isolated vertices. -/
def componentBoundary (N : Network V E) : N.Demand →ₗ[Bit] (N.Component → Bit) :=
  push N.component

@[simp] theorem componentBoundary_boundary (N : Network V E) (x : N.Word) :
    N.componentBoundary (N.boundary x) = 0 := by
  change push N.component (push N.src x + push N.dst x) = 0
  rw [map_add, push_comp, push_comp]
  have heq : N.component ∘ N.src = N.component ∘ N.dst := by
    funext e
    exact N.component_src_eq_dst e
  rw [heq, word_add_self]

/-- The two endpoints of any actual path give a realizable binary demand. -/
theorem pair_mem_range_of_walk (N : Network V E) {u v : V}
    (p : N.graph.Walk u v) :
    unitWord u + unitWord v ∈ LinearMap.range N.boundary := by
  induction p with
  | nil =>
      simpa only [word_add_self] using (LinearMap.range N.boundary).zero_mem
  | @cons u v w huv p ih =>
      have hedge : unitWord u + unitWord v ∈ LinearMap.range N.boundary := by
        rcases huv with ⟨e, h | h⟩
        · refine ⟨unitWord e, ?_⟩
          simp only [boundary_unit, h.1, h.2]
        · refine ⟨unitWord e, ?_⟩
          simp only [boundary_unit, h.1, h.2, add_comm]
      have hsum := (LinearMap.range N.boundary).add_mem hedge ih
      have heq : (unitWord u + unitWord v) + (unitWord v + unitWord w) =
          unitWord u + unitWord w := by
        calc
          (unitWord u + unitWord v) + (unitWord v + unitWord w) =
              unitWord u + unitWord w + (unitWord v + unitWord v) := by abel
          _ = unitWord u + unitWord w := by rw [word_add_self, add_zero]
      rwa [heq] at hsum

def representative (N : Network V E) (c : N.Component) : V :=
  Classical.choose c.exists_rep

@[simp] theorem component_representative (N : Network V E) (c : N.Component) :
    N.component (N.representative c) = c :=
  Classical.choose_spec c.exists_rep

theorem pair_representative_mem_range (N : Network V E) (v : V) :
    unitWord v + unitWord (N.representative (N.component v)) ∈
      LinearMap.range N.boundary := by
  have hreach : N.graph.Reachable v (N.representative (N.component v)) := by
    apply SimpleGraph.ConnectedComponent.exact
    exact (N.component_representative (N.component v)).symm
  obtain ⟨p⟩ := hreach
  exact N.pair_mem_range_of_walk p

/-- Incidence solvability is proved from paths and finite pushforward, not
assumed as a component-count axiom. -/
theorem mem_range_boundary_iff (N : Network V E) (t : N.Demand) :
    t ∈ LinearMap.range N.boundary ↔ N.componentBoundary t = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact N.componentBoundary_boundary x
  · intro ht
    have hsum : (∑ v, t v •
        (unitWord v + unitWord (N.representative (N.component v)))) ∈
        LinearMap.range N.boundary := by
      apply Submodule.sum_mem
      intro v _
      exact (LinearMap.range N.boundary).smul_mem (t v)
        (N.pair_representative_mem_range v)
    have hid : (∑ v, t v • unitWord v) = t := push_id t
    have hroot : (∑ v, t v • unitWord (N.representative (N.component v))) = 0 := by
      change push (N.representative ∘ N.component) t = 0
      rw [← push_comp]
      change push N.representative (N.componentBoundary t) = 0
      rw [ht, map_zero]
    simpa only [smul_add, Finset.sum_add_distrib, hid, hroot, add_zero] using hsum

/-- The form used to construct an ACTUAL exterior completing word. -/
theorem exists_word_of_component_even (N : Network V E) (t : N.Demand)
    (ht : N.componentBoundary t = 0) :
    ∃ x : N.Word, N.boundary x = t :=
  (N.mem_range_boundary_iff t).2 ht



end Network
end Erdos1016.BoundaryTrace

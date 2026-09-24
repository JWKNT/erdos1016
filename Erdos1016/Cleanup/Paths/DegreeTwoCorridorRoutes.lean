import Erdos1016.Cleanup.Corridors.EndpointBoundary
import Erdos1016.Cleanup.Compression.DegreeTwoParity
import Mathlib.Data.List.ChainOfFn

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.DegreeTwoCorridorRoutes

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute
open Erdos1016.Proof.EndpointBoundary
open Erdos1016.Proof.DegreeTwoParity

variable {G : PhysicalGraph}

/-- The indexed step at edge position `i` in a corridor. -/
def corridorStepAt (C : PhysicalCorridor G) (i : Fin C.edges.length) :
    PathStep (routeGraph G) :=
  let e : G.Edge := C.edges.get i
  let u : G.Vertex := C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩
  let v : G.Vertex := C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩
  { startVertex := u
    edge := e
    endVertex := v
    endpoints := C.step i }

private theorem corridorSteps_eq_ofFn (C : PhysicalCorridor G) :
    corridorSteps C = List.ofFn (corridorStepAt C) := by
  rfl

/-- Every indexed internal vertex has ambient physical degree two.  The
indexing is by the edge immediately before the vertex; hence `i` ranges over
`0 .. edges.length - 2`. -/
def InternalVerticesDegreeTwo (C : PhysicalCorridor G) : Prop :=
  ∀ i : Fin (C.edges.length - 1),
    G.degree (C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩) = 2

/-- Consecutive corridor steps satisfy the exact linked two-incidence
identity.  The degree-two star is exhausted by the two recorded edge labels;
`PhysicalCorridor.edges_nodup` supplies their distinctness. -/
theorem corridorSteps_chain_of_internal_degree_two
    (C : PhysicalCorridor G) (hdegree : InternalVerticesDegreeTwo C) :
    List.Chain' PathStep.Link (corridorSteps C) := by
  rw [corridorSteps_eq_ofFn, List.chain'_ofFn]
  intro i hi
  let i₀ : Fin C.edges.length := ⟨i, Nat.lt_of_succ_lt hi⟩
  let i₁ : Fin C.edges.length := ⟨i + 1, hi⟩
  let a := corridorStepAt C i₀
  let b := corridorStepAt C i₁
  let mid : G.Vertex := C.vertices.get ⟨i + 1, by rw [C.vertices_length]; omega⟩
  have hmeet : a.endVertex = b.startVertex := by
    rfl
  have h₁ : G.incident a.edge mid := by
    dsimp [a, corridorStepAt, mid]
    have hs := C.step i₀
    rcases hs with hs | hs
    · exact Or.inr hs.2
    · exact Or.inl hs.2
  have h₂ : G.incident b.edge mid := by
    dsimp [b, corridorStepAt, mid]
    have hs := C.step i₁
    rcases hs with hs | hs
    · exact Or.inl hs.1
    · exact Or.inr hs.1
  have hne : a.edge ≠ b.edge := by
    intro he
    have hij : i₀ = i₁ := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hv := congrArg Fin.val hij
    simp [i₀, i₁] at hv
  have hdeg : G.degree mid = 2 := by
    dsimp [mid]
    exact hdegree ⟨i, by omega⟩
  refine ⟨hmeet, ?_⟩
  intro y
  change G.boundary y mid = y a.edge + y b.edge
  exact DegreeTwoParity.boundary_eq_two_of_degree_two
    G y mid a.edge b.edge h₁ h₂ hne hdeg

/- A nonempty corridor gives a nonempty indexed step list. -/
theorem corridorSteps_ne_nil (C : PhysicalCorridor G) (hC : C.edges ≠ []) :
    corridorSteps C ≠ [] := by
  intro hnil
  have := congrArg List.length hnil
  simp [corridorSteps] at this
  exact hC this

/-- The first indexed step starts at the corridor's recorded head. -/
theorem corridorSteps_head_start (C : PhysicalCorridor G) (hC : C.edges ≠ []) :
    ((corridorSteps C).head (corridorSteps_ne_nil C hC)).startVertex =
      corridorStart C := by
  have hlen : 0 < C.edges.length := List.length_pos_iff.mpr hC
  have hneOf : List.ofFn (corridorStepAt C) ≠ [] := by
    simpa [corridorSteps_eq_ofFn] using corridorSteps_ne_nil C hC
  have hfirst' : (List.ofFn (corridorStepAt C)).head hneOf =
      corridorStepAt C ⟨0, hlen⟩ := by
    rw [List.head_eq_getElem_zero]
    simp [List.getElem_ofFn, hlen]
  have hfirst : (corridorSteps C).head (corridorSteps_ne_nil C hC) =
      corridorStepAt C ⟨0, hlen⟩ := by
    simpa only [corridorSteps_eq_ofFn] using hfirst'
  rw [hfirst]
  simp [corridorStepAt, corridorStart, List.head_eq_getElem_zero,
    SingleCorridorRoute.routeGraph]

/-- The last indexed step finishes at the corridor's recorded final vertex. -/
theorem corridorSteps_last_end (C : PhysicalCorridor G) (hC : C.edges ≠ []) :
    ((corridorSteps C).getLast (corridorSteps_ne_nil C hC)).endVertex =
      corridorFinish C := by
  cases hn : C.edges.length with
  | zero => exact (hC (List.length_eq_zero_iff.mp hn)).elim
  | succ n =>
      have hneOf : List.ofFn (corridorStepAt C) ≠ [] := by
        simpa [corridorSteps_eq_ofFn] using corridorSteps_ne_nil C hC
      let iLast : Fin C.edges.length := ⟨n, by omega⟩
      have hlast' : (List.ofFn (corridorStepAt C)).getLast hneOf =
          corridorStepAt C iLast := by
        rw [List.getLast_eq_getElem]
        rw [List.getElem_ofFn]
        congr 1
        apply Fin.ext
        simp [iLast, hn]
      have hlast : (corridorSteps C).getLast (corridorSteps_ne_nil C hC) =
          corridorStepAt C iLast := by
        simpa only [corridorSteps_eq_ofFn] using hlast'
      rw [hlast]
      have hverts : C.vertices.length = C.edges.length + 1 := C.vertices_length
      have hiLast : (iLast : ℕ) = n := by simp [iLast]
      simp [corridorStepAt, corridorFinish, List.getLast_eq_getElem,
        SingleCorridorRoute.routeGraph, hverts, hn, iLast, hiLast]



end Erdos1016.Proof.DegreeTwoCorridorRoutes

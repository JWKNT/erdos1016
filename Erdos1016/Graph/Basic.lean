import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Erdos1016.CycleSpace.Parity

set_option autoImplicit false

/-!
# Finite physical simple graphs

Vertices and individually labelled, unoriented physical edges are finite.
`src` and `dst` choose an orientation only to store each edge once. The
`simple` field excludes parallel copies in either orientation.

Cycle rank is DEFINED as the binary boundary-kernel dimension. The Euler
identity `rank = edges - vertices + components` is a later bridge obligation;
it is not silently installed as an axiom.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016

structure PhysicalGraph where
  vertexCount : ℕ
  edgeCount : ℕ
  src : Fin edgeCount → Fin vertexCount
  dst : Fin edgeCount → Fin vertexCount
  noLoops : ∀ e, src e ≠ dst e
  simple : ∀ e f,
    ((src e = src f ∧ dst e = dst f) ∨
     (src e = dst f ∧ dst e = src f)) → e = f

namespace PhysicalGraph

abbrev Vertex (G : PhysicalGraph) := Fin G.vertexCount
abbrev Edge (G : PhysicalGraph) := Fin G.edgeCount
abbrev Word (G : PhysicalGraph) := EdgeWord G.Edge
abbrev Demand (G : PhysicalGraph) := G.Vertex → F₂

def incident (G : PhysicalGraph) (e : G.Edge) (v : G.Vertex) : Prop :=
  G.src e = v ∨ G.dst e = v

/-- The binary boundary operator on actual physical edges. -/
def boundary (G : PhysicalGraph) : G.Word →ₗ[F₂] G.Demand where
  toFun x v := ∑ e,
    ((if G.src e = v then x e else 0) +
     (if G.dst e = v then x e else 0))
  map_add' x y := by
    funext v
    change (∑ e, ((if G.src e = v then x e + y e else 0) +
      (if G.dst e = v then x e + y e else 0))) = _ + _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      simp [hs, ht] <;> ring
  map_smul' a x := by
    funext v
    change (∑ e, ((if G.src e = v then a * x e else 0) +
      (if G.dst e = v then a * x e else 0))) =
      a * ∑ e, ((if G.src e = v then x e else 0) +
      (if G.dst e = v then x e else 0))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
      simp [hs, ht] <;> ring

abbrev CycleSpace (G : PhysicalGraph) := LinearMap.ker G.boundary

def cycleRank (G : PhysicalGraph) : ℕ :=
  Module.finrank F₂ G.CycleSpace

noncomputable instance cycleSpaceFintype (G : PhysicalGraph) :
    Fintype G.CycleSpace := Fintype.ofFinite _

abbrev TJoin (G : PhysicalGraph) (t : G.Demand) :=
  Parity.Fiber G.boundary t

/-- The spanning simple graph selected by a physical word; isolates remain. -/
def selectedGraph (G : PhysicalGraph) (x : G.Word) : SimpleGraph G.Vertex where
  Adj u v := ∃ e, x e ≠ 0 ∧
    ((G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u))
  symm := by
    intro u v h
    rcases h with ⟨e, hx, h | h⟩
    · exact ⟨e, hx, Or.inr h⟩
    · exact ⟨e, hx, Or.inl h⟩
  loopless := by
    intro v h
    rcases h with ⟨e, _, h | h⟩
    · exact G.noLoops e (h.1.trans h.2.symm)
    · exact G.noLoops e (h.1.trans h.2.symm)

def toSimpleGraph (G : PhysicalGraph) : SimpleGraph G.Vertex :=
  G.selectedGraph (fun _ => 1)

def IsConnected (G : PhysicalGraph) : Prop := G.toSimpleGraph.Connected

def IsForest (G : PhysicalGraph) (x : G.Word) : Prop :=
  (G.selectedGraph x).IsAcyclic

def edgeSupport (G : PhysicalGraph) (x : G.Word) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => x e ≠ 0

def wordLength (G : PhysicalGraph) (x : G.Word) : ℕ :=
  (G.edgeSupport x).card

def usedVertices (G : PhysicalGraph) (x : G.Word) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v => ∃ e, x e ≠ 0 ∧ G.incident e v

def selectedDegree (G : PhysicalGraph) (x : G.Word) (v : G.Vertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun e => x e ≠ 0 ∧ G.incident e v).card

def degree (G : PhysicalGraph) (v : G.Vertex) : ℕ :=
  G.selectedDegree (fun _ => 1) v

/-- A circuit is a nonempty connected two-regular selected subgraph.
The explicit zero-boundary field makes the finite-state injection immediate. -/
def IsCycleWord (G : PhysicalGraph) (x : G.Word) : Prop :=
  x ≠ 0 ∧ G.boundary x = 0 ∧
  ((G.selectedGraph x).induce (↑(G.usedVertices x) : Set G.Vertex)).Connected ∧
  ∀ v ∈ G.usedVertices x, G.selectedDegree x v = 2

def CycleWord (G : PhysicalGraph) := {x : G.Word // G.IsCycleWord x}

noncomputable instance cycleWordFintype (G : PhysicalGraph) :
    Fintype G.CycleWord := by
  classical
  unfold CycleWord
  exact Fintype.ofFinite _

lemma tjoin_natCard (G : PhysicalGraph) {t : G.Demand} (x : G.TJoin t) :
    Nat.card (G.TJoin t) = 2 ^ G.cycleRank :=
  Parity.fiber_natCard G.boundary x

lemma cycleSpace_card (G : PhysicalGraph) :
    Fintype.card G.CycleSpace = 2 ^ G.cycleRank := by
  have h := Module.card_eq_pow_finrank (K := F₂) (V := G.CycleSpace)
  simpa [F₂, cycleRank] using h





lemma wordLength_le (G : PhysicalGraph) (x : G.Word) :
    G.wordLength x ≤ G.edgeCount := by
  simpa [wordLength] using Finset.card_le_univ (G.edgeSupport x)

@[simp] lemma wordLength_zero (G : PhysicalGraph) : G.wordLength 0 = 0 := by
  simp [wordLength, edgeSupport]

end PhysicalGraph
end Erdos1016

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Erdos1016.Graph.Multigraph.Components

set_option autoImplicit false

/-!
# Forest events and incidence degrees of labelled multigraphs

A multigraph forest has no selected loop or parallel pair as well as no cycle
in its underlying simple graph. Forgetting the first two conditions would
incorrectly treat loops and digons as forests. Degrees count both incidences
of every loop. All probabilities use the uniform binary cycle space.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

/-- The underlying simple graph of an edge word. Labels are retained separately. -/
def selectedGraph (G : FiniteMultiGraph) (x : G.EdgeWord) : SimpleGraph G.Vertex where
  Adj u v := u ≠ v ∧ ∃ e, x e ≠ 0 ∧
    ((G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u))
  symm := by
    rintro u v ⟨hne, e, he, h | h⟩
    · exact ⟨hne.symm, e, he, Or.inr h⟩
    · exact ⟨hne.symm, e, he, Or.inl h⟩
  loopless := by rintro v ⟨h, _⟩; exact h rfl

/-- Selected incidence degree; a loop contributes two. -/
def selectedDegree (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) : ℕ := by
  classical
  let S := Finset.univ.filter fun e : G.Edge => x e ≠ 0
  exact (S.filter fun e => G.src e = v).card + (S.filter fun e => G.dst e = v).card

/-- Ambient incidence degree. -/
def degree (G : FiniteMultiGraph) (v : G.Vertex) : ℕ :=
  selectedDegree G (fun _ => 1) v

/-- Acyclicity of the labelled selected subgraph, including length-one and
length-two multigraph cycles. -/
def IsForestWord (G : FiniteMultiGraph) (x : G.EdgeWord) : Prop :=
  (∀ e, x e ≠ 0 → G.src e ≠ G.dst e) ∧
  (∀ e f, x e ≠ 0 → x f ≠ 0 →
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
     (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f) ∧
  (G.selectedGraph x).IsAcyclic

/-- The additional maximum-degree-two condition for a linear forest. -/
def IsLinearForestWord (G : FiniteMultiGraph) (x : G.EdgeWord) : Prop :=
  G.IsForestWord x ∧ ∀ v, G.selectedDegree x v ≤ 2

/-- Edges internal to a vertex region. -/
def internalEdges (G : FiniteMultiGraph) (U : Finset G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => G.src e ∈ U ∧ G.dst e ∈ U

/-- Labelled edges crossing a vertex region; loops never cross. -/
def cutEdges (G : FiniteMultiGraph) (U : Finset G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (G.src e ∈ U ∧ G.dst e ∉ U) ∨ (G.src e ∉ U ∧ G.dst e ∈ U)

/-- Restrict an edge word and extend it by zero outside the retained labels. -/
def restrictEdges (G : FiniteMultiGraph) (E : Finset G.Edge) (x : G.EdgeWord) :
    G.EdgeWord := fun e => if e ∈ E then x e else 0

/-- Probability of a forest on the edges internal to a vertex region. -/
def regionForestProbability (G : FiniteMultiGraph) (U : Finset G.Vertex) : ℝ := by
  classical
  exact ((Finset.univ.filter fun x : G.CycleSpace =>
    G.IsForestWord (G.restrictEdges (G.internalEdges U) x.1)).card : ℝ) /
      (2 : ℝ) ^ G.cycleRank

@[simp] theorem selectedGraph_zero (G : FiniteMultiGraph) :
    G.selectedGraph 0 = ⊥ := by
  ext u v
  simp [selectedGraph]

@[simp] theorem selectedDegree_zero (G : FiniteMultiGraph) (v : G.Vertex) :
    G.selectedDegree 0 v = 0 := by
  simp [selectedDegree]

theorem zero_isForestWord (G : FiniteMultiGraph) : G.IsForestWord 0 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [selectedGraph_zero]
  exact SimpleGraph.isAcyclic_bot

theorem zero_isLinearForestWord (G : FiniteMultiGraph) : G.IsLinearForestWord 0 :=
  ⟨G.zero_isForestWord, by simp⟩

/-- Foresthood is hereditary under deletion of labelled edges. -/
theorem IsForestWord.mono {G : FiniteMultiGraph} {x y : G.EdgeWord}
    (hx : G.IsForestWord x) (hsub : ∀ e, y e ≠ 0 → x e ≠ 0) :
    G.IsForestWord y := by
  refine ⟨fun e he => hx.1 e (hsub e he), ?_, ?_⟩
  · intro e f he hf h
    exact hx.2.1 e f (hsub e he) (hsub f hf) h
  · let f : G.selectedGraph y →g G.selectedGraph x := {
      toFun := id
      map_rel' := by
        rintro u v ⟨huv, e, he, h⟩
        exact ⟨huv, e, hsub e he, h⟩ }
    intro v p hp
    exact hx.2.2 (p.map f)
      ((SimpleGraph.Walk.map_isCycle_iff_of_injective (by intro a b h; exact h)).2 hp)

theorem IsForestWord.restrictEdges {G : FiniteMultiGraph} {x : G.EdgeWord}
    (hx : G.IsForestWord x) (E : Finset G.Edge) :
    G.IsForestWord (G.restrictEdges E x) := by
  apply hx.mono
  intro e he
  by_cases hm : e ∈ E
  · simpa [FiniteMultiGraph.restrictEdges, hm] using he
  · simp [FiniteMultiGraph.restrictEdges, hm] at he

/-- Handshaking counts selected labelled edges, including loops twice. -/
theorem sum_selectedDegree (G : FiniteMultiGraph) (x : G.EdgeWord) :
    (∑ v, G.selectedDegree x v) =
      2 * (Finset.univ.filter fun e : G.Edge => x e ≠ 0).card := by
  classical
  let S := Finset.univ.filter fun e : G.Edge => x e ≠ 0
  have hs : (∑ v : G.Vertex, (S.filter fun e => G.src e = v).card) = S.card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hd : (∑ v : G.Vertex, (S.filter fun e => G.dst e = v).card) = S.card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  change (∑ v, ((S.filter fun e => G.src e = v).card +
    (S.filter fun e => G.dst e = v).card)) = 2 * S.card
  rw [Finset.sum_add_distrib, hs, hd]
  omega

/-- Ambient handshaking for the full multigraph. -/
theorem sum_degree (G : FiniteMultiGraph) : (∑ v, G.degree v) = 2 * G.edgeCount := by
  simpa [degree] using G.sum_selectedDegree (fun _ => 1)

@[simp] theorem selectedGraph_one (G : FiniteMultiGraph) :
    G.selectedGraph (fun _ => 1) = G.toSimpleGraph := by
  ext u v
  simp [selectedGraph, toSimpleGraph]

theorem regionForestProbability_bounds (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    0 ≤ G.regionForestProbability U ∧ G.regionForestProbability U ≤ 1 := by
  classical
  constructor
  · unfold regionForestProbability
    positivity
  · unfold regionForestProbability
    apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ G.cycleRank)).2
    have h := Finset.card_le_univ (Finset.univ.filter fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U) x.1))
    rw [G.cycleSpace_card] at h
    exact_mod_cast h

end Erdos1016.FiniteMultiGraph

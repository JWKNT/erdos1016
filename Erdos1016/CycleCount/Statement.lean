import Erdos1016.CycleCount.Bound
import Erdos1016.Extremal.SimpleGraphRealization
import Erdos1016.Graph.RankNormalization

set_option autoImplicit false

/-!
# The cycle-count bound in Mathlib's simple-graph language

Cycles are Mathlib `SimpleGraph.Walk.IsCycle` objects, counted by their edge
sets. The cyclomatic number is `edges - vertices + components`. The target is
stated for graphs on `Fin n`, which is equivalent up to relabelling to the
statement for all finite simple graphs. This file states the target and
derives it from the physical-graph bound.
-/

noncomputable section

namespace Erdos1016.CycleCount

/-- The edge sets of the cycles of a simple graph. A cycle is determined by
its edge set, so each cycle is counted once. -/
def cycleEdgeSets {V : Type*} (G : SimpleGraph V) : Set (Set (Sym2 V)) :=
  {s | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = {a | a ∈ p.edges}}

/-- The number of cycles of a finite simple graph. -/
def numCycles {V : Type*} (G : SimpleGraph V) : ℕ := (cycleEdgeSets G).ncard

/-- Every simple graph on `Fin n` whose cyclomatic number `r` is large has at
most `(1/2 + 21 / log₂ log₂ log₂ r) * 2^r` cycles. -/
def CycleCountStatement : Prop :=
  ∃ r₁ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    (numCycles G : ℝ) ≤
      (1 / 2 + 21 / Real.logb 2 (Real.logb 2 (Real.logb 2 (r : ℝ)))) * 2 ^ r

/-- Every edge of the simple graph of `P` is the pair of a physical edge. -/
theorem exists_physicalPair (P : PhysicalGraph) {a : Sym2 P.Vertex}
    (ha : a ∈ P.toSimpleGraph.edgeSet) :
    ∃ e : P.Edge, Nonbacktracking.physicalPair P e = a := by
  revert ha
  refine Sym2.inductionOn a ?_
  intro u v huv
  rcases huv with ⟨e, _, h | h⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inl h)⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inr h)⟩

/-- Distinct cycles of the simple graph of `P` have distinct cycle words. -/
theorem numCycles_toSimpleGraph_le (P : PhysicalGraph) :
    numCycles P.toSimpleGraph ≤ cycleCount P := by
  classical
  have hex : ∀ s : cycleEdgeSets P.toSimpleGraph, ∃ c : P.CycleWord,
      ∀ e : P.Edge, c.1 e ≠ 0 ↔ Nonbacktracking.physicalPair P e ∈ s.1 := by
    rintro ⟨s, v, p, hp, rfl⟩
    exact ⟨Nonbacktracking.cycleWordOfWalk P p hp,
      fun e => Nonbacktracking.walkWord_nonzero_iff P p e⟩
  choose f hf using hex
  have key : ∀ t t' : cycleEdgeSets P.toSimpleGraph, f t = f t' →
      ∀ a ∈ t.1, a ∈ t'.1 := by
    intro t t' htt a ha
    obtain ⟨w, q, hq, ht⟩ := t.2
    have haq : a ∈ q.edges := by
      rw [ht] at ha
      exact ha
    obtain ⟨e, rfl⟩ := exists_physicalPair P (q.edges_subset_edgeSet haq)
    have h1 := (hf t e).2 ha
    rw [htt] at h1
    exact (hf t' e).1 h1
  have hinj : Function.Injective f := by
    intro s s' h
    apply Subtype.ext
    ext a
    exact ⟨key s s' h a, key s' s h.symm a⟩
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold numCycles cycleCount
  rw [← Set.Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
  exact hcard

/-- Euler's formula for the physical realization, in Mathlib terms. -/
theorem physical_euler {n : ℕ} (G : SimpleGraph (Fin n)) :
    (Problem1016.physicalOfSimpleGraph G).cycleRank + n =
      Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  have hPG : (Problem1016.physicalOfSimpleGraph G).toSimpleGraph = G :=
    Problem1016.physicalOfSimpleGraph_toSimpleGraph G
  have hEuler : (Problem1016.physicalOfSimpleGraph G).cycleRank + n =
      (Problem1016.physicalOfSimpleGraph G).edgeCount +
        Fintype.card (Problem1016.physicalOfSimpleGraph G).traceNetwork.Component :=
    PhysicalGraph.cycleRank_euler_components (Problem1016.physicalOfSimpleGraph G)
  have he : (Problem1016.physicalOfSimpleGraph G).edgeCount = Nat.card G.edgeSet :=
    (@Nat.card_eq_fintype_card _ (Problem1016.simpleGraphEdgeFintype G)).symm
  have hgraph : (Problem1016.physicalOfSimpleGraph G).traceNetwork.graph = G :=
    (PhysicalGraph.traceNetwork_graph _).trans hPG
  have hc : Fintype.card (Problem1016.physicalOfSimpleGraph G).traceNetwork.Component =
      Nat.card G.ConnectedComponent := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.cast
      (congrArg (fun Q : SimpleGraph (Fin n) => Q.ConnectedComponent) hgraph))
  omega

/-- The cycles of `G` inject into the cycle words of its physical realization. -/
theorem numCycles_le_cycleCount {n : ℕ} (G : SimpleGraph (Fin n)) :
    numCycles G ≤ cycleCount (Problem1016.physicalOfSimpleGraph G) := by
  have h1 := numCycles_toSimpleGraph_le (Problem1016.physicalOfSimpleGraph G)
  rw [Problem1016.physicalOfSimpleGraph_toSimpleGraph G] at h1
  exact h1

/-- The elementary bound: a graph of cyclomatic number `r` has fewer than `2^r` cycles. -/
theorem numCycles_lt_two_pow {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (hr : r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent) :
    numCycles G < 2 ^ r := by
  have hE := physical_euler G
  have hrank : (Problem1016.physicalOfSimpleGraph G).cycleRank = r := by omega
  have h1 := numCycles_le_cycleCount G
  have h2 := (Problem1016.physicalOfSimpleGraph G).cycleWord_card_le
  rw [hrank] at h2
  have hpos : 0 < 2 ^ r := by positivity
  unfold cycleCount at h1
  omega

/-- The physical-graph bound implies the statement for Mathlib simple graphs. -/
theorem cycleCountStatement_of_bound (h : CycleCountBound) : CycleCountStatement := by
  obtain ⟨r₁, hr₁⟩ := h
  refine ⟨r₁, ?_⟩
  intro n G r hr hrr
  have hE := physical_euler G
  have hrank : (Problem1016.physicalOfSimpleGraph G).cycleRank = r := by omega
  have hb := hr₁ (Problem1016.physicalOfSimpleGraph G) (by rw [hrank]; exact hrr)
  rw [hrank] at hb
  have hcyc' : (numCycles G : ℝ) ≤
      (cycleCount (Problem1016.physicalOfSimpleGraph G) : ℝ) := by
    exact_mod_cast numCycles_le_cycleCount G
  exact hcyc'.trans hb

end Erdos1016.CycleCount

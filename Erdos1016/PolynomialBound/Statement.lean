import Erdos1016.PolynomialBound.CycleBound
import Erdos1016.CycleCount.FiniteTypes

set_option autoImplicit false

/-!
# The polynomial cycle-count bound in Mathlib's simple-graph language

The target: there is `κ > 0` such that every simple graph with large
cyclomatic number `r` has at most `(1/2 + r ^ (-κ)) * 2 ^ r` cycles. This file
states the target for graphs on `Fin n`, for graphs on every finite vertex
type, and for the maximum number of cycles. It derives all three from
`PolynomialMarkedBound`, the forest estimate for marked multigraphs.

`PolynomialMarkedBound` is not proved here. So the results of this file are
implications. They do not yet give the cycle-count bound itself.
-/

noncomputable section

namespace Erdos1016.PolynomialBound
open CycleCount

/-- There is `κ > 0` such that every simple graph on `Fin n` whose cyclomatic
number `r` is large has at most `(1/2 + r ^ (-κ)) * 2 ^ r` cycles. -/
def PolynomialCycleCountStatement : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ r₁ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ),
    r + n = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    (numCycles G : ℝ) ≤ (1 / 2 + (r : ℝ) ^ (-κ)) * 2 ^ r

/-- The physical-graph bound implies the statement for Mathlib simple graphs. -/
theorem polynomialCycleCountStatement_of_bound (h : PolynomialCycleCountBound) :
    PolynomialCycleCountStatement := by
  obtain ⟨κ, hκ, r₁, hr₁⟩ := h
  refine ⟨κ, hκ, r₁, ?_⟩
  intro n G r hr hrr
  have hE := physical_euler G
  have hrank : (Problem1016.physicalOfSimpleGraph G).cycleRank = r := by omega
  have hb := hr₁ (Problem1016.physicalOfSimpleGraph G) (by rw [hrank]; exact hrr)
  rw [hrank] at hb
  have hcyc' : (numCycles G : ℝ) ≤
      (cycleCount (Problem1016.physicalOfSimpleGraph G) : ℝ) := by
    exact_mod_cast numCycles_le_cycleCount G
  exact hcyc'.trans hb

/-- The polynomial cycle-count bound for simple graphs on any finite vertex type. -/
def GeneralPolynomialCycleCountStatement : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ r₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (r : ℕ),
    r + Fintype.card V = Nat.card G.edgeSet + Nat.card G.ConnectedComponent → r₁ ≤ r →
    (numCycles G : ℝ) ≤ (1 / 2 + (r : ℝ) ^ (-κ)) * 2 ^ r

/-- The statement on `Fin n` implies the statement on every finite type. -/
theorem generalPolynomialCycleCountStatement_of_statement
    (h : PolynomialCycleCountStatement) : GeneralPolynomialCycleCountStatement := by
  obtain ⟨κ, hκ, r₁, h₁⟩ := h
  refine ⟨κ, hκ, r₁, ?_⟩
  intro V _ G r hr hrr
  classical
  let φ : G ≃g G.map (Fintype.equivFin V).toEmbedding :=
    SimpleGraph.Iso.map (Fintype.equivFin V) G
  have hE : Nat.card (G.map (Fintype.equivFin V).toEmbedding).edgeSet =
      Nat.card G.edgeSet := Nat.card_congr φ.mapEdgeSet.symm
  have hC : Nat.card (G.map (Fintype.equivFin V).toEmbedding).ConnectedComponent =
      Nat.card G.ConnectedComponent := Nat.card_congr φ.connectedComponentEquiv.symm
  have hb := h₁ (Fintype.card V) (G.map (Fintype.equivFin V).toEmbedding) r
    (by rw [hE, hC]; exact hr) hrr
  have hle : (numCycles G : ℝ) ≤
      (numCycles (G.map (Fintype.equivFin V).toEmbedding) : ℝ) := by
    exact_mod_cast numCycles_le_of_iso φ
  exact hle.trans hb

/-- The polynomial bound for the maximum number of cycles at cyclomatic
number `r`. -/
def PolynomialMaxCyclesStatement : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ r₁ : ℕ, ∀ r, r₁ ≤ r →
    (maxCycles r : ℝ) ≤ (1 / 2 + (r : ℝ) ^ (-κ)) * 2 ^ r

/-- The statement on `Fin n` gives the bound for the maximum. -/
theorem polynomialMaxCyclesStatement_of_statement (h : PolynomialCycleCountStatement) :
    PolynomialMaxCyclesStatement := by
  obtain ⟨κ, hκ, r₁, h₁⟩ := h
  refine ⟨κ, hκ, max r₁ 3, fun r hr => ?_⟩
  obtain ⟨n, G, hG, hc⟩ := maxCycles_mem r (le_trans (le_max_right _ _) hr)
  rw [← hc]
  exact h₁ n G r hG (le_trans (le_max_left _ _) hr)

/-! ### The reductions, composed -/

/-- The forest estimate for marked multigraphs implies the polynomial
cycle-count bound for simple graphs on `Fin n`. -/
theorem polynomialCycleCountStatement_of_markedBound (h : PolynomialMarkedBound) :
    PolynomialCycleCountStatement :=
  polynomialCycleCountStatement_of_bound
    (polynomialCycleCountBound_of_forestEstimate
      (polynomialForestEstimate_of_marked_bound h))

/-- The same implication for simple graphs on every finite vertex type. -/
theorem generalPolynomialCycleCountStatement_of_markedBound (h : PolynomialMarkedBound) :
    GeneralPolynomialCycleCountStatement :=
  generalPolynomialCycleCountStatement_of_statement
    (polynomialCycleCountStatement_of_markedBound h)

/-- The same implication for the maximum number of cycles. -/
theorem polynomialMaxCyclesStatement_of_markedBound (h : PolynomialMarkedBound) :
    PolynomialMaxCyclesStatement :=
  polynomialMaxCyclesStatement_of_statement
    (polynomialCycleCountStatement_of_markedBound h)

end Erdos1016.PolynomialBound

import Erdos1016.Nonbacktracking.Spectrum.Operator

set_option autoImplicit false

/-!
# Matrix powers count the actual nonbacktracking dart runs

A run is defined recursively by its individually labelled intermediate dart
and the proof of the physical nonbacktracking transition. Repeated vertices
and repeated edges are permitted, as required for the trace argument.

This establishes the combinatorial meaning of the matrix trace. It does not
identify that trace with algebraic eigenvalue multiplicities, prove a
Perron lower bound, or compare closed runs with simple cycles.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance walkTraceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite one-point type when p holds, empty otherwise. -/
def Flag (p : Prop) := {u : Unit // p}

instance flagFintype (p : Prop) : Fintype (Flag p) := by
  unfold Flag
  infer_instance

theorem card_flag (p : Prop) : Fintype.card (Flag p) = if p then 1 else 0 := by
  by_cases hp : p
  · letI : Unique (Flag p) :=
      { default := ⟨(), hp⟩
        uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
    rw [if_pos hp]
    exact Fintype.card_unique
  · letI : IsEmpty (Flag p) := ⟨fun x => hp x.2⟩
    rw [if_neg hp]
    exact Fintype.card_eq_zero

/-- Exactly k transitions, with the first and last dart prescribed. -/
def Run (G : PhysicalGraph) : ℕ → Dart G → Dart G → Type
  | 0, d, e => Flag (d = e)
  | k + 1, d, e => Σ u : Dart G, Flag (Next G d u) × Run G k u e

instance runFinite (G : PhysicalGraph) (k : ℕ) (d e : Dart G) :
    Finite (Run G k d e) := by
  induction k generalizing d e with
  | zero =>
      change Finite (Flag (d = e))
      infer_instance
  | succ k ih =>
      change Finite (Σ u : Dart G, Flag (Next G d u) × Run G k u e)
      letI : ∀ u : Dart G, Finite (Run G k u e) := fun u => ih u e
      infer_instance

noncomputable instance runFintype (G : PhysicalGraph) (k : ℕ) (d e : Dart G) :
    Fintype (Run G k d e) := Fintype.ofFinite _

/-- An exact matrix identity over any semiring. Natural casts of counts are
used; no nonnegative-real or spectral interpretation is an extra premise. -/
theorem card_run_cast {K : Type*} [Semiring K] (G : PhysicalGraph)
    (k : ℕ) (d e : Dart G) :
    (Fintype.card (Run G k d e) : K) = ((matrix G : Matrix _ _ K) ^ k) d e := by
  induction k generalizing d e with
  | zero =>
      have hc : Fintype.card (Run G 0 d e) = Fintype.card (Flag (d = e)) :=
        Fintype.card_congr (Equiv.refl _)
      rw [hc, card_flag, pow_zero]
      by_cases h : d = e <;> simp [h, Matrix.one_apply]
  | succ k ih =>
      have hc : Fintype.card (Run G (k + 1) d e) =
          ∑ u : Dart G, Fintype.card (Flag (Next G d u)) *
            Fintype.card (Run G k u e) := by
        calc
          _ = Fintype.card (Σ u : Dart G, Flag (Next G d u) × Run G k u e) :=
            @Fintype.card_congr (Run G (k + 1) d e)
              (Σ u : Dart G, Flag (Next G d u) × Run G k u e)
              (runFintype G (k + 1) d e) inferInstance (Equiv.refl _)
          _ = _ := by rw [Fintype.card_sigma]; simp only [Fintype.card_prod]
      rw [hc]
      push_cast
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro u _
      rw [card_flag, ih]
      by_cases h : Next G d u <;> simp [matrix, h]

theorem card_run (G : PhysicalGraph) (k : ℕ) (d e : Dart G) :
    Fintype.card (Run G k d e) = ((matrix G : Matrix _ _ ℕ) ^ k) d e := by
  simpa using (card_run_cast (K := ℕ) G k d e)

/-- Rooted closed runs, with a distinguished initial physical dart. -/
def closedRunCount (G : PhysicalGraph) (k : ℕ) : ℕ :=
  ∑ d : Dart G, Fintype.card (Run G k d d)

theorem trace_pow_eq_closedRunCount {K : Type*} [Semiring K]
    (G : PhysicalGraph) (k : ℕ) :
    Matrix.trace ((matrix G : Matrix _ _ K) ^ k) = (closedRunCount G k : K) := by
  unfold Matrix.trace closedRunCount
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  exact (card_run_cast (K := K) G k d d).symm

/-- The real trace is a nonnegative integer, without spectral assumptions. -/
theorem real_trace_pow_nonneg (G : PhysicalGraph) (k : ℕ) :
    0 ≤ Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ k) := by
  rw [trace_pow_eq_closedRunCount]
  exact Nat.cast_nonneg _

/-- This identifies the real trace with the real part of the complex trace. -/
theorem complex_trace_pow_re (G : PhysicalGraph) (k : ℕ) :
    (Matrix.trace ((matrix G : Matrix _ _ ℂ) ^ k)).re =
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ k) := by
  rw [trace_pow_eq_closedRunCount, trace_pow_eq_closedRunCount]
  simp

end Erdos1016.Nonbacktracking

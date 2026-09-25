import Erdos1016.Nonbacktracking.Entropy.UniformBranching
import Erdos1016.Nonbacktracking.Entropy.Stationarity
import Erdos1016.Nonbacktracking.Trace.WalkTrace

set_option autoImplicit false

/-!
# Entropy growth for the actual physical nonbacktracking walks

The successor set and its double-stochastic normalization are constructed
from the labelled darts. `allRunCount` counts all actual runs, including
repeated vertices and edges. The resulting lower bound is the walk-count
part of source (5.2), and also supplies the entropy input to §7.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance entropyGrowthDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

def successors (d : Dart G) : Finset (Dart G) :=
  Finset.univ.filter (fun e => Next G d e)

@[simp] theorem mem_successors (d e : Dart G) : e ∈ successors G d ↔ Next G d e := by
  simp [successors]

/-- The reversal removes exactly one of the actual outgoing incidences. -/
theorem successors_card (d : Dart G) :
    (successors G d).card = G.degree (head G d) - 1 := by
  have hr := step_eq_sum_next (K := ℤ) G (fun _ => 1) d
  have hc : (∑ e : Dart G, if Next G d e then (1 : ℤ) else 0) =
      ((successors G d).card : ℤ) := by
    simpa [successors] using
      (Finset.sum_boole (fun e : Dart G => Next G d e) Finset.univ :
        (∑ e ∈ Finset.univ, if Next G d e then (1 : ℤ) else 0) = _)
  rw [hc] at hr
  simp only [step, outgoing_one] at hr
  have hle : 1 ≤ G.degree (head G d) := by omega
  exact_mod_cast (show ((successors G d).card : ℤ) =
      ((G.degree (head G d) - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub hle]
    simpa using hr.symm)

theorem successors_nonempty (hmin : ∀ v, 2 ≤ G.degree v) (d : Dart G) :
    (successors G d).Nonempty := by
  apply Finset.card_pos.mp
  rw [successors_card]
  have := hmin (head G d)
  omega

def branchingSystem (hmin : ∀ v, 2 ≤ G.degree v) : UniformBranching (Dart G) where
  successors := successors G
  successors_nonempty := successors_nonempty G hmin
  column_sum e := by
    have heq (d : Dart G) :
        (if e ∈ successors G d then 1 / ((successors G d).card : ℝ) else 0) =
        transition G d e := by
      have hle : 1 ≤ G.degree (head G d) := (by omega : 1 ≤ 2).trans (hmin _)
      rw [successors_card, Nat.cast_sub hle, Nat.cast_one]
      by_cases h : Next G d e <;> simp [transition, h]
    simp_rw [heq]
    exact transition_column_sum G hmin e

/-- Total count for k transitions: the two dart endpoints are unrestricted. -/
def allRunCount (k : ℕ) : ℕ := ∑ d : Dart G, ∑ e : Dart G, Fintype.card (Run G k d e)

/-- A literal finite type of all k-transition runs. -/
abbrev AllRuns (k : ℕ) := Σ d : Dart G, Σ e : Dart G, Run G k d e

theorem card_allRuns (k : ℕ) : Fintype.card (AllRuns G k) = allRunCount G k := by
  simp [AllRuns, allRunCount, Fintype.card_sigma]

def endpoints (k : ℕ) (p : AllRuns G k) : G.Vertex × G.Vertex :=
  (tail G p.1, head G p.2.1)

/-- No walks are omitted or identified when passing to the branching recursion. -/
theorem branching_walkCount (hmin : ∀ v, 2 ≤ G.degree v) (k : ℕ) (d : Dart G) :
    (branchingSystem G hmin).walkCount k d =
      ∑ e : Dart G, Fintype.card (Run G k d e) := by
  induction k generalizing d with
  | zero =>
      simp only [UniformBranching.walkCount_zero]
      simp_rw [card_run]
      simp [pow_zero, Matrix.one_apply]
  | succ k ih =>
      rw [UniformBranching.walkCount_succ]
      dsimp only [branchingSystem]
      change (∑ j ∈ successors G d,
        (branchingSystem G hmin).walkCount k j) = _
      simp_rw [ih]
      simp_rw [card_run]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [pow_succ', Matrix.mul_apply]
      simp [matrix, successors, Finset.sum_filter, ite_mul]

theorem branching_totalWalkCount (hmin : ∀ v, 2 ≤ G.degree v) (k : ℕ) :
    (branchingSystem G hmin).totalWalkCount k = allRunCount G k := by
  unfold UniformBranching.totalWalkCount allRunCount
  apply Finset.sum_congr rfl
  intro d _
  exact branching_walkCount G hmin k d

/-- Natural-log entropy equals log(2) times the source's bit entropy. -/
theorem branching_entropyRate (hmin : ∀ v, 2 ≤ G.degree v) :
    (branchingSystem G hmin).entropyRate = Real.log 2 * meanLogBranching G := by
  by_cases hm : G.edgeCount = 0
  · simp [UniformBranching.entropyRate, meanLogBranching, card_dart, hm]
  have hc (d : Dart G) :
      (((branchingSystem G hmin).degree d : ℕ) : ℝ) =
      (G.degree (head G d) : ℝ) - 1 := by
    change ((successors G d).card : ℝ) = _
    rw [successors_card, Nat.cast_sub (by have := hmin (head G d); omega),
      Nat.cast_one]
  unfold UniformBranching.entropyRate UniformBranching.logBranchSum meanLogBranching
  simp_rw [hc, Real.logb]
  rw [card_dart]
  push_cast
  rw [← Finset.sum_div]
  have htwo : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [htwo, hm]
  ring

/-- There is at least one labelled dart as soon as the graph has an edge. -/
theorem dart_nonempty_of_edgeCount_pos (hm : 0 < G.edgeCount) : Nonempty (Dart G) := by
  apply Fintype.card_pos_iff.mp
  rw [card_dart]
  omega

theorem edgeCount_pos_of_min_two (hmin : ∀ v, 2 ≤ G.degree v)
    (hn : 0 < G.vertexCount) : 0 < G.edgeCount := by
  haveI : Nonempty G.Vertex := by
    apply Fintype.card_pos_iff.mp
    simpa only [PhysicalGraph.Vertex, Fintype.card_fin] using hn
  let v : G.Vertex := Classical.choice (inferInstance : Nonempty G.Vertex)
  have hd := hmin v
  have hsum := physical_degree_sum G
  have hle : G.degree v ≤ ∑ u : G.Vertex, G.degree u :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  omega

/-- Source stationary entropy bound, on the exact finite physical walk set.
The graph may be disconnected and the transition chain may be periodic. -/
theorem allRunCount_entropy_lower
    (hmin : ∀ v, 2 ≤ G.degree v) (hm : 0 < G.edgeCount) (k : ℕ) :
    (2 * (G.edgeCount : ℝ)) *
      (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) ≤ allRunCount G k := by
  letI : Nonempty (Dart G) := dart_nonempty_of_edgeCount_pos G hm
  have h := (branchingSystem G hmin).totalWalkCount_lower k
  rw [branching_totalWalkCount, card_dart, branching_entropyRate] at h
  push_cast at h
  have hexp : Real.exp ((k : ℝ) * (Real.log 2 * meanLogBranching G)) =
      (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hexp] at h
  exact h







end Erdos1016.Nonbacktracking

import Erdos1016.Cycles.Counting.CollisionSplitCodes

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CyclicRunSplitCodeArithmetic

open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.CollisionSplitCodes
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Nonbacktracking

local notation "F₂" => ZMod 2

abbrev ValidSplitLength (ell s : ℕ) :=
  {a : ℕ // a ∈ (Finset.Icc 1 (ell - 1)).filter (fun a => s < ell - a)}

def splitLengthEquiv (ell s : ℕ) : SplitLength ell s ≃ ValidSplitLength ell s where
  toFun a := ⟨a.val.val, by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · exact a.property.1
      · have hlt : a.val.val < ell := a.val.isLt
        omega
    · exact a.property.2⟩
  invFun a := ⟨⟨a.val, by
      have hmem := a.property
      simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
      omega⟩,
    by
      have hmem := a.property
      simp only [Finset.mem_filter, Finset.mem_Icc] at hmem
      exact ⟨hmem.1.1, hmem.2⟩⟩
  left_inv := by intro a; apply Subtype.ext; rfl
  right_inv := by intro a; apply Subtype.ext; rfl

private def splitCodeWeight (G : PhysicalGraph) (ell s : ℕ)
    (a : SplitLength ell s) : ℝ :=
  (ell : ℝ) * (Fintype.card (ClosedEndpointRuns (G := G) (a.val.val - 1)) : ℝ) *
    (3 : ℝ) * (2 : ℝ) ^ (ell - a.val.val - s - 1)

private def splitCodeWeightAt (G : PhysicalGraph) (ell s a : ℕ) : ℝ :=
  (ell : ℝ) * (Fintype.card (ClosedEndpointRuns (G := G) (a - 1)) : ℝ) *
    (3 : ℝ) * (2 : ℝ) ^ (ell - a - s - 1)

private theorem splitCodeWeight_fiber_bound (G : PhysicalGraph)
    (ell s : ℕ) (hmax : ∀ v, G.degree v ≤ 3)
    (a : SplitLength ell s) :
    (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) ≤
      splitCodeWeight G ell s a := by
  have hnat := positionedSplitCodeFiber_card_le_of_max_degree G ell s hmax a
  have hcast :
      (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) ≤
        ((ell * Fintype.card (ClosedEndpointRuns (G := G) (a.val.val - 1)) *
          (3 * 2 ^ (ell - a.val.val - s - 1)) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) ≤
        ((ell * Fintype.card (ClosedEndpointRuns (G := G) (a.val.val - 1)) *
          (3 * 2 ^ (ell - a.val.val - s - 1)) : ℕ) : ℝ) := hcast
    _ = splitCodeWeight G ell s a := by
      simp only [splitCodeWeight, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring

private theorem splitCodeWeight_sum_le (G : PhysicalGraph) (ell s : ℕ) :
    (∑ a : SplitLength ell s, splitCodeWeight G ell s a) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
  classical
  let e := splitLengthEquiv ell s
  let interval := Finset.Icc 1 (ell - 1)
  let filtered := interval.filter (fun a => s < ell - a)
  have hsubtype :
      (∑ a : ValidSplitLength ell s, splitCodeWeightAt G ell s a.val) =
        ∑ a ∈ filtered, splitCodeWeightAt G ell s a := by
    symm
    apply Finset.sum_subtype filtered
    intro a
    rfl
  have hequiv :
      (∑ a : SplitLength ell s, splitCodeWeight G ell s a) =
        ∑ a : ValidSplitLength ell s, splitCodeWeightAt G ell s a.val := by
    apply Fintype.sum_equiv e
    intro a
    change (ell : ℝ) *
        (Fintype.card (ClosedEndpointRuns (G := G) (a.val.val - 1)) : ℝ) *
          (3 : ℝ) * (2 : ℝ) ^ (ell - a.val.val - s - 1) =
      (ell : ℝ) *
        (Fintype.card (ClosedEndpointRuns (G := G) ((e a).val - 1)) : ℝ) *
          (3 : ℝ) * (2 : ℝ) ^ (ell - (e a).val - s - 1)
    rfl
  rw [hequiv, hsubtype]
  let K := (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s)
  have hterm (a : ℕ) (ha : a ∈ interval) (hvalid : s < ell - a) :
      splitCodeWeightAt G ell s a = K * V G a := by
    have hle : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hsum : (ell - a - s - 1) + a = ell - s - 1 := by omega
    have hcancel : (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ a = 1 := by
      rw [← mul_pow]
      norm_num
    have hpow : (2 : ℝ) ^ (ell - a - s - 1) =
        (2 : ℝ) ^ (ell - s - 1) * (1 / 2 : ℝ) ^ a := by
      calc
        (2 : ℝ) ^ (ell - a - s - 1) =
            (2 : ℝ) ^ (ell - a - s - 1) * 1 := by ring
        _ = (2 : ℝ) ^ (ell - a - s - 1) *
            ((2 : ℝ) ^ a * (1 / 2 : ℝ) ^ a) := by rw [hcancel]
        _ = ((2 : ℝ) ^ (ell - a - s - 1) * (2 : ℝ) ^ a) *
            (1 / 2 : ℝ) ^ a := by ring
        _ = (2 : ℝ) ^ (ell - s - 1) * (1 / 2 : ℝ) ^ a := by
          rw [← pow_add, hsum]
    have hpowSucc : (2 : ℝ) ^ (ell - s) =
        (2 : ℝ) ^ (ell - s - 1) * 2 := by
      have hn : ell - s - 1 + 1 = ell - s := by omega
      calc
        (2 : ℝ) ^ (ell - s) = (2 : ℝ) ^ (ell - s - 1 + 1) :=
          congrArg (fun n : ℕ => (2 : ℝ) ^ n) hn.symm
        _ = (2 : ℝ) ^ (ell - s - 1) * (2 : ℝ) ^ 1 := by rw [pow_add]
        _ = (2 : ℝ) ^ (ell - s - 1) * 2 := by norm_num
    rw [splitCodeWeightAt, V, ordinaryClosedRunCount]
    dsimp [K]
    rw [hpow]
    rw [hpowSucc]
    ring
  calc
    (∑ a ∈ filtered, splitCodeWeightAt G ell s a) =
        ∑ a ∈ filtered, K * V G a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hterm a ((Finset.mem_filter.mp ha).1) ((Finset.mem_filter.mp ha).2)
    _ ≤ ∑ a ∈ interval, K * V G a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro a ha hnot
      have hV : 0 ≤ V G a := by
        unfold V ordinaryClosedRunCount
        positivity
      dsimp [K]
      positivity
    _ = (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
          change (∑ a ∈ interval, K * V G a) = K * (∑ a ∈ interval, V G a)
          rw [Finset.mul_sum]

/-- The positioned split code's finite-fiber estimate yields exactly the raw
collision cardinal bound used by the normalized collision slice. -/
theorem bad_runs_card_le_of_positioned_split_code_of_max_degree
    (G : PhysicalGraph) (ell s : ℕ)
    (hmax : ∀ v, G.degree v ≤ 3)
    (code : NonsimpleCyclicRuns G ell →
      Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a)
    (hcode : Function.Injective code) :
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
  let weight : SplitLength ell s → ℝ := splitCodeWeight G ell s
  have hfiber : ∀ a, (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) ≤
      weight a := by
    intro a
    exact splitCodeWeight_fiber_bound G ell s hmax a
  simpa [weight] using card_bad_runs_le_of_positioned_split_code
    G ell s code hcode weight hfiber _ (splitCodeWeight_sum_le G ell s)




/-- Compatibility form of the stronger maximum-degree-only bound. -/
theorem bad_runs_card_le_of_positioned_split_code
    (G : PhysicalGraph) (ell s : ℕ)
    (_hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (code : NonsimpleCyclicRuns G ell →
      Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a)
    (hcode : Function.Injective code) :
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a)  := by
  exact bad_runs_card_le_of_positioned_split_code_of_max_degree G ell s hmax code hcode

end Erdos1016.Proof.CyclicRunSplitCodeArithmetic

end

import Erdos1016.Nonbacktracking.Trace.SeamReduction

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.CyclicRunCollisionSlice

open Erdos1016.Nonbacktracking

local instance collisionSliceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Closed nonbacktracking runs with their cyclic seam also nonbacktracking.
The parameter `ell` is the number of physical darts/edges in the circuit. -/
def CyclicRuns (G : PhysicalGraph) (ell : ℕ) :=
  {p : ClosedEndpointRuns (G := G) (ell - 1) //
    Next G p.1.2.1 p.1.1}

def cyclicRunWalk (G : PhysicalGraph) (ell : ℕ)
    (p : CyclicRuns G ell) : G.toSimpleGraph.Walk
      (tail G p.1.1.1) (tail G p.1.1.1) :=
  (runWalk G (ell - 1) p.1.1.2.2).copy rfl p.1.2.symm







/-- Runs in the cyclically reduced closed-run slice whose vertex walk is
not an ordinary simple cycle. -/
def NonsimpleCyclicRuns (G : PhysicalGraph) (ell : ℕ) :=
  {p : CyclicRuns G ell // ¬ (cyclicRunWalk G ell p).IsCycle}

noncomputable instance cyclicRunsFintype (G : PhysicalGraph) (ell : ℕ) :
    Fintype (CyclicRuns G ell) := by
  classical
  letI : Fintype (AllRuns G (ell - 1)) := inferInstance
  letI : Fintype (ClosedEndpointRuns (G := G) (ell - 1)) :=
    Fintype.subtype
      (Finset.univ.filter fun x : AllRuns G (ell - 1) =>
        tail G x.1 = head G x.2.1)
      (by intro x; simp [ClosedEndpointRuns])
  exact Fintype.subtype
    (Finset.univ.filter fun x : ClosedEndpointRuns (G := G) (ell - 1) =>
      Next G x.1.2.1 x.1.1)
    (by intro x; simp [CyclicRuns])

noncomputable instance nonsimpleCyclicRunsFintype (G : PhysicalGraph) (ell : ℕ) :
    Fintype (NonsimpleCyclicRuns G ell) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun x : CyclicRuns G ell =>
      ¬ (cyclicRunWalk G ell x).IsCycle)
    (by intro x; simp [NonsimpleCyclicRuns])

/-- Ordinary rooted closed endpoint-run count at length `a`. -/
def ordinaryClosedRunCount (G : PhysicalGraph) (a : ℕ) : ℕ :=
  Fintype.card (ClosedEndpointRuns (G := G) (a - 1))

/-- The normalized ordinary closed-run mass `2^{-a} N_a`. -/
def V (G : PhysicalGraph) (a : ℕ) : ℝ :=
  (ordinaryClosedRunCount G a : ℝ) * (1 / 2 : ℝ) ^ a

/-- The normalized per-length mass of nonsimple cyclically reduced closed
runs. -/
def bad (G : PhysicalGraph) (ell : ℕ) : ℝ :=
  (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) * (1 / 2 : ℝ) ^ ell

/-- Exact arithmetic reduction for the collision slice. The premise is the
graph-specific split estimate: charge each bad cyclic run to a split
position, a shorter ordinary closed run, and a complementary suffix. Once
that estimate is proved by an injection, normalization gives the paper's
`(3/2) ell 2^{-s} sum_{a<ell} V_a` bound. -/
theorem bad_le_of_split_count
    (G : PhysicalGraph) (ell s : ℕ)
    (hsle : s ≤ ell)
    (hraw : (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a)) :
    bad G ell ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (1 / 2 : ℝ) ^ s *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
  unfold bad
  have hpow : (2 : ℝ) ^ (ell - s) * (1 / 2 : ℝ) ^ ell =
      (1 / 2 : ℝ) ^ s := by
    let k := ell - s
    have hidx : k + s = ell := by dsimp [k]; omega
    have hsub : ell - s = k := by dsimp [k]
    have hcancel : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (2 : ℝ) ^ (ell - s) * (1 / 2 : ℝ) ^ ell =
          (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (k + s) := by rw [hsub, hidx]
      _ = (2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ s) := by rw [pow_add]
      _ = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) *
          (1 / 2 : ℝ) ^ s := by ring
      _ = (1 / 2 : ℝ) ^ s := by rw [hcancel]; norm_num
  have hmul := mul_le_mul_of_nonneg_right hraw
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ ell)
  calc
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) * (1 / 2 : ℝ) ^ ell ≤
        ((3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
          (∑ a ∈ Finset.Icc 1 (ell - 1), V G a)) * (1 / 2 : ℝ) ^ ell := hmul
    _ = (3 / 2 : ℝ) * (ell : ℝ) * (1 / 2 : ℝ) ^ s *
          (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
      calc
        _ = ((3 / 2 : ℝ) * (ell : ℝ) *
            ((2 : ℝ) ^ (ell - s) * (1 / 2 : ℝ) ^ ell)) *
            (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by ring
        _ = _ := by rw [hpow]

end Erdos1016.Proof.CyclicRunCollisionSlice
end

import Erdos1016.Cycles.Counting.SplitCodeWeights
import Erdos1016.Nonbacktracking.Walks.PositionedCollisionInjection
import Erdos1016.Nonbacktracking.Trace.CollisionTraceMass

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.CollisionCharging

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.CollisionSplitCodes
open Erdos1016.Proof.CyclicRunSplitCodeArithmetic
open Erdos1016.Proof.CollisionTailReconstruction
open Erdos1016.Proof.PositionedCollisionInjection
open Erdos1016.Proof.CollisionTraceMass
open Erdos1016.Proof.HighGirthCollisionArithmetic
variable (G : PhysicalGraph)

/-- Choose the positioned suffix code supplied by the collision reconstruction.
The nonempty short-arc fact is retained as part of the code's subtype. -/
noncomputable def chosenPositionedCollisionCode (ell s D : ℕ)
    (hell : 0 < ell) (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (p : NonsimpleCyclicRuns G ell) :
    Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a := by
  let c := chosenCyclicCollisionCode G ell s D hell hg hshort hs p
  have hpos : 1 ≤ c.2.1.val := by
    rcases chosenCyclicCollisionCode_spec G ell s D hell hg hshort hs p with
      ⟨v, hroot, hoff, hlength, htail, hword⟩
    exact hlength
  exact toPositionedSplitCode G ell s c hpos

theorem chosenPositionedCollisionCode_injective (ell s D : ℕ)
    (hell : 0 < ell) (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    Function.Injective (chosenPositionedCollisionCode G ell s D hell hg hshort hs) := by
  intro p q h
  let cp := chosenCyclicCollisionCode G ell s D hell hg hshort hs p
  let cq := chosenCyclicCollisionCode G ell s D hell hg hshort hs q
  have hppos : 1 ≤ cp.2.1.val := by
    rcases chosenCyclicCollisionCode_spec G ell s D hell hg hshort hs p with
      ⟨v, hroot, hoff, hlength, htail, hword⟩
    exact hlength
  have hqpos : 1 ≤ cq.2.1.val := by
    rcases chosenCyclicCollisionCode_spec G ell s D hell hg hshort hs q with
      ⟨v, hroot, hoff, hlength, htail, hword⟩
    exact hlength
  have hsub : positionedSplitCodeMap G ell s ⟨cp, hppos⟩ =
      positionedSplitCodeMap G ell s ⟨cq, hqpos⟩ := by
    simpa [chosenPositionedCollisionCode, positionedSplitCodeMap, cp, cq] using h
  have hcSubtype : (⟨cp, hppos⟩ : {c : CyclicCollisionCode G ell s // 1 ≤ c.2.1.val}) =
      ⟨cq, hqpos⟩ := toPositionedSplitCode_injective G ell s hsub
  have hc : cp = cq := congrArg Subtype.val hcSubtype
  have hpq := chosenCyclicCollisionCode_injective G ell s D hell hg hshort hs hc
  exact hpq

/-- The collision reconstruction and the suffix fiber count together give the
raw nonsimple cyclic-run bound used by the trace-to-cycle conversion. -/
theorem nonsimpleCyclicRuns_card_le_split_bound_of_max_degree (ell s D : ℕ)
    (hell : 0 < ell)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a) := by
  exact bad_runs_card_le_of_positioned_split_code_of_max_degree G ell s hmax
    (chosenPositionedCollisionCode G ell s D hell hg hshort hs)
    (chosenPositionedCollisionCode_injective G ell s D hell hg hshort hs)

/-- Combining the injected split-code count with cyclic seam stripping gives
the normalized collision error against the actual trace mass. -/
theorem normalizedCollisionMass_le_trace_of_max_degree (L s D : ℕ)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    normalizedCollisionMass (bad G) L ≤
      (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s *
        nonbacktrackingTraceMass (G := G) L := by
  have hgS : ShortWalks.GirthGreater G.toSimpleGraph s := by
    intro v p hp
    have hD := hg v p hp
    omega
  apply collision_error_le_of_split_counts G L s hmax hgS
  intro ell hell hsle
  exact nonsimpleCyclicRuns_card_le_split_bound_of_max_degree G ell s D
    (by omega) hmax hg hshort hs


/-- Compatibility form of the stronger maximum-degree-only bound. -/
theorem nonsimpleCyclicRuns_card_le_split_bound (ell s D : ℕ)
    (hell : 0 < ell)
    (_hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
        (∑ a ∈ Finset.Icc 1 (ell - 1), V G a)  := by
  exact nonsimpleCyclicRuns_card_le_split_bound_of_max_degree G ell s D hell hmax hg hshort hs

/-- Compatibility form of the stronger maximum-degree-only bound. -/
theorem normalizedCollisionMass_le_trace (L s D : ℕ)
    (_hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    normalizedCollisionMass (bad G) L ≤
      (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s *
        nonbacktrackingTraceMass (G := G) L  := by
  exact normalizedCollisionMass_le_trace_of_max_degree G L s D hmax hg hshort hs

end Erdos1016.Proof.CollisionCharging
end

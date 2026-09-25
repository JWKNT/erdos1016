import Erdos1016.Nonbacktracking.Walks.CollisionTailReconstruction

set_option autoImplicit false

universe u v

noncomputable section
namespace Erdos1016.Proof.PositionedCollisionInjection

open Erdos1016
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.CollisionSplitCodes
open Erdos1016.Proof.CollisionTailReconstruction

private theorem cast_sigma_snd {α : Type u} (F : ℕ → α → Type v)
    {n m : ℕ} (h : n = m) (a : α) (x : F n a) :
    cast (congrArg (fun k => Σ y : α, F k y) h) ⟨a, x⟩ =
      ⟨a, cast (congrArg (fun k => F k a) h) x⟩ := by
  cases h
  rfl

private def reconstructedLongLength (ell s : ℕ) (a : SplitLength ell s) :
    {b : Fin ell // a.val.val + b.val = ell ∧ s < b.val} := by
  have hapos : 0 < a.val.val := by omega
  refine ⟨⟨ell - a.val.val, ?_⟩, ?_⟩
  · omega
  · constructor
    · simp only [Fin.val_mk]
      omega
    · exact a.2.2

def fromPositionedSplitCode (G : PhysicalGraph) (ell s : ℕ)
    (z : Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a) :
    CyclicCollisionCode G ell s := by
  let b := reconstructedLongLength ell s z.1
  exact ⟨z.2.1, z.1.val,
    ⟨b.1, b.2⟩,
    z.2.2.1, z.2.2.2⟩

theorem from_toPositionedSplitCode
    (G : PhysicalGraph) (ell s : ℕ)
    (c : CyclicCollisionCode G ell s)
    (hshort : 1 ≤ c.2.1.val) :
    fromPositionedSplitCode G ell s (toPositionedSplitCode G ell s c hshort) = c := by
  rcases c with ⟨offset, shortLength, longLength, shortArc, suffix⟩
  change 1 ≤ shortLength.val at hshort
  have hsum := longLength.2.1
  have htail := longLength.2.2
  let a : SplitLength ell s := ⟨shortLength, by constructor <;> omega⟩
  have hlen : ell - shortLength.val - s - 1 = longLength.val - s - 1 := by omega
  unfold fromPositionedSplitCode toPositionedSplitCode
  dsimp
  simp only [Sigma.mk.injEq]
  constructor
  · trivial
  ·
    let b' := reconstructedLongLength ell s a
    have hbval : b'.1.val = longLength.1.val := by
      simp [b', reconstructedLongLength, a]
      omega
    have hLong : b' = longLength := by
      apply Subtype.ext
      apply Fin.ext
      exact hbval
    let F : ℕ → ClosedEndpointRuns (G := G) (shortLength.val - 1) → Type 0 :=
      fun n u => StartingRuns G n (tail G u.1.1)
    have htype := congrArg (fun n => Σ u : ClosedEndpointRuns (G := G)
      (shortLength.val - 1), StartingRuns G n (tail G u.1.1)) hlen.symm
    have htransport : cast htype (⟨shortArc, suffix⟩ : Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1), F (longLength.val - s - 1) u) =
        (⟨shortArc, hlen.symm ▸ suffix⟩ : Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1), F (ell - shortLength.val - s - 1) u) := by
      simpa [F, eqRec_eq_cast] using cast_sigma_snd (F := F) hlen.symm shortArc suffix
    have hrest : HEq
        (⟨shortArc, hlen.symm ▸ suffix⟩ : Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1), F (ell - shortLength.val - s - 1) u)
        (⟨shortArc, suffix⟩ : Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1), F (longLength.val - s - 1) u) := by
      exact (heq_of_eq htransport).symm.trans (cast_heq htype (⟨shortArc, suffix⟩ : Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1), F (longLength.val - s - 1) u))
    have hinner :
        (⟨b', (⟨shortArc, hlen.symm ▸ suffix⟩ :
          Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1),
            StartingRuns G (ell - shortLength.val - s - 1) (tail G u.1.1))⟩ :
          Σ b : {b : Fin ell // shortLength.val + b.val = ell ∧ s < b.val},
            Σ u : ClosedEndpointRuns (G := G) (shortLength.val - 1),
              StartingRuns G (b.val.val - s - 1) (tail G u.1.1)) =
        ⟨longLength, ⟨shortArc, suffix⟩⟩ := Sigma.ext hLong hrest
    -- The nested sigma equality supplied by `hinner` is precisely the
    -- heterogeneous tail equality in the outer code.
    exact heq_of_eq (Sigma.ext rfl (heq_of_eq hinner))

def positionedSplitCodeMap (G : PhysicalGraph) (ell s : ℕ) :
    {c : CyclicCollisionCode G ell s // 1 ≤ c.2.1.val} →
      Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a :=
  fun c => toPositionedSplitCode G ell s c.1 c.2

theorem toPositionedSplitCode_injective (G : PhysicalGraph) (ell s : ℕ) :
    Function.Injective (positionedSplitCodeMap G ell s) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (fromPositionedSplitCode G ell s) hxy
  simpa [positionedSplitCodeMap, from_toPositionedSplitCode] using h

end Erdos1016.Proof.PositionedCollisionInjection
end

import Erdos1016.Nonbacktracking.Girth.CollisionSlices

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.RootedCyclicRunInjection

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice

variable {G : PhysicalGraph}

/-- A closed dart run of length `ell`. -/
abbrev ClosedDartRun (ell : ℕ) := Σ d : Dart G, Run G ell d d

/-- Peel the final transition from a run, retaining the preceding run. -/
noncomputable def run_peel_last : (k : ℕ) → {d f : Dart G} →
    Run G (k + 1) d f → Σ e : Dart G, Σ _pre : Run G k d e, Flag (Next G e f)
  | 0, d, f, r => by
      rcases r with ⟨u, hu, r0⟩
      have huf : u = f := r0.2
      subst f
      exact ⟨d, ⟨⟨(), rfl⟩, hu⟩⟩
  | k + 1, d, f, r => by
      rcases r with ⟨u, hu, rest⟩
      obtain ⟨e, pre, last⟩ := run_peel_last k rest
      exact ⟨e, ⟨⟨u, hu, pre⟩, last⟩⟩

/-- Reattaching the peeled final transition reconstructs the original run. -/
theorem run_peel_last_reconstruct : ∀ (k : ℕ) {d f : Dart G}
    (r : Run G (k + 1) d f),
    run_append_step k (run_peel_last (G := G) k r).2.1
      ((run_peel_last (G := G) k r).2.2).2 = r := by
  intro k
  induction k with
  | zero =>
      intro d f r
      rcases r with ⟨u, hu, r0⟩
      have huf : u = f := r0.2
      subst f
      simp only [run_peel_last, run_append_step]
      congr 2
  | succ k ih =>
      intro d f r
      rcases r with ⟨u, hu, rest⟩
      simp only [run_peel_last]
      have hs : run_append_step (k + 1)
          ⟨u, hu, (run_peel_last (G := G) k rest).2.1⟩
          ((run_peel_last (G := G) k rest).2.2).2 =
        ⟨u, hu, run_append_step k (run_peel_last (G := G) k rest).2.1
          ((run_peel_last (G := G) k rest).2.2).2⟩ := rfl
      rw [hs, ih rest]

/-- Every closed dart run determines a closed endpoint run plus its cyclic
seam transition. -/
noncomputable def closedDartRunToCyclic (ell : ℕ) (hell : 0 < ell) :
    ClosedDartRun (G := G) ell → CyclicRuns G ell := by
  intro x
  rcases x with ⟨d, r⟩
  have hidx : (ell - 1) + 1 = ell := Nat.sub_add_cancel (by omega)
  obtain ⟨e, pre, hlast⟩ := run_peel_last (ell - 1) (hidx ▸ r)
  have hclose : tail G d = head G e := hlast.2.1.symm
  let closed : ClosedEndpointRuns (G := G) (ell - 1) :=
    ⟨⟨d, e, pre⟩, hclose⟩
  exact ⟨closed, hlast.2⟩

/-- Reassemble the linear run represented by a cyclic run. -/
noncomputable def cyclicToClosedDartRun (ell : ℕ) (hell : 0 < ell) :
    CyclicRuns G ell → ClosedDartRun (G := G) ell := by
  intro p
  let core := p.1.1
  let d := core.1
  let e := core.2.1
  let pre := core.2.2
  have hidx : (ell - 1) + 1 = ell := Nat.sub_add_cancel (by omega)
  exact ⟨d, hidx ▸ run_append_step (ell - 1) pre p.2⟩

theorem cyclicToClosedDartRun_leftInverse (ell : ℕ) (hell : 0 < ell) :
    Function.LeftInverse (cyclicToClosedDartRun (G := G) ell hell)
      (closedDartRunToCyclic (G := G) ell hell) := by
  intro x
  rcases x with ⟨d, r⟩
  dsimp [cyclicToClosedDartRun, closedDartRunToCyclic]
  have hidx : (ell - 1) + 1 = ell := Nat.sub_add_cancel (by omega)
  have hrebuild := run_peel_last_reconstruct (G := G) (ell - 1) (hidx ▸ r)
  -- Both conversions use the exact prefix and seam returned by `run_peel_last`.
  rw [hrebuild]
  have hcancel {n m : ℕ} (h : n = m) (F : ℕ → Type _)
      (z : F m) : h ▸ (h.symm ▸ z) = z := by
    cases h
    rfl
  apply congrArg (fun z : Run G ell d d => (⟨d, z⟩ : ClosedDartRun (G := G) ell))
  exact hcancel hidx (fun n => Run G n d d) r

theorem closedDartRunToCyclic_injective (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (closedDartRunToCyclic (G := G) ell hell) :=
  (cyclicToClosedDartRun_leftInverse (G := G) ell hell).injective





end Erdos1016.Proof.RootedCyclicRunInjection
end

import Erdos1016.Nonbacktracking.Walks.PrefixCounts

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.CollisionSliceInstantiation

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix

variable (G : PhysicalGraph)

private theorem runDarts_head {k : ℕ} {d e : Dart G}
    (r : Run G k d e) :
    runDarts G k r = d :: (runDarts G k r).tail := by
  cases k <;> simp [runDarts]

private theorem runDarts_cast {m n : ℕ} (hmn : m = n) {d e : Dart G}
    (r : Run G m d e) : runDarts G n (hmn ▸ r) = runDarts G m r := by
  cases hmn
  rfl

private theorem run_transport_eq {m n : ℕ} (hmn : n = m) {d e : Dart G}
    (r : Run G m d e) :
    Eq.mpr (congrArg (fun t => Run G t d e) hmn) r = hmn.symm ▸ r := by
  cases hmn
  rfl

/-- The existing short-walk geometry theorem gives the exact suffix uniqueness
needed after a fixed boundary dart: its continuation is determined by its
terminal vertex when twice its transition length is below the girth. -/
theorem continuation_eq_of_boundary_and_endpoint (s D : ℕ)
    (hs : 0 < s)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D)
    {d e₁ e₂ : Dart G}
    (r₁ : Run G s d e₁) (r₂ : Run G s d e₂)
    (hend : head G e₁ = head G e₂) :
    ∃ he : e₁ = e₂, he ▸ r₁ = r₂ := by
  apply eq_of_dropFirstRun_eq G hs r₁ r₂
  exact dropFirstRun_eq_of_same_boundary_and_endpoint G s D hs hg hshort r₁ r₂ hend

/-- Splitting a run retains the shared boundary dart, so its dart list is the
prefix list followed by the suffix list with that one shared dart removed. -/
theorem runDarts_splitRun : ∀ {j k : ℕ} (hjk : j ≤ k) {d e : Dart G}
    (r : Run G k d e),
    let z := splitRun G hjk r
    runDarts G k r = runDarts G j z.2.1 ++ (runDarts G (k - j) z.2.2).tail := by
  intro j
  induction j with
  | zero =>
      intro k hjk d e r
      rw [splitRun.eq_1 G k d e r hjk]
      simp only [Nat.sub_zero, runDarts]
      rw [runDarts_head G r]
      simp
  | succ j ih =>
      intro k hjk d e r
      cases k with
      | zero => omega
      | succ k =>
          rcases r with ⟨u, hu, rest⟩
          rw [splitRun.eq_3 G d e j k hjk ⟨u, hu, rest⟩]
          let pieces := splitRun G (Nat.le_of_succ_le_succ hjk) rest
          have hp := ih (k := k) (Nat.le_of_succ_le_succ hjk) rest
          have hsub : k + 1 - (j + 1) = k - j :=
            Nat.succ_sub_succ_eq_sub k j
          simp only [runDarts]
          apply congrArg (fun xs => d :: xs)
          have hRun : Run G (k + 1 - (j + 1)) pieces.1 e =
              Run G (k - j) pieces.1 e :=
            congrArg (fun q => Run G q pieces.1 e) hsub
          have hproof := run_transport_eq G hsub pieces.2.2
          rw [hproof]
          have hcast := runDarts_cast G hsub.symm pieces.2.2
          convert hp using 1
          exact congrArg (fun xs => runDarts G j pieces.2.1 ++ xs.tail) hcast

end Erdos1016.Proof.CollisionSliceInstantiation
end

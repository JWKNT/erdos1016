import Erdos1016.Nonbacktracking.Trace.ClosedRunTail

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace Erdos1016.Nonbacktracking

open scoped BigOperators
variable {G : PhysicalGraph}

/-- Rooted closed dart runs, the objects counted by the nonbacktracking
matrix trace. -/
abbrev ClosedDartRuns (ell : ℕ) := Σ d : Dart G, Run G ell d d

/-- Close a reduced closed endpoint run by its unique legal seam transition.
The reduced-seam condition is exactly what makes the appended first dart a
legal nonbacktracking transition. -/
def reducedEndpointRunToClosedDartRun (ell : ℕ) (hell : 0 < ell) :
    ReducedClosedEndpointRuns (G := G) (ell - 1) → ClosedDartRuns (G := G) ell :=
  fun p => by
    let d := p.1.1.1
    let e := p.1.1.2.1
    let r := p.1.1.2.2
    have hseam : Next G e d := by
      refine ⟨p.1.2.symm, ?_⟩
      intro h
      apply p.2
      have hr := congrArg (reverse G) h
      simpa using hr.symm
    let r' := run_append_step (ell - 1) r hseam
    have hlen : (ell - 1) + 1 = ell := Nat.sub_add_cancel (by omega)
    exact ⟨d, hlen ▸ r'⟩



theorem reducedEndpointRunToClosedDartRun_injective (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (reducedEndpointRunToClosedDartRun (G := G) ell hell) := by
  rintro ⟨⟨⟨d, e, r⟩, hclosed⟩, hred⟩ ⟨⟨⟨d', e', r'⟩, hclosed'⟩, hred'⟩ hpq
  let hseam : Next G e d := ⟨hclosed.symm, by
    intro h
    apply hred
    have hr := congrArg (reverse G) h
    simpa using hr.symm⟩
  let hseam' : Next G e' d' := ⟨hclosed'.symm, by
    intro h
    apply hred'
    have hr := congrArg (reverse G) h
    simpa using hr.symm⟩
  have hparts := (Sigma.ext_iff).mp hpq
  have hd : d = d' := by simpa [reducedEndpointRunToClosedDartRun] using hparts.1
  subst d'
  have hrun : (Nat.sub_add_cancel (by omega : 1 ≤ ell) ▸
      run_append_step (ell - 1) r hseam) =
      (Nat.sub_add_cancel (by omega : 1 ≤ ell) ▸
        run_append_step (ell - 1) r' hseam') := by
    exact eq_of_heq (by simpa [reducedEndpointRunToClosedDartRun] using hparts.2)
  have hlist := congrArg (runDarts G ell) hrun
  have hlistLeft : runDarts G ell
      (Nat.sub_add_cancel (by omega : 1 ≤ ell) ▸
        run_append_step (ell - 1) r hseam) = runDarts G (ell - 1) (⟨d, e, r⟩ : AllRuns G (ell - 1)).2.2 ++ [d] := by
    rw [runDarts_cast (Nat.sub_add_cancel (by omega : 1 ≤ ell))]
    simpa [hseam] using run_append_step_darts (ell - 1) r hseam
  have hlistRight : runDarts G ell
      (Nat.sub_add_cancel (by omega : 1 ≤ ell) ▸
        run_append_step (ell - 1) r' hseam') = runDarts G (ell - 1) (⟨d, e', r'⟩ : AllRuns G (ell - 1)).2.2 ++ [d] := by
    rw [runDarts_cast (Nat.sub_add_cancel (by omega : 1 ≤ ell))]
    simpa [hseam'] using run_append_step_darts (ell - 1) r' hseam'
  rw [hlistLeft, hlistRight] at hlist
  have hprefix : runDarts G (ell - 1) (⟨d, e, r⟩ : AllRuns G (ell - 1)).2.2 =
      runDarts G (ell - 1) (⟨d, e', r'⟩ : AllRuns G (ell - 1)).2.2 :=
    List.append_cancel_right hlist
  have hraw : (⟨d, e, r⟩ : AllRuns G (ell - 1)) = ⟨d, e', r'⟩ :=
    allRuns_darts_injective (G := G) (ell - 1) hprefix
  apply Subtype.ext
  apply Subtype.ext
  exact hraw

theorem reducedClosedEndpointRuns_card_le_closedRunCount (ell : ℕ) (hell : 0 < ell) :
    Fintype.card (ReducedClosedEndpointRuns (G := G) (ell - 1)) ≤
      closedRunCount G ell := by
  calc
    Fintype.card (ReducedClosedEndpointRuns (G := G) (ell - 1)) ≤
        Fintype.card (ClosedDartRuns (G := G) ell) :=
      Fintype.card_le_of_injective
        (reducedEndpointRunToClosedDartRun (G := G) ell hell)
        (reducedEndpointRunToClosedDartRun_injective (G := G) ell hell)
    _ = closedRunCount G ell := by
      simp [ClosedDartRuns, closedRunCount, Fintype.card_sigma]

/-- Trace mass using the paper's per-length normalization `tr(B^ell)/(2 ell 2^ell)`. -/
def nonbacktrackingTraceMass (L : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 L,
    (closedRunCount G ell : ℝ) / ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)

/-- Cyclically reduced endpoint-run mass is dominated by the normalized
nonbacktracking trace mass, with the paper's factor `2L`. -/
theorem reducedClosedRunMass_prefix_le_two_L_traceMass (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L, reducedClosedRunMass (G := G) ell) ≤
      2 * (L : ℝ) * nonbacktrackingTraceMass (G := G) L := by
  have hterm (ell : ℕ) (hell : ell ∈ Finset.Icc 1 L) :
      reducedClosedRunMass (G := G) ell ≤
        2 * (L : ℝ) *
          ((closedRunCount G ell : ℝ) / ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) := by
    have hellpos : 0 < ell := (Finset.mem_Icc.mp hell).1
    have hcard := reducedClosedEndpointRuns_card_le_closedRunCount
      (G := G) ell hellpos
    have hcast : (Fintype.card (ReducedClosedEndpointRuns (G := G) (ell - 1)) : ℝ) ≤
        (closedRunCount G ell : ℝ) := by exact_mod_cast hcard
    have hdenpos : (0 : ℝ) < (2 : ℝ) ^ ell := by positivity
    have hnorm :
        reducedClosedRunMass (G := G) ell ≤
          (closedRunCount G ell : ℝ) / (2 : ℝ) ^ ell := by
      unfold reducedClosedRunMass
      exact div_le_div_of_nonneg_right hcast (by positivity)
    have hfactor : (2 : ℝ) * (ell : ℝ) ≤ 2 * (L : ℝ) := by
      have := (Finset.mem_Icc.mp hell).2
      exact_mod_cast (Nat.mul_le_mul_left 2 this)
    have htracepos : 0 ≤
        (closedRunCount G ell : ℝ) / ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) := by
      positivity
    have hscale :
        (closedRunCount G ell : ℝ) / (2 : ℝ) ^ ell ≤
          2 * (L : ℝ) *
            ((closedRunCount G ell : ℝ) /
              ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) := by
      have heq :
          2 * (ell : ℝ) *
              ((closedRunCount G ell : ℝ) /
                ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) =
            (closedRunCount G ell : ℝ) / (2 : ℝ) ^ ell := by
        field_simp [ne_of_gt hellpos]
        ring
      rw [← heq]
      exact mul_le_mul_of_nonneg_right hfactor htracepos
    exact hnorm.trans hscale
  calc
    _ ≤ ∑ ell ∈ Finset.Icc 1 L,
        2 * (L : ℝ) *
          ((closedRunCount G ell : ℝ) /
            ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) := by
          apply Finset.sum_le_sum
          intro ell hell
          exact hterm ell hell
    _ = 2 * (L : ℝ) * nonbacktrackingTraceMass (G := G) L := by
          unfold nonbacktrackingTraceMass
          rw [Finset.mul_sum]

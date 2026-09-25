import Erdos1016.Probability.Cylinders.GraphicalThreshold

set_option autoImplicit false

/-!
# A generic threshold obstruction for a family of cylinders

This module packages the one conclusion that can be drawn from the graphical
second-moment argument without additional graph-specific estimates.  If a
large-count event is contained in a graph event whose probability is known to
be small, then its first and pair-cylinder bounds force the displayed
numerical inequality.  In applications, the containment and partner-count
estimates are the graph-specific work.
-/

noncomputable section

namespace Erdos1016.Proof.BadVertexCylinderCount

open Erdos1016.Proof.GraphicalThreshold

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- Probability is monotone under event inclusion on a finite uniform space. -/
theorem eventProbability_mono (P Q : Ω → Prop)
    (hPQ : ∀ x, P x → Q x) :
    eventProbability P ≤ eventProbability Q := by
  classical
  unfold eventProbability Erdos1016.Proof.FinitePaleyZygmund.probability
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter P) ⊆ (Finset.univ.filter Q) from by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hPQ x hx)

/-- If the event that at least `a` cylinders hold is contained in an event `U`,
the graphical cylinder hypotheses and an upper bound on `P(U)` force the
threshold lower bound to be at most that upper bound.  All event-level
dependencies are explicit: `E` are the cylinder events, `exceptional` is the
pair relation, and `U` is the event used to control their large-count tail. -/
theorem cylinder_threshold_le_of_contained_event
    (E : ι → Ω → Prop) (exceptional : ι → ι → Prop)
    [DecidableRel exceptional] (U : Ω → Prop)
    (K a μ δ : ℝ)
    (ha : 0 ≤ a) (hμ : a < μ) (hK : 0 ≤ K)
    (hmean : μ = ∑ i, eventProbability (E i))
    (hdiag : ∀ i,
      eventProbability (fun x => E i x ∧ E i x) ≤ eventProbability (E i))
    (hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤
        2 * eventProbability (E i) * eventProbability (E j))
    (hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x => E i x ∧ E j x) ≤ eventProbability (E i))
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ K)
    (hcontain : ∀ x, a ≤ eventCount E x → U x)
    (hU : eventProbability U ≤ δ) :
    (μ - a) ^ 2 / (2 * μ ^ 2 + (1 + K) * μ) ≤ δ := by
  have hthreshold := graphical_cylinder_threshold E exceptional K a μ
    ha hμ hK hmean hdiag hordinary hexceptional hpartners
  exact hthreshold.trans ((eventProbability_mono
    (fun x => a ≤ eventCount E x) U hcontain).trans hU)



end Erdos1016.Proof.BadVertexCylinderCount

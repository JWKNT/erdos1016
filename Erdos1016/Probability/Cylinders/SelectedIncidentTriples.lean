import Erdos1016.Probability.Cylinders.TriplePairBounds
import Erdos1016.Probability.Cylinders.ThresholdObstruction
import Erdos1016.Cleanup.Degree.LinearBadVertexBound
import Erdos1016.Cleanup.Degree.TripleForestObstruction

set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Selected triples as cylinders in the bad-vertex argument

This module connects feasible all-one incident triples to the generic
cylinder threshold estimate. The graph-specific inputs remain explicit:
pairwise common constraint rank, exceptional neighbours, and the implication
that any selected triple spoils the forest event.
-/

noncomputable section

namespace Erdos1016.Proof.BadVertexSelectedTriples

open Erdos1016
open Erdos1016.Proof.ActiveTripleBridge
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.AffineCylinders
open Erdos1016.Proof.AffineCylinderPairs

local notation "F₂" => ZMod 2

private theorem finiteProbability_eq_affineProbability
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] [Fintype W] [Fintype F₂]
    (P : Module.Dual F₂ W → Prop) :
    Erdos1016.Proof.FinitePaleyZygmund.probability P =
      Erdos1016.Proof.AffineCylinders.probability P := by
  classical
  unfold Erdos1016.Proof.FinitePaleyZygmund.probability
    Erdos1016.Proof.AffineCylinders.probability
  have hnum : Nat.card {x : Module.Dual F₂ W // P x} =
      (Finset.univ.filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hden : Nat.card (Module.Dual F₂ W) = Fintype.card (Module.Dual F₂ W) :=
    Nat.card_eq_fintype_card
  rw [hnum, hden]

private theorem affineProbability_congr
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] [Fintype W] [Fintype F₂]
    (P Q : Module.Dual F₂ W → Prop) (h : ∀ x, P x ↔ Q x) :
    Erdos1016.Proof.AffineCylinders.probability P =
      Erdos1016.Proof.AffineCylinders.probability Q := by
  classical
  unfold Erdos1016.Proof.AffineCylinders.probability
  have hcard : Nat.card {x : Module.Dual F₂ W // P x} =
      Nat.card {x : Module.Dual F₂ W // Q x} :=
    Nat.card_congr (Equiv.subtypeEquiv
      (Equiv.refl (Module.Dual F₂ W)) h)
  rw [hcard]

/-- Probability of one selected-triple event as a cylinder on the double
dual of the cycle space. -/
theorem allSelectedTriple_probability_eq_affineCylinder
    (G : PhysicalGraph) (e : Fin 3 → G.Edge)
    (x₀ : G.CycleSpace) (hx₀ : allSelectedTriple G e x₀) :
    eventProbability (allSelectedTriple G e) =
      Erdos1016.Proof.AffineCylinders.probability
        (Cylinder (tripleConstraintSpace G e)
          (tripleCylinderAssignment G e x₀)) := by
  classical
  let ev : G.CycleSpace ≃
      Module.Dual F₂ (Module.Dual F₂ G.CycleSpace) :=
    (Module.evalEquiv F₂ G.CycleSpace).toEquiv
  let L := tripleConstraintSpace G e
  let a := tripleCylinderAssignment G e x₀
  have hevent (y : Module.Dual F₂ (Module.Dual F₂ G.CycleSpace)) :
      allSelectedTriple G e (ev.symm y) ↔ Cylinder L a y := by
    have h := allSelectedTriple_iff_affineCylinder G e x₀ hx₀ (ev.symm y)
    simpa [ev, L, a] using h
  calc
    eventProbability (allSelectedTriple G e) =
        Erdos1016.Proof.FinitePaleyZygmund.probability
          (allSelectedTriple G e) := rfl
    _ = Erdos1016.Proof.FinitePaleyZygmund.probability
          (fun y => allSelectedTriple G e (ev.symm y)) :=
      Erdos1016.Proof.SelectedTripleCylinder.uniformEventProbability_congr_equiv
        ev (allSelectedTriple G e)
    _ = Erdos1016.Proof.AffineCylinders.probability
          (fun y => allSelectedTriple G e (ev.symm y)) :=
      finiteProbability_eq_affineProbability _
    _ = Erdos1016.Proof.AffineCylinders.probability (Cylinder L a) :=
      affineProbability_congr _ _ hevent

/-- Joint probability of two selected-triple events as a pair of affine
cylinders on the double dual. -/
theorem pairSelectedTriple_probability_eq_affineCylinders
    (G : PhysicalGraph) (e₁ e₂ : Fin 3 → G.Edge)
    (x₁ x₂ : G.CycleSpace)
    (hx₁ : allSelectedTriple G e₁ x₁)
    (hx₂ : allSelectedTriple G e₂ x₂) :
    eventProbability (fun x => allSelectedTriple G e₁ x ∧
        allSelectedTriple G e₂ x) =
      Erdos1016.Proof.AffineCylinders.probability
        (fun y =>
          Cylinder (tripleConstraintSpace G e₁)
            (tripleCylinderAssignment G e₁ x₁) y ∧
          Cylinder (tripleConstraintSpace G e₂)
            (tripleCylinderAssignment G e₂ x₂) y) := by
  classical
  let ev : G.CycleSpace ≃
      Module.Dual F₂ (Module.Dual F₂ G.CycleSpace) :=
    (Module.evalEquiv F₂ G.CycleSpace).toEquiv
  have hevent (y : Module.Dual F₂ (Module.Dual F₂ G.CycleSpace)) :
      (allSelectedTriple G e₁ (ev.symm y) ∧
        allSelectedTriple G e₂ (ev.symm y)) ↔
      (Cylinder (tripleConstraintSpace G e₁)
          (tripleCylinderAssignment G e₁ x₁) y ∧
        Cylinder (tripleConstraintSpace G e₂)
          (tripleCylinderAssignment G e₂ x₂) y) := by
    constructor
    · rintro ⟨h₁, h₂⟩
      have heval : Module.evalEquiv F₂ G.CycleSpace (ev.symm y) = y :=
        ev.apply_symm_apply y
      have h₁' := (allSelectedTriple_iff_affineCylinder G e₁ x₁ hx₁
        (ev.symm y)).mp h₁
      have h₂' := (allSelectedTriple_iff_affineCylinder G e₂ x₂ hx₂
        (ev.symm y)).mp h₂
      rw [heval] at h₁' h₂'
      exact ⟨h₁', h₂'⟩
    · rintro ⟨h₁, h₂⟩
      have heval : Module.evalEquiv F₂ G.CycleSpace (ev.symm y) = y :=
        ev.apply_symm_apply y
      have h₁' := (allSelectedTriple_iff_affineCylinder G e₁ x₁ hx₁
        (ev.symm y)).mpr (by simpa [heval] using h₁)
      have h₂' := (allSelectedTriple_iff_affineCylinder G e₂ x₂ hx₂
        (ev.symm y)).mpr (by simpa [heval] using h₂)
      exact ⟨h₁', h₂'⟩
  calc
    eventProbability (fun x => allSelectedTriple G e₁ x ∧
        allSelectedTriple G e₂ x) =
        Erdos1016.Proof.FinitePaleyZygmund.probability
          (fun x => allSelectedTriple G e₁ x ∧ allSelectedTriple G e₂ x) := rfl
    _ = Erdos1016.Proof.FinitePaleyZygmund.probability
          (fun y => allSelectedTriple G e₁ (ev.symm y) ∧
            allSelectedTriple G e₂ (ev.symm y)) :=
      Erdos1016.Proof.SelectedTripleCylinder.uniformEventProbability_congr_equiv
        ev (fun x => allSelectedTriple G e₁ x ∧ allSelectedTriple G e₂ x)
    _ = Erdos1016.Proof.AffineCylinders.probability
          (fun y => allSelectedTriple G e₁ (ev.symm y) ∧
            allSelectedTriple G e₂ (ev.symm y)) :=
      finiteProbability_eq_affineProbability _
    _ = _ := affineProbability_congr _ _ hevent

set_option maxHeartbeats 0 in
private theorem eventProbability_add_complement
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    [DecidableEq ι] (P : Ω → Prop) :
    eventProbability P + eventProbability (fun x => ¬ P x) = 1 := by
  rw [Erdos1016.Proof.BadVertexLinearBound.eventProbability_compl
    P]
  ring

set_option maxHeartbeats 0 in
private theorem forestEventProbability_eq
    (G : PhysicalGraph) (E : Finset G.Edge) :
    eventProbability (fun x : G.CycleSpace =>
      x ∈ G.outsideLinearForestStates E) =
      G.outsideLinearForestProbability E := by
  classical
  letI : DecidablePred
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E) :=
    fun x => Classical.propDecidable
      ((fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E) x)
  unfold eventProbability Erdos1016.Proof.FinitePaleyZygmund.probability
  unfold Erdos1016.PhysicalGraph.outsideLinearForestProbability
  change ((Finset.univ.filter
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E)).card : ℝ) /
      (Fintype.card G.CycleSpace : ℝ) =
    ((G.outsideLinearForestStates E).card : ℝ) / (2 : ℝ) ^ G.cycleRank
  have hden : (Fintype.card G.CycleSpace : ℝ) =
      (2 : ℝ) ^ G.cycleRank := by exact_mod_cast G.cycleSpace_card
  rw [hden]
  have hnum : (Finset.univ.filter
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E)) =
      G.outsideLinearForestStates E := by
    ext x
    simp
  have hnumCard : ((Finset.univ.filter
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E)).card : ℝ) =
      ((G.outsideLinearForestStates E).card : ℝ) := by
    exact_mod_cast congrArg Finset.card hnum
  rw [hnumCard]

/-- Many feasible selected triples, with controlled common information and
bounded exceptional neighbourhoods, contradict an outside-forest probability
above `1/2+1/R` when every selected triple destroys the forest property. -/
theorem impossible_many_selected_triples
    (G : PhysicalGraph) (E : Finset G.Edge) (R : ℕ)
    (hR : 5 ≤ R)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι → Fin 3 → G.Edge)
    (witness : ι → G.CycleSpace)
    (hfeasible : ∀ i, allSelectedTriple G (edges i) (witness i))
    (exceptional : ι → ι → Prop) [DecidableRel exceptional]
    (hcommon : ∀ i j, i ≠ j → ¬ exceptional i j →
      Module.finrank Erdos1016.Proof.AffineCylinders.F₂
        (Erdos1016.Proof.AffineCylinderPairs.CommonSubspace
          (tripleConstraintSpace G (edges i))
          (tripleConstraintSpace G (edges j))) ≤ 1)
    (hpartners : ∀ i,
      ((Finset.univ.filter (fun j => exceptional i j)).card : ℝ) ≤ 64)
    (vertices : ι → G.Vertex)
    (hinjective : ∀ i, Function.Injective (edges i))
    (hincident : ∀ i k, G.incident (edges i k) (vertices i))
    (houtside : ∀ i k, edges i k ∉ E)
    (hforest : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E)
    (hcard : 520 * R ≤ Fintype.card ι) :
    False := by
  classical
  let A : ι → G.CycleSpace → Prop := fun i x => allSelectedTriple G (edges i) x
  have hcontained : ∀ x, 1 ≤ eventCount A x →
      x ∉ G.outsideLinearForestStates E := by
    intro x hx
    exact Erdos1016.Proof.BadVertexTripleForestBridge.positive_selectedTripleCount_not_outsideLinearForestStates
      G E vertices edges hinjective hincident houtside x (by simpa [A] using hx)
  have hmean : (65 : ℝ) * (R : ℝ) ≤
      ∑ i, eventProbability (A i) := by
    calc
      (65 : ℝ) * (R : ℝ) = (520 * (R : ℕ) : ℝ) / 8 := by
        push_cast
        norm_num [div_eq_mul_inv]
        ring
      _ ≤ (Fintype.card ι : ℝ) / 8 := by
        have hcard' : (520 * (R : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) :=
          by exact_mod_cast hcard
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
          (by norm_num : (0 : ℝ) < 8)).2
        nlinarith [hcard']
      _ = ∑ _i : ι, (1 / 8 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ i, eventProbability (A i) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [A] using
          (allSelectedTriple_probability_ge_one_eighth G (edges i)
            ⟨witness i, hfeasible i⟩)
  have hdiag : ∀ i,
      eventProbability (fun x => A i x ∧ A i x) ≤ eventProbability (A i) := by
    intro i
    exact Erdos1016.Proof.BadVertexCylinderCount.eventProbability_mono
      (fun x => A i x ∧ A i x) (A i) (fun x hx => hx.1)
  have hordinary : ∀ i j, i ≠ j → ¬ exceptional i j →
      eventProbability (fun x => A i x ∧ A j x) ≤
        2 * eventProbability (A i) * eventProbability (A j) := by
    intro i j hij hnot
    have hpair := pairSelectedTriple_probability_eq_affineCylinders
      G (edges i) (edges j) (witness i) (witness j)
      (hfeasible i) (hfeasible j)
    have hbound := Erdos1016.Proof.SelectedTriplePairBounds.pair_probability_le_twice_product_of_common_finrank_le_one
        (tripleConstraintSpace G (edges i))
        (tripleConstraintSpace G (edges j))
        (tripleCylinderAssignment G (edges i) (witness i))
        (tripleCylinderAssignment G (edges j) (witness j))
        (hcommon i j hij hnot)
    have hpi := allSelectedTriple_probability_eq_affineCylinder
      G (edges i) (witness i) (hfeasible i)
    have hpj := allSelectedTriple_probability_eq_affineCylinder
      G (edges j) (witness j) (hfeasible j)
    rw [← hpair, ← hpi, ← hpj] at hbound
    simpa [A] using hbound
  have hexceptional : ∀ i j, exceptional i j →
      eventProbability (fun x => A i x ∧ A j x) ≤ eventProbability (A i) := by
    intro i j hij
    exact Erdos1016.Proof.BadVertexCylinderCount.eventProbability_mono
      (fun x => A i x ∧ A j x) (A i) (fun x hx => hx.1)
  have hsmall : eventProbability
      (fun x : G.CycleSpace => x ∉ G.outsideLinearForestStates E) <
        (1 / 2 : ℝ) - 1 / (R : ℝ) := by
    have hforestEvent := forestEventProbability_eq G E
    have hcomplement := eventProbability_add_complement (ι := ι)
      (fun x : G.CycleSpace => x ∈ G.outsideLinearForestStates E)
    rw [hforestEvent] at hcomplement
    linarith
  exact Erdos1016.Proof.BadVertexCylinderThreshold.impossible_many_cylinders_under_small_event
      A exceptional (fun x => x ∈ G.outsideLinearForestStates E) R hR
      hmean hdiag hordinary hexceptional hpartners hcontained hsmall

end Erdos1016.Proof.BadVertexSelectedTriples

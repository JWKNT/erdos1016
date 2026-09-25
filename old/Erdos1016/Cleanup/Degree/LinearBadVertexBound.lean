import Erdos1016.Probability.Cylinders.ThresholdMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section

namespace Erdos1016.Proof.BadVertexLinearBound

open Erdos1016.Proof.BadVertexCylinderCount
open Erdos1016.Proof.GraphicalThreshold

theorem eventProbability_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (U : Ω → Prop) :
    eventProbability (fun x => ¬ U x) = 1 - eventProbability U := by
  classical
  letI : DecidablePred U := fun a => Classical.propDecidable (U a)
  letI : DecidablePred (fun x : Ω => ¬ U x) :=
    fun a => Classical.propDecidable ((fun x : Ω => ¬ U x) a)
  let A := {x : Ω // U x}
  let B := {x : Ω // ¬ U x}
  have hcard : Fintype.card A + Fintype.card B = Fintype.card Ω := by
    let e : A ⊕ B ≃ Ω := {
      toFun := fun x => match x with
        | Sum.inl a => a.1
        | Sum.inr b => b.1
      invFun := fun x => if h : U x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩
      left_inv := by
        intro x
        cases x with
        | inl a => simp [A, a.2]
        | inr b => simp [B, b.2]
      right_inv := by
        intro x
        by_cases h : U x <;> simp [h]
    }
    calc
      Fintype.card A + Fintype.card B = Fintype.card (A ⊕ B) := by simp
      _ = Fintype.card Ω := Fintype.card_congr e
  have hprob (P : Ω → Prop) : eventProbability P =
      (Fintype.card {x // P x} : ℝ) / (Fintype.card Ω : ℝ) := by
    unfold eventProbability Erdos1016.Proof.FinitePaleyZygmund.probability
    rw [← Fintype.card_subtype]
  rw [hprob, hprob]
  change (Fintype.card B : ℝ) / (Fintype.card Ω : ℝ) =
    1 - (Fintype.card A : ℝ) / (Fintype.card Ω : ℝ)
  have hsum : (Fintype.card B : ℝ) + (Fintype.card A : ℝ) =
      (Fintype.card Ω : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm] using hcard)
  have hden : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  have hdiv := congrArg (fun z : ℝ => z / (Fintype.card Ω : ℝ)) hsum
  change (↑(Fintype.card B) + ↑(Fintype.card A)) / (Fintype.card Ω : ℝ) =
    (Fintype.card Ω : ℝ) / (Fintype.card Ω : ℝ) at hdiv
  rw [add_div, div_self hden] at hdiv
  linarith

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]




end Erdos1016.Proof.BadVertexLinearBound

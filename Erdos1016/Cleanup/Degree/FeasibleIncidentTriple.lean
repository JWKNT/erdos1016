import Erdos1016.Probability.Moments.SelectedDegree
import Erdos1016.Probability.Cylinders.IncidentTripleEvents

set_option autoImplicit false

/-!
# A feasible triple at every high active degree vertex

If at least four active edge coordinates meet a vertex, their all-one
coordinate event is feasible for some three of them. The proof uses the exact
half marginal of each active coordinate and the fact that the zero cycle word
is a positive-mass state.
-/

noncomputable section

namespace Erdos1016.Proof.BadVertexTripleExistence

open Erdos1016
open Erdos1016.Proof.ActiveDegreeMoment
open Erdos1016.Proof.ActiveEdgeUniform
open Erdos1016.Proof.ActiveTripleBridge

local notation "F₂" => ZMod 2

/-- Four or more active edges at one vertex contain three edges which can all
be selected by one cycle-space word. -/
theorem exists_feasible_triple_of_active_edges
    (G : PhysicalGraph) (v : G.Vertex) (F : Finset G.Edge)
    (hinc : ∀ e ∈ F, G.incident e v)
    (hactive : ∀ e ∈ F, ActiveEdge G e)
    (hcard : 4 ≤ F.card) :
    ∃ e : Fin 3 → G.Edge,
      (∀ i, e i ∈ F) ∧ (∀ i, G.incident (e i) v) ∧ Function.Injective e ∧
        ∃ x : G.CycleSpace, allSelectedTriple G e x := by
  classical
  let Z : G.CycleSpace → ℝ := selectedFamilyCount G F
  have hmean : Erdos1016.Proof.FinitePaleyZygmund.mean Z =
      (F.card : ℝ) / 2 := by
    change Erdos1016.Proof.FinitePaleyZygmund.mean
      (selectedFamilyCount G F) = _
    unfold Erdos1016.Proof.FinitePaleyZygmund.mean
    rw [mean_selectedFamilyCount_eq_expectedSelectedFamilySize]
    rw [expectedSelectedFamilySize_eq_half G F hactive]
  have hN : 0 < (Fintype.card G.CycleSpace : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨0⟩)
  have hzero : Z 0 = 0 := by
    simp [Z, selectedFamilyCount]
  have hexists : ∃ x : G.CycleSpace, 3 ≤ Z x := by
    by_contra hno
    push_neg at hno
    have hsmall : ∀ x : G.CycleSpace, Z x ≤ 2 := by
      intro x
      let Sx : Finset G.Edge := F.filter fun e => x.1 e = 1
      have hZcard : Z x = (Sx.card : ℝ) := by
        simp [Z, Sx, selectedFamilyCount, Finset.sum_boole]
      have hcardlt : Sx.card < 3 := by
        have hreal : (Sx.card : ℝ) < 3 := by
          rw [← hZcard]
          exact hno x
        exact_mod_cast hreal
      have hcardle : Sx.card ≤ 2 := by omega
      rw [hZcard]
      exact_mod_cast hcardle
    have hsumlt : (∑ x : G.CycleSpace, Z x) <
        ∑ _x : G.CycleSpace, (2 : ℝ) :=
      Finset.sum_lt_sum
        (fun x hx => hsmall x)
        ⟨0, Finset.mem_univ _, by rw [hzero]; norm_num⟩
    have hmeanlt : Erdos1016.Proof.FinitePaleyZygmund.mean Z < 2 := by
      unfold Erdos1016.Proof.FinitePaleyZygmund.mean
      apply (div_lt_iff₀ hN).2
      simpa [mul_comm] using hsumlt
    have hcardcast : (4 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
    rw [hmean] at hmeanlt
    linarith
  obtain ⟨x, hx⟩ := hexists
  let S : Finset G.Edge := F.filter fun e => x.1 e = 1
  have hZcard : Z x = (S.card : ℝ) := by
    simp [Z, S, selectedFamilyCount, Finset.sum_boole]
  have hScard : 3 ≤ S.card := by
    have hx' : (3 : ℝ) ≤ (S.card : ℝ) := by
      rw [← hZcard]
      exact hx
    exact_mod_cast hx'
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hScard
  let e : Fin 3 → G.Edge := fun i => (T.equivFinOfCardEq hTcard).symm i
  have heT : ∀ i, e i ∈ T := by
    intro i
    exact ((T.equivFinOfCardEq hTcard).symm i).property
  have heF : ∀ i, e i ∈ F := by
    intro i
    have hiS : e i ∈ S := hTS (heT i)
    exact (Finset.mem_filter.mp hiS).1
  have hinc' : ∀ i, G.incident (e i) v := by
    intro i
    exact hinc (e i) (heF i)
  have hinj : Function.Injective e := by
    intro i j hij
    apply (T.equivFinOfCardEq hTcard).symm.injective
    exact Subtype.ext hij
  have hselected : ∀ i, x.1 (e i) = 1 := by
    intro i
    have hiS : e i ∈ S := hTS (heT i)
    exact (Finset.mem_filter.mp hiS).2
  refine ⟨e, heF, hinc', hinj, x, ?_⟩
  change tripleObservation G e x = fun _ => (1 : F₂)
  funext i
  simp [tripleObservation, Erdos1016.Proof.ActiveEdgeUniform.edgeCoordinate,
    hselected i]

end Erdos1016.Proof.BadVertexTripleExistence

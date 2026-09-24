import Erdos1016.Cycles.Geometry.OrdinaryProximity
import Erdos1016.Probability.Moments.CycleTupleLowerBound

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos1016.Proof.RetainedCycleAvoidance

open scoped BigOperators
open BoundaryDecay SafeCore ConditionalMoments CycleProximity
open CycleExtensionProbability IsolatedCycleConditionalLaw

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance (G : PhysicalGraph) : DecidableEq G.CycleWord := Classical.decEq _

/-- Compatibility is literal disjointness of all different cycle supports. -/
def Compatible {G : PhysicalGraph} {A : Finset G.CycleWord} (k : ℕ) (u : Fin k → A) : Prop :=
  Pairwise (fun i j => Disjoint (Cycle.vertices (u i).1) (Cycle.vertices (u j).1))

def tupleFamily {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) : Finset G.CycleWord := Finset.univ.image (fun i => (u i).1)

theorem tupleFamily_subset {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) : tupleFamily u ⊆ A := by
  rintro C hC
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
  exact (u i).2

theorem tupleFamily_disjoint {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) (h : Compatible k u) :
    ∀ C ∈ tupleFamily u, ∀ D ∈ tupleFamily u, C ≠ D →
      Disjoint (Cycle.vertices C) (Cycle.vertices D) := by
  rintro C hC D hD hne
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hD
  exact h (fun hij => hne (congrArg (fun i => (u i).1) hij))

theorem tupleFamily_card_le {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) : (tupleFamily u).card ≤ k := by
  exact (Finset.card_image_le).trans (by simp)

theorem tupleEvent_tupleFamily {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) (x : G.CycleSpace) :
    tupleEvent (tupleFamily u) x ↔ ∀ i, Cycle.Event (u i).1 x := by
  simp [tupleEvent, tupleFamily]

theorem snoc_conditional_eq {G : PhysicalGraph} {A : Finset G.CycleWord} {k : ℕ}
    (u : Fin k → A) (a : A) :
    tupleEventProbability (fun a : A => Cycle.Event a.1) (Fin.snoc u a) /
      tupleEventProbability (fun a : A => Cycle.Event a.1) u =
      conditionalDensity (tupleEvent (tupleFamily u)) (Cycle.Event a.1) := by
  have hden : (fun x : G.CycleSpace => ∀ i, Cycle.Event (u i).1 x) =
      tupleEvent (tupleFamily u) := by
    funext x
    exact propext (tupleEvent_tupleFamily u x).symm
  have hnum : (fun x : G.CycleSpace => ∀ i : Fin (k + 1), Cycle.Event ((Fin.snoc u a : Fin (k+1) → A) i).1 x) =
      (fun x => tupleEvent (tupleFamily u) x ∧ Cycle.Event a.1 x) := by
    funext x
    apply propext
    rw [tupleEvent_tupleFamily]
    constructor
    · intro hx
      exact ⟨fun i => by simpa using hx i.castSucc, by simpa using hx (Fin.last k)⟩
    · rintro ⟨hx, ha⟩ i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · simpa using hx i
      · simpa using ha
  simp only [tupleEventProbability, conditionalDensity, hden, hnum]

/-- Pairwise far cycles have disjoint supports: a shared vertex would itself
be a length-zero witness to proximity. -/
theorem good_compatible {G : PhysicalGraph} (J : Finset G.Vertex) (q : ℕ)
    (A : Finset G.CycleWord) (hAJ : ∀ C ∈ A, Cycle.vertices C ⊆ J)
    (k : ℕ) (u : Fin k → A)
    (h : InvalidTupleMass.pairwiseRGood (fun C D : A => Near G J q C.1 D.1) k u) :
    Compatible k u := by
  induction k with
  | zero => exact fun i => Fin.elim0 i
  | succ k ih =>
    have hpre := ih (Fin.init u) h.1
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · exact hpre (fun heq => hij (congrArg Fin.castSucc heq))
      · apply Classical.byContradiction
        intro hoverlap
        exact h.2 i (near_of_overlap J q _ _ (hAJ _ (u i.castSucc).2) hoverlap)
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · apply Disjoint.symm
        apply Classical.byContradiction
        intro hoverlap
        exact h.2 j (near_of_overlap J q _ _ (hAJ _ (u j.castSucc).2) hoverlap)
      · exact (hij rfl).elim

theorem sum_eligible_eq {G : PhysicalGraph} (J : Finset G.Vertex) (q : ℕ)
    (A F : Finset G.CycleWord) (C : G.CycleWord) :
    (∑ a : A, if Disjoint (tupleVertices F) (Cycle.vertices a.1) ∧ Near G J q C a.1
      then conditionalDensity (tupleEvent F) (Cycle.Event a.1) else 0) =
    ∑ D ∈ eligible G A F, if Near G J q C D
      then conditionalDensity (tupleEvent F) (Cycle.Event D) else 0 := by
  classical
  rw [eligible, Finset.sum_filter]
  have hsum := (Finset.sum_coe_sort A
    (fun D => if Disjoint (tupleVertices F) (Cycle.vertices D) then
      (if Near G J q C D then conditionalDensity (tupleEvent F) (Cycle.Event D) else 0)
      else 0)).symm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

/-- Literal retained-cycle instance of the finite conditional-moment bound.
Exact marginals and the conditional neighbor load are supplied by their
separate graph theorems. Incompatibility, product lower bounds, and all far
extension laws are derived from actual cycle and complement geometry. -/
theorem finite_avoidance_le
    {G : PhysicalGraph} (hG : G.IsConnected)
    (J : Finset G.Vertex) (A : Finset G.CycleWord) (K q : ℕ)
    (hK : Even K) (hKtwo : 2 ≤ K) (hq : 1 ≤ q) (hKq : K ≤ q + 1)
    (d : ℝ) (hd : 0 ≤ d)
    (hAJ : ∀ C ∈ A, Cycle.vertices C ⊆ J)
    (hcubic : ∀ C ∈ A, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hinduced : ∀ C ∈ A, Cycle.IsInduced C)
    (hmarginal : ∀ C ∈ A, Cycle.probability C = 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C)
    (v₀ : G.Vertex) (hv₀ : ∀ C ∈ A, v₀ ∉ Cycle.vertices C)
    (hpositive : 0 < ∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C)
    (hgeometry : ∀ F ⊆ A,
      (∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint (Cycle.vertices C) (Cycle.vertices D)) →
      F.card ≤ K → ∃ B ∈ components G (tupleVertices F)ᶜ,
        ∀ R ∈ components G (tupleVertices F)ᶜ, R ≠ B →
          R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
          (∀ v ∈ R, G.degree v = 3) ∧ R.card + 2 ≤ K ∧
          (∀ C ∈ F, ∀ e f, e ∈ crossing G R (Cycle.vertices C) →
            f ∈ crossing G R (Cycle.vertices C) → e = f))
    (hload : ∀ F ⊆ A,
      (∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint (Cycle.vertices C) (Cycle.vertices D)) →
      F.card < K → ∀ C ∈ A,
        (∑ D ∈ eligible G A F, if Near G J q C D then
          conditionalDensity (tupleEvent F) (Cycle.Event D) else 0) ≤ d) :
    Finite.density (fun x : G.CycleSpace => ∀ C ∈ A, ¬ Cycle.Event C x) ≤
      Real.exp (-(∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C)) +
        (∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C) ^ (K + 1) /
          ((K + 1).factorial : ℝ) +
        d * (∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C) *
          Real.exp ((∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C) +
            (Nat.choose K 2 : ℝ) * d /
              (∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C)) := by
  classical
  letI : Nonempty G.CycleSpace := ⟨0⟩
  let P : A → G.CycleSpace → Prop := fun a => Cycle.Event a.1
  let w : A → ℝ := fun a => 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length a.1
  let lambdaVar := ∑ C ∈ A, 1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length C
  let R : A → A → Prop := fun C D => Near G J q C.1 D.1
  have hsum : ∑ a, w a = lambdaVar := by
    exact Finset.sum_coe_sort A (fun C => (1 : ℝ) / 2 ^ BoundaryDecay.Cycle.length C)
  have hprefix : ∀ k < K, ∀ (u : Fin k → A) (a : A), Compatible (k+1) (Fin.snoc u a) → Compatible k u := by
    intro k hk u a hc i j hij
    simpa using hc (fun h => hij (Fin.castSucc_injective _ h))
  have hfar : ∀ k < K, ∀ (u : Fin k → A) (a : A),
      Function.Injective (Fin.snoc u a) → Compatible (k+1) (Fin.snoc u a) →
      (∀ i, ¬ R (u i) a) → tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u = w a := by
    intro k hk u a hinj hc hf
    let F := tupleFamily u
    have hpre := hprefix k hk u a hc
    have hFdisj := tupleFamily_disjoint u hpre
    have hFD : ∀ C ∈ F, Disjoint (Cycle.vertices C) (Cycle.vertices a.1) := by
      intro C hC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      simpa using hc (Fin.castSucc_ne_last i)
    have hiF : insert a.1 F ⊆ A := Finset.insert_subset a.2 (tupleFamily_subset u)
    have hdisj : ∀ C ∈ insert a.1 F, ∀ D ∈ insert a.1 F, C ≠ D →
        Disjoint (Cycle.vertices C) (Cycle.vertices D) := by
      intro C hC D hD hne
      rcases Finset.mem_insert.mp hC with rfl | hC
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (hne rfl).elim
        · exact (hFD D hD).symm
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact hFD C hC
        · exact hFdisj C hC D hD hne
    have hcard : (insert a.1 F).card ≤ K :=
      (Finset.card_insert_le _ _).trans (by have := tupleFamily_card_le u; dsimp [F]; omega)
    obtain ⟨B, hB, hs⟩ := hgeometry (insert a.1 F) hiF hdisj hcard
    have hU : tupleVertices (insert a.1 F) = tupleVertices F ∪ Cycle.vertices a.1 := by
      simp [tupleVertices, Finset.biUnion_insert, Finset.union_comm]
    rw [hU] at hB hs
    rw [snoc_conditional_eq]
    apply conditional_cycle_probability_eq_weight_of_far hG J F a.1 B q hq hFdisj hFD
      (fun C hC => hAJ C (tupleFamily_subset u hC)) (hAJ _ a.2)
      (fun C hC => hcubic C (tupleFamily_subset u hC)) (hcubic _ a.2) (hinduced _ a.2) hB
    · intro T hT hTB
      obtain ⟨hTJ, ht, hcub, hsize, hone⟩ := hs T hT hTB
      exact ⟨hTJ, ht, hcub, by omega, hone a.1 (Finset.mem_insert_self _ _)⟩
    · intro v z hv hz p
      apply lt_of_not_ge
      intro hlen
      obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact hf i ⟨v, z, hv, hz, p, hlen⟩
  have hproduct : ∀ k ≤ K, ∀ (u : Fin k → A), Function.Injective u → Compatible k u →
      tupleProduct w u ≤ tupleEventProbability P u := by
    intro k hk u hinj hc
    have h := disjoint_cycle_tuple_probability_ge_product hG (Finset.univ : Finset (Fin k))
      (fun i => (u i).1) (fun i _ j _ hij => hc hij)
      (fun i _ => hcubic _ (u i).2) v₀ (by
        intro hv
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
        exact hv₀ _ (u i).2 hi)
    simpa only [tupleProduct, tupleEventProbability, w, P, Finset.mem_univ, forall_true_left] using h
  have hcompatible : ∀ k ≤ K, ∀ (u : Fin k → A), Function.Injective u →
      ∀ x, (∀ i, P (u i) x) → Compatible k u := by
    intro k hk u hinj x hx i j hij
    apply Classical.byContradiction
    intro hoverlap
    have heq := Cycle.eq_of_joint_overlap (u i).1 (u j).1 x (hx i) (hx j) hoverlap
    exact hij (hinj (Subtype.ext heq))
  have hnear : ∀ k < K, ∀ (u : Fin k → A), Function.Injective u → Compatible k u → ∀ i : Fin k,
      (∑ a, if (Function.Injective (Fin.snoc u a) ∧ Compatible (k+1) (Fin.snoc u a)) ∧ R (u i) a
        then tupleEventProbability P (Fin.snoc u a) / tupleEventProbability P u else 0) ≤ d := by
    intro k hk u hinj hc i
    have h := hload (tupleFamily u) (tupleFamily_subset u) (tupleFamily_disjoint u hc)
      ((tupleFamily_card_le u).trans_lt hk) (u i).1 (u i).2
    rw [← sum_eligible_eq] at h
    apply le_trans (Finset.sum_le_sum ?_) h
    intro a _
    by_cases ha : (Function.Injective (Fin.snoc u a) ∧ Compatible (k+1) (Fin.snoc u a)) ∧ R (u i) a
    · have hdisj : Disjoint (tupleVertices (tupleFamily u)) (Cycle.vertices a.1) := by
        apply Finset.disjoint_left.mpr
        intro v hv hva
        obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
        have hd : Disjoint (Cycle.vertices (u j).1) (Cycle.vertices a.1) := by
          simpa using ha.1.2 (Fin.castSucc_ne_last j)
        exact Finset.disjoint_left.mp hd hv hva
      rw [if_pos ha, if_pos ⟨hdisj, ha.2⟩, snoc_conditional_eq]
    · rw [if_neg ha]
      split_ifs
      · exact div_nonneg (Finite.density_nonneg _) (Finite.density_nonneg _)
      · rfl
  have hrow : ∀ a : A, (∑ b, if R a b then w b else 0) ≤ d := by
    intro a
    have h := hload ∅ (Finset.empty_subset A) (by simp) (by simp; omega) a.1 a.2
    rw [← sum_eligible_eq] at h
    have hempty : ∀ b : A, conditionalDensity (tupleEvent (∅ : Finset G.CycleWord))
        (Cycle.Event b.1) = w b := by
      intro b
      have ht : Finite.density (fun _ : G.CycleSpace => True) = 1 := by
        simp only [Finite.density, Finite.count, if_true, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
        apply div_self
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card G.CycleSpace ≠ 0)
      have he : tupleEvent (∅ : Finset G.CycleWord) = (fun _ : G.CycleSpace => True) := by
        funext x
        simp [tupleEvent]
      unfold conditionalDensity
      rw [he]
      simp only [true_and, ht, div_one]
      exact hmarginal _ b.2
    simpa only [tupleVertices, Finset.biUnion_empty, Finset.disjoint_empty_left, true_and, hempty, R] using h
  have hfinal := finite_avoidance_le_of_conditional_extension_load P K hK hKtwo R Compatible
    w lambdaVar d hpositive hd (fun a => by positivity) hsum (fun a => hmarginal _ a.2)
    hcompatible hprefix hfar (by
      intro k hk u hi hc i
      convert hnear k hk u hi hc i using 1
      congr 1
      funext a
      split_ifs <;> rfl) hproduct
    (fun a => near_self J q _ (hAJ _ a.2)) hrow
    (fun k hk u h => good_compatible J q A hAJ k u h)
  have hevent : (fun x : G.CycleSpace => finiteEventCount Finset.univ P x = 0) =
      (fun x : G.CycleSpace => ∀ C ∈ A, ¬ Cycle.Event C x) := by
    funext x
    apply propext
    simp [finiteEventCount, P, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  rw [hevent] at hfinal
  exact hfinal

end Erdos1016.Proof.RetainedCycleAvoidance
end

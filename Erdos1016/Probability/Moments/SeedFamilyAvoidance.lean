import Erdos1016.Probability.Moments.SeedPairCorrelation
import Erdos1016.CycleSpace.Graphical.ExceptionalRegionPacking
import Erdos1016.Probability.Moments.PackingRowBound

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Weighted avoidance for actual supported cycle seeds

The exceptional relation is defined by the actual zero-cut probabilities.
Its packing bound is proved from the connected contraction lemma. The only
quantitative geometric inputs are a link-factor envelope and the vertex
weight load; no pair-moment or exceptional-row hypothesis is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph.SeedFamilyAvoidance
open BoundaryDecay BoundaryTrace SeedPairCorrelation

variable {ι : Type*} [DecidableEq ι]
variable (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)
  (seed : ∀ i, G.internalCycleSpace (U i))

/-- The geometric mean assigned to the literal nonzero seed coordinates. -/
def weight (i : ι) : ℝ := 1 / (2 : ℝ) ^ (G.seedSupport (seed i).1).card

/-- Exceptional partners are disjoint cycles whose actual zero-cut correlation
exceeds two. Overlapping distinct cycles are handled by incompatibility. -/
def Exceptional (i j : ι) : Prop :=
  Disjoint (U i) (U j) ∧
    2 * Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U i)) *
      Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U j)) <
      Finite.density (fun x : G.CycleSpace =>
        x ∈ G.zeroCutSpace (U i) ∧ x ∈ G.zeroCutSpace (U j))

private theorem zeroCut_density_pos (A : Finset G.Vertex) :
    0 < Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace A) := by
  have he : (fun x : G.CycleSpace => x ∈ G.zeroCutSpace A) =
      fun x : G.CycleSpace => ∀ e ∈ G.cutEdges A, x.1 e = 0 := by
    funext x
    exact propext (G.mem_zeroCutSpace_iff A x)
  rw [he]
  exact lt_of_lt_of_le (by positivity) (G.zeroCoordinates_probability_ge _)

omit [DecidableEq ι] in
private theorem ambient_connected (i : ι)
    (hc : ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected) :
    (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected := by
  apply hc.mono
  intro u v huv
  rcases huv with ⟨hne, e, he, hend⟩
  exact ⟨hne, e, hend⟩

/-- The actual normalized seed sum has the required second moment. -/
theorem second_moment_le (s : Finset ι) (L : ℕ) (M b : ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s,
      ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (seed i).1 = (seed j).1 → i = j)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then weight G U seed i else 0) ≤ b)
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Exceptional G U i j →
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ M) :
    average (fun x => (∑ i ∈ s, G.normalizedSeedIndicator (seed i).1 x) ^ 2) ≤
      2 * (∑ i ∈ s, weight G U seed i) ^ 2 +
        (1 + M * L * L * b) * (∑ i ∈ s, weight G U seed i) := by
  classical
  have hw (i : ι) : 0 ≤ weight G U seed i := by unfold weight; positivity
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s)
      (hd : Disjoint (U i) (U j)) :
      average (fun x => G.normalizedSeedIndicator (seed i).1 x *
        G.normalizedSeedIndicator (seed j).1 x) =
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) *
        weight G U seed i * weight G U seed j :=
    normalizedSelectedSeed_pair G _ _ hG hd
      (ambient_connected G U seed i (hconn i hi))
      (ambient_connected G U seed j (hconn j hj))
      (seed i) (seed j) (htwo i hi) (htwo j hj) (hdegree i hi) (hdegree j hj)
  apply weighted_sum_second_moment_le s _ (weight G U seed) (Exceptional G U)
  · exact fun i hi x => (G.normalizedSeedIndicator_bounds (seed i).1 x).1
  · exact fun i hi x => (G.normalizedSeedIndicator_bounds (seed i).1 x).2
  · exact fun i hi => G.average_normalizedSeedIndicator (seed i).1
  · intro i hi j hj hij hex
    by_cases hd : Disjoint (U i) (U j)
    · have hnot : ¬ (2 * Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U i)) *
          Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U j)) <
          Finite.density (fun x : G.CycleSpace =>
            x ∈ G.zeroCutSpace (U i) ∧ x ∈ G.zeroCutSpace (U j))) := fun h => hex ⟨hd, h⟩
      have hcut := zeroCut_pair_exact G (U i) (U j) hG hd
        (ambient_connected G U seed i (hconn i hi))
        (ambient_connected G U seed j (hconn j hj))
      have hfactor : dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ 2 := by
        have hle := le_of_not_gt hnot
        rw [hcut] at hle
        have hpos := mul_pos (zeroCut_density_pos G (U i)) (zeroCut_density_pos G (U j))
        nlinarith
      rw [hpair i hi j hj hd]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (hw i)) (hw j)
    · have hz : average (fun x => G.normalizedSeedIndicator (seed i).1 x *
          G.normalizedSeedIndicator (seed j).1 x) = 0 :=
        normalizedIndicator_joint_eq_zero _ _ _ _
          (G.selectedSeed_overlap_incompatible (U i) (U j) (seed i) (seed j)
            (hconn i hi) (hconn j hj) (htwo i hi) (htwo j hj)
            (hdegree i hi) (hdegree j hj) (fun h => hij (hinj i hi j hj h)) hd)
      rw [hz]
      exact mul_nonneg (mul_nonneg (by norm_num) (hw i)) (hw j)
  · intro i hi
    let T := s.filter (fun j => i ≠ j ∧ Exceptional G U i j)
    have hT (j : ι) (hj : j ∈ T) : j ∈ s ∧ i ≠ j ∧ Exceptional G U i j :=
      Finset.mem_filter.mp hj
    have hpack : ∀ F ⊆ T, (∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (U j) (U k)) →
        F.card ≤ L := by
      intro F hFT hdisj
      have hp := G.exceptional_cycle_packing_card_le (U i) (seed i).1.1
        (htwo i hi) (seed i).2 (hdegree i hi) U F hG
        (ambient_connected G U seed i (hconn i hi))
        (fun j hj => ambient_connected G U seed j (hconn j (hT j (hFT hj)).1))
        (fun j hj => (hT j (hFT hj)).2.2.1) hdisj
      apply (hp ?_).trans (hlen i hi)
      intro j hj
      have he (A : Finset G.Vertex) : DisjointRegionCuts.ZeroCut G A =
          fun x : G.CycleSpace => x ∈ G.zeroCutSpace A := by
        funext x
        exact propext (G.mem_zeroCutSpace_iff A x).symm
      simpa only [he] using (hT j (hFT hj)).2.2.2
    have hloadT (v : G.Vertex) :
        (∑ j ∈ T, if v ∈ U j then weight G U seed j else 0) ≤ b := by
      apply le_trans _ (hload v)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro j hj hn
      split_ifs
      · exact hw j
      · exact le_refl 0
    have hrow := exceptional_row_le_of_packing T U L L (weight G U seed)
      (fun j => average (fun x => G.normalizedSeedIndicator (seed i).1 x *
        G.normalizedSeedIndicator (seed j).1 x)) (weight G U seed i) M b
      (hw i) hM hb (fun j hj => hw j)
      (fun j hj => by
        obtain ⟨v⟩ := (hconn j (hT j hj).1).nonempty
        exact ⟨v.1, v.2⟩)
      (fun j hj => hlen j (hT j hj).1) hpack hloadT
      (fun j hj => by
        dsimp only
        rw [hpair i hi j (hT j hj).1 (hT j hj).2.2.1]
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hlinks i hi j (hT j hj).1
            (hT j hj).2.1 (hT j hj).2.2) (hw i)) (hw j)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h)
    rw [mul_comm (weight G U seed i)] at hrow
    apply le_trans (le_of_eq ?_) hrow
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> rfl

/-- The sharp Cauchy--Schwarz consequence for the actual cycle-avoidance event. -/
theorem avoidance_le (s : Finset ι) (L : ℕ) (M b : ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s,
      ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (seed i).1 = (seed j).1 → i = j)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then weight G U seed i else 0) ≤ b)
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Exceptional G U i j →
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ M)
    (hmean : 0 < ∑ i ∈ s, weight G U seed i) :
    Finite.density (fun x : G.CycleSpace => ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x) ≤
      1 / 2 + (1 + M * L * L * b) /
        (4 * (∑ i ∈ s, weight G U seed i) + 2 * (1 + M * L * L * b)) := by
  classical
  have hz : (fun x : G.CycleSpace => ∀ i ∈ s, ¬ G.SelectedSeed (seed i).1 x) =
      fun x => (∑ i ∈ s, G.normalizedSeedIndicator (seed i).1 x) = 0 := by
    funext x
    apply propext
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => (G.normalizedSeedIndicator_bounds (seed i).1 x).1)]
    apply forall₂_congr
    intro i hi
    exact (normalizedIndicator_eq_zero_iff _ _ (by positivity)
      (lt_of_lt_of_le (by positivity) (G.selectedSeed_probability_ge (seed i).1)) x).symm
  rw [hz]
  apply zero_density_le_half_add_of_second_moment _ _ _ hmean (by positivity)
  · simp only [average_sum, G.average_normalizedSeedIndicator, weight]
  · exact second_moment_le G U seed s L M b hG hconn htwo hdegree hinj hlen hM hb hload hlinks

end Erdos1016.FiniteMultiGraph.SeedFamilyAvoidance

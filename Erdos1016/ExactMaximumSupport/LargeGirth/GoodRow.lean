import Erdos1016.ExactMaximumSupport.LargeGirth.Orientation
import Erdos1016.ExactMaximumSupport.LargeGirth.TwoLinkMoment
import Erdos1016.Graph.PackingCover

set_option autoImplicit false

/-!
# A heavy row of actual good cycle pairs

Good pairs have exactly two links, no direct edge, and the second support
lies on the anchor side of the first. Directly joined pairs are bounded by
the load on the outside ends of the first support's cut edges.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open FiniteMultiGraph PolynomialBound.TwoLinkMoment PolynomialBound.Separation
open FiniteMultiGraph.SeedFamilyAvoidance FiniteMultiGraph.SeedPairCorrelation
open BoundaryDecay BoundaryTrace

local instance goodRowDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Outside ends of the physical cut edges. Parallel labels can have the
same outside end, which only decreases the size of this set. -/
def cutOutsideVertices (G : FiniteMultiGraph) (A : Finset G.Vertex) : Finset G.Vertex :=
  (G.cutEdges A).image fun e => if G.src e ∈ A then G.dst e else G.src e

theorem cutOutsideVertices_card_le (G : FiniteMultiGraph) (A : Finset G.Vertex) :
    (cutOutsideVertices G A).card ≤ (G.cutEdges A).card := Finset.card_image_le

/-- A region joined to a disjoint region meets its outside cut endpoints. -/
theorem directLabels_hit_cutOutsideVertices (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (hd : Disjoint A B) (hj : (G.directLabels A B).Nonempty) :
    (cutOutsideVertices G A ∩ B).Nonempty := by
  obtain ⟨e, he⟩ := hj
  rcases (G.mem_directLabels A B e).mp he with h | h
  · have hout : G.dst e ∉ A := fun ha => Finset.disjoint_left.mp hd ha h.2
    refine ⟨G.dst e, Finset.mem_inter.mpr ⟨?_, h.2⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨e, ?_, by simp [h.1]⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h.1, hout⟩⟩
  · have hout : G.src e ∉ A := fun ha => Finset.disjoint_left.mp hd ha h.1
    refine ⟨G.src e, Finset.mem_inter.mpr ⟨?_, h.1⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨e, ?_, by simp [hout]⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hout, h.2⟩⟩

variable {ι : Type*} (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)

/-- Disjoint supports joined by at least one physical edge. -/
def joinedPair (i j : ι) : ℝ :=
  if Disjoint (U i) (U j) ∧ (G.directLabels (U i) (U j)).Nonempty then 1 else 0

/-- The exact graph predicate used for good ordered pairs. -/
def goodTwoLink (p : G.Vertex) (i j : ι) : ℝ :=
  if twoLink G U i j = 1 ∧
    ¬ Disjoint (↑(U j) : Set G.Vertex) (side G.toSimpleGraph (↑(U i)) p) ∧
    ¬ (G.directLabels (U i) (U j)).Nonempty then 1 else 0

theorem twoLink_le_good_far_joined (p : G.Vertex) (i j : ι) :
    twoLink G U i j ≤ goodTwoLink G U p i j + farTwoLink G U p i j + joinedPair G U i j := by
  rcases twoLink_eq_zero_or_one G U i j with hz | hone
  · simp only [goodTwoLink, farTwoLink, joinedPair, hz]
    split_ifs <;> norm_num
  · have hd := ((twoLink_eq_one_iff G U i j).mp hone).2.1
    simp only [goodTwoLink, farTwoLink, joinedPair, hone, hd, true_and]
    split_ifs <;> norm_num
    all_goals tauto

/-- A uniform vertex-load bound controls every row of joined cycle pairs. -/
theorem joinedPair_row_le (s : Finset ι) (a : ι → ℝ) (b : ℝ) (i : ι)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ j ∈ s, if v ∈ U j then a j else 0) ≤ b) :
    (∑ j ∈ s, joinedPair G U i j * a j) ≤ (G.cutEdges (U i)).card * b := by
  classical
  let T := s.filter fun j => Disjoint (U i) (U j) ∧ (G.directLabels (U i) (U j)).Nonempty
  have hsub : T ⊆ s := Finset.filter_subset _ _
  have hhit : ∀ j ∈ T, (cutOutsideVertices G (U i) ∩ U j).Nonempty := by
    intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    exact directLabels_hit_cutOutsideVertices G (U i) (U j) hh.1 hh.2
  have hloadT : ∀ v, (∑ j ∈ T, if v ∈ U j then a j else 0) ≤ b := by
    intro v
    apply le_trans ?_ (hload v)
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro j hj _
    split_ifs <;> simp [ha j hj]
  have hmass := PackingCover.mass_le_vertex_load T U (cutOutsideVertices G (U i)) a b
    (fun j hj => ha j (hsub hj)) hhit (fun v _ => hloadT v)
  have heq : (∑ j ∈ s, joinedPair G U i j * a j) = ∑ j ∈ T, a j := by
    simp only [T, Finset.sum_filter, joinedPair]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [heq]
  exact hmass.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast cutOutsideVertices_card_le G (U i)) hb)

/-- The row bound in terms of the length of a two-regular support. -/
theorem joinedPair_cycle_row_le (s : Finset ι) (a : ι → ℝ) (b : ℝ) (i : ι)
    (x : G.EdgeWord) (hx : ∀ v ∈ U i, G.selectedDegree x v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges (U i) → x e = 0)
    (hdegree : ∀ v ∈ U i, G.degree v ≤ 3)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ j ∈ s, if v ∈ U j then a j else 0) ≤ b) :
    (∑ j ∈ s, joinedPair G U i j * a j) ≤ (U i).card * b := by
  exact (joinedPair_row_le G U s a b i ha hb hload).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast
      G.cutEdges_card_le_of_two_regular (U i) x hx hsupport hdegree) hb)

/-- Actual graph orientations and joined-pair loads give a good row of
weight above eight. The remaining hypothesis is total two-link weight. -/
theorem exists_goodTwoLink_row_gt_eight (p : G.Vertex) (s : Finset ι) (a : ι → ℝ)
    (seed : ∀ i, G.internalCycleSpace (U i)) (L : ℕ) (b η : ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hp : ∀ i ∈ s, p ∉ U i)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ b)
    (hjoined : L * b ≤ 1 / 2) (hμ : 30 < ∑ i ∈ s, a i) (hη : η ≤ 1 / 2)
    (hW : (2 / 3 : ℝ) * (∑ i ∈ s, a i) ^ 2 -
      (1 + η) * (∑ i ∈ s, a i) ≤
        ∑ i ∈ s, ∑ j ∈ s, twoLink G U i j * (a i * a j)) :
    ∃ i ∈ s, 8 < ∑ j ∈ s, goodTwoLink G U p i j * a j := by
  apply Averaging.exists_good_row_gt_eight s a (twoLink G U) (farTwoLink G U p)
    (joinedPair G U) (goodTwoLink G U p) η ha hμ hη
    (fun i _ j _ => twoLink_le_good_far_joined G U p i j)
    (fun i hi j hj => farTwoLink_add_reverse_le G U p i j hG (hconn i hi) (hconn j hj) (hp i hi)) hW
  intro i hi
  have hrow := joinedPair_cycle_row_le G U s a b i (seed i).1.1
    (htwo i hi) (seed i).2 (hdegree i hi) ha hb hload
  exact hrow.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast hlen i hi) hb).trans hjoined)

/-- A forest probability of two fifths and the quantitative cycle-load
hypotheses produce a good row of weight above eight. Every pair predicate
and every moment in this conclusion is derived from the actual graph. -/
theorem exists_goodTwoLink_row_gt_eight_of_forest
    (p : G.Vertex) (s : Finset ι) (seed : ∀ i, G.internalCycleSpace (U i))
    (L : ℕ) (M b : ℝ) (E : Finset G.Edge)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s,
      ((G.selectedGraph (seed i).1.1).induce (↑(U i) : Set G.Vertex)).Connected)
    (hp : ∀ i ∈ s, p ∉ U i)
    (htwo : ∀ i ∈ s, ∀ v ∈ U i, G.selectedDegree (seed i).1.1 v = 2)
    (hdegree : ∀ i ∈ s, ∀ v ∈ U i, G.degree v ≤ 3)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (seed i).1 = (seed j).1 → i = j)
    (hlen : ∀ i ∈ s, (U i).card ≤ L)
    (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then weight G U seed i else 0) ≤ b)
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Exceptional G U i j →
      dyadic ((Nat.card (Links G (U i) (U j)) : ℤ) - 1) ≤ M)
    (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E)
    (hforest : (2 / 5 : ℝ) ≤
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)))
    (hjoined : L * b ≤ 1 / 2) (hμ : 30 < ∑ i ∈ s, weight G U seed i)
    (hη : M * L * L * b ≤ 1 / 2) :
    ∃ i ∈ s, 8 < ∑ j ∈ s, goodTwoLink G U p i j * weight G U seed j := by
  have hne : ∀ i ∈ s, (seed i).1 ≠ 0 := by
    intro i hi hz
    obtain ⟨v⟩ := (hconn i hi).nonempty
    have hd := htwo i hi v.1 v.2
    have hw : (seed i).1.1 = 0 := congrArg Subtype.val hz
    rw [hw, G.selectedDegree_zero] at hd
    omega
  have hW := twoLink_weight_ge_of_forest G U seed s L M b hG hconn htwo hdegree
    hinj hlen hM hb hload hlinks E hne hE hforest
  apply exists_goodTwoLink_row_gt_eight G U p s (weight G U seed) seed L b
    (M * L * L * b) hG ?_ hp htwo hdegree hlen ?_ hb hload hjoined hμ hη hW
  · intro i hi
    apply (hconn i hi).mono
    intro u v huv
    rcases huv with ⟨hne, e, _, hend⟩
    exact ⟨hne, e, hend⟩
  · intro i _
    unfold weight
    positivity

end Erdos1016.ExactMaximumSupport.LargeGirth

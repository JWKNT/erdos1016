import Erdos1016.ExactMaximumSupport.LargeGirth.DeletedReach
import Erdos1016.PolynomialBound.Chain

set_option autoImplicit false

/-!
# Selecting a large family of separators

A heavy row of good pairs has a heavy subfamily with one common attachment.
A maximal disjoint subfamily then gives the separator family used by the
existing chain theorem. The weight bound follows from the actual vertex load.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open PolynomialBound.Separation PolynomialBound.ParallelLinks
open PolynomialBound.TwoLinkMoment FiniteMultiGraph
open FiniteMultiGraph.SeedFamilyAvoidance FiniteMultiGraph.SeedPairCorrelation
open BoundaryTrace BoundaryDecay

local instance chainSelectionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A cover by at most `L` witnesses has a row of weight greater than
`γ / L` when the covered total is greater than `γ`. -/
theorem exists_heavy_cover_row {ι κ : Type*} (s : Finset ι) (H : Finset κ)
    (R : κ → ι → Prop) (a : ι → ℝ) (L : ℕ) (γ : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hL : 0 < L) (hγ : 0 ≤ γ)
    (hcard : H.card ≤ L) (hcover : ∀ i ∈ s, ∃ u ∈ H, R u i)
    (hmass : γ < ∑ i ∈ s, a i) :
    ∃ u ∈ H, γ / L < ∑ i ∈ s, if R u i then a i else 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hterm : ∀ i ∈ s, a i ≤ ∑ u ∈ H, if R u i then a i else 0 := by
    intro i hi
    obtain ⟨u, hu, hui⟩ := hcover i hi
    have hh := Finset.single_le_sum (f := fun u => if R u i then a i else 0)
      (fun u _ => by dsimp only; split_ifs <;> simp [ha i hi]) hu
    simpa [hui] using hh
  have htotal : (∑ i ∈ s, a i) ≤ ∑ u ∈ H, ∑ i ∈ s, if R u i then a i else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum hterm
  have hrows : (∑ u ∈ H, ∑ i ∈ s, if R u i then a i else 0) ≤ H.card * (γ / L) := by
    calc
      _ ≤ ∑ _u ∈ H, γ / L := Finset.sum_le_sum hn
      _ = _ := by simp
  have hsize : (H.card : ℝ) * (γ / L) ≤ γ := by
    calc
      _ ≤ (L : ℝ) * (γ / L) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) (by positivity)
      _ = γ := by field_simp
  linarith

/-- A maximal disjoint family carries a cardinality lower bound from the
covered weight and the uniform vertex load. -/
theorem exists_large_disjoint_family {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (s : Finset ι) (U : ι → Finset V) (a : ι → ℝ) (L : ℕ) (b γ : ℝ)
    (hne : ∀ i ∈ s, (U i).Nonempty) (hsize : ∀ i ∈ s, (U i).card ≤ L)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ i ∈ s, if v ∈ U i then a i else 0) ≤ b)
    (hmass : γ < ∑ i ∈ s, a i) :
    ∃ F ⊆ s, (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j)) ∧
      γ < (F.card : ℝ) * L * b := by
  obtain ⟨F, hF, hd, hhit⟩ := PackingCover.exists_maximal_disjoint_family s U hne
  have hcard : (F.biUnion U).card ≤ F.card * L := by
    calc
      _ ≤ ∑ i ∈ F, (U i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ F, L := Finset.sum_le_sum fun i hi => hsize i (hF hi)
      _ = _ := by simp
  have hmassle := PackingCover.mass_le_vertex_load s U (F.biUnion U) a b ha hhit
    (fun v _ => hload v)
  refine ⟨F, hF, hd, hmass.trans_le (hmassle.trans ?_)⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb

theorem goodTwoLink_zero_or_one {ι : Type*} (G : FiniteMultiGraph)
    (U : ι → Finset G.Vertex) (p : G.Vertex) (i j : ι) :
    goodTwoLink G U p i j = 0 ∨ goodTwoLink G U p i j = 1 := by
  unfold goodTwoLink
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem twoLink_eq_one_of_good {ι : Type*} (G : FiniteMultiGraph)
    (U : ι → Finset G.Vertex) (p : G.Vertex) (i j : ι)
    (hgood : goodTwoLink G U p i j = 1) : twoLink G U i j = 1 := by
  unfold goodTwoLink at hgood
  split_ifs at hgood with h
  · exact h.1
  · norm_num at hgood

/-- A heavy row of actual good pairs gives a large disjoint separator
family with one common attachment. All supports retain their original labels. -/
theorem exists_separatorFamily_of_good_row {ι : Type*}
    (G : FiniteMultiGraph) (U : ι → Finset G.Vertex) (p : G.Vertex)
    (s : Finset ι) (i : ι) (a : ι → ℝ) (L : ℕ) (b : ℝ)
    (hconn : ∀ j ∈ s, (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected)
    (hp : ∀ j ∈ s, p ∉ U j) (hlen : ∀ j ∈ s, (U j).card ≤ L)
    (hcut : (G.cutEdges (U i)).card ≤ L) (hL : 0 < L)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hb : 0 ≤ b)
    (hload : ∀ v, (∑ j ∈ s, if v ∈ U j then a j else 0) ≤ b)
    (hrow : 8 < ∑ j ∈ s, goodTwoLink G U p i j * a j) :
    ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ s,
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      (8 : ℝ) / L < (F.card : ℝ) * L * b := by
  classical
  let T := s.filter fun j => goodTwoLink G U p i j = 1
  have hTs : T ⊆ s := Finset.filter_subset _ _
  have hTgood : ∀ j ∈ T, goodTwoLink G U p i j = 1 :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hmass : (8 : ℝ) < ∑ j ∈ T, a j := by
    have heq : (∑ j ∈ T, a j) = ∑ j ∈ s, goodTwoLink G U p i j * a j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      rcases goodTwoLink_zero_or_one G U p i j with hz | hone
      · simp [hz]
      · simp [hone]
    rw [heq]
    exact hrow
  let H := deletedGraph G.toSimpleGraph (↑(U i))
  let R : G.Vertex → ι → Prop := fun u j => H.Reachable u p ∧ Separates H (↑(U j)) u p
  have hcover : ∀ j ∈ T, ∃ u ∈ cutOutsideVertices G (U i), R u j := by
    intro j hj
    exact goodTwoLink_deleted_separator G U p i j (hconn j (hTs hj))
      (hp j (hTs hj)) (hTgood j hj)
  obtain ⟨u, hu, hheavy⟩ := exists_heavy_cover_row T (cutOutsideVertices G (U i)) R a L 8
    (fun j hj => ha j (hTs hj)) hL (by norm_num)
    ((cutOutsideVertices_card_le G (U i)).trans hcut) hcover hmass
  let Q := T.filter (R u)
  have hQT : Q ⊆ T := Finset.filter_subset _ _
  have hQs : Q ⊆ s := hQT.trans hTs
  have hQR : ∀ j ∈ Q, R u j := fun j hj => (Finset.mem_filter.mp hj).2
  have hheavyQ : (8 : ℝ) / L < ∑ j ∈ Q, a j := by
    convert hheavy using 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : R u j
    · simp only [R] at hh ⊢
      simp [hh]
    · simp only [R] at hh ⊢
      simp [hh]
  have hloadQ : ∀ v, (∑ j ∈ Q, if v ∈ U j then a j else 0) ≤ b := by
    intro v
    apply le_trans ?_ (hload v)
    apply Finset.sum_le_sum_of_subset_of_nonneg hQs
    intro j hj _
    split_ifs <;> simp [ha j hj]
  have hQne : Q.Nonempty := by
    by_cases hne : Q.Nonempty
    · exact hne
    · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : (8 : ℝ) / L < 0 := by simpa [he] using hheavyQ
      have hnonneg : (0 : ℝ) ≤ 8 / L := by positivity
      linarith
  obtain ⟨j₀, hj₀⟩ := hQne
  obtain ⟨F, hF, hd, hlarge⟩ := exists_large_disjoint_family Q U a L b (8 / L)
    (fun j hj => by obtain ⟨v⟩ := (hconn j (hQs hj)).nonempty; exact ⟨v.1, v.2⟩)
    (fun j hj => hlen j (hQs hj)) (fun j hj => ha j (hQs hj)) hb hloadQ hheavyQ
  refine ⟨u, hu, F, hF.trans hQs, ⟨(hQR j₀ hj₀).1, ?_, ?_, ?_⟩, hlarge⟩
  · intro j hj
    exact (hQR j (hF hj)).2
  · intro j hj
    have hg := hTgood j (hQT (hF hj))
    have hdisj := ((twoLink_eq_one_iff G U i j).mp (twoLink_eq_one_of_good G U p i j hg)).2.1
    exact connectedSet_deleted G.toSimpleGraph (↑(U i)) (↑(U j))
      (isConnectedSet_of_induce (hconn j (hQs (hF hj)))) (by exact_mod_cast hdisj.symm)
  · intro j hj k hk hjk
    exact_mod_cast hd j hj k hk hjk

/-- The finite chain step from the actual forest event. The second moment,
orientation, joined-row loss, common attachment, and disjoint packing are all
proved from the graph. The quantitative cycle supply and link/load envelope
remain explicit hypotheses. -/
theorem exists_separatorFamily_of_forest {ι : Type*}
    (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)
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
    ∃ i ∈ s, ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ s,
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      (8 : ℝ) / L < (F.card : ℝ) * L * b := by
  obtain ⟨i, hi, hrow⟩ := exists_goodTwoLink_row_gt_eight_of_forest G U p s seed L M b E
    hG hconn hp htwo hdegree hinj hlen hM hb hload hlinks hE hforest hjoined hμ hη
  have hambient : ∀ j ∈ s,
      (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected := by
    intro j hj
    apply (hconn j hj).mono
    intro u v huv
    rcases huv with ⟨hne, e, _, hend⟩
    exact ⟨hne, e, hend⟩
  have hcut : (G.cutEdges (U i)).card ≤ L :=
    (G.cutEdges_card_le_of_two_regular (U i) (seed i).1.1
      (htwo i hi) (seed i).2 (hdegree i hi)).trans (hlen i hi)
  have hL : 0 < L := by
    obtain ⟨v⟩ := (hconn i hi).nonempty
    exact (Finset.card_pos.mpr ⟨v.1, v.2⟩).trans_le (hlen i hi)
  obtain ⟨u, hu, F, hF, hfamily, hlarge⟩ := exists_separatorFamily_of_good_row
    G U p s i (weight G U seed) L b hambient hp hlen hcut hL
    (fun j _ => by unfold weight; positivity) hb hload hrow
  exact ⟨i, hi, u, hu, F, hF, hfamily, hlarge⟩

end Erdos1016.ExactMaximumSupport.LargeGirth

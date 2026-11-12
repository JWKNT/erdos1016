import Erdos1016.ExactMaximumSupport.LargeGirth.BlockGeometry

set_option autoImplicit false

/-!
# Separator chains for arbitrary disjoint connected regions

The two-link separator construction already works for arbitrary connected
vertex regions. Disjointness allows retaining every partner with a common
attachment, avoiding the cycle-size and vertex-load losses of the old selector.
The blocks are literal original vertex sets and need not be connected.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.DisjointRegionChain
open LargeGirth PolynomialBound.Separation PolynomialBound.ParallelLinks
open PolynomialBound.TwoLinkMoment FiniteMultiGraph

local instance regionChainDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A good row of disjoint connected regions gives a large actual separator
family. There is no upper bound on the size of a region. -/
theorem exists_separatorFamily_of_good_row {ι : Type*}
    (G : FiniteMultiGraph) (U : ι → Finset G.Vertex) (p : G.Vertex)
    (s : Finset ι) (i : ι) (a : ι → ℝ) (d : ℕ) (γ : ℝ)
    (hconn : ∀ j ∈ s, (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected)
    (hp : ∀ j ∈ s, p ∉ U j)
    (hdisj : ∀ j ∈ s, ∀ k ∈ s, j≠k → Disjoint (U j) (U k))
    (hcut : (G.cutEdges (U i)).card ≤ d) (hd : 0<d)
    (ha : ∀ j ∈ s, 0≤a j) (ha1 : ∀ j ∈ s, a j≤1) (hγ : 0≤γ)
    (hrow : γ < ∑ j ∈ s, goodTwoLink G U p i j * a j) :
    ∃ u ∈ cutOutsideVertices G (U i), ∃ F ⊆ s,
      SeparatorFamily (deletedGraph G.toSimpleGraph (↑(U i))) u p F (fun j => ↑(U j)) ∧
      γ / d < (F.card : ℝ) := by
  classical
  let T := s.filter fun j => goodTwoLink G U p i j=1
  have hTs : T⊆s := Finset.filter_subset _ _
  have hTgood : ∀ j ∈ T, goodTwoLink G U p i j=1 :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hmass : γ < ∑ j ∈ T, a j := by
    have heq : (∑ j ∈ T, a j)=∑ j ∈ s, goodTwoLink G U p i j*a j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      rcases goodTwoLink_zero_or_one G U p i j with hz | hone
      · simp [hz]
      · simp [hone]
    rwa [heq]
  let H := deletedGraph G.toSimpleGraph (↑(U i))
  let R : G.Vertex → ι → Prop := fun u j => H.Reachable u p ∧ Separates H (↑(U j)) u p
  have hcover : ∀ j ∈ T, ∃ u ∈ cutOutsideVertices G (U i), R u j := by
    intro j hj
    exact goodTwoLink_deleted_separator G U p i j (hconn j (hTs hj))
      (hp j (hTs hj)) (hTgood j hj)
  obtain ⟨u,hu,hheavy⟩ := exists_heavy_cover_row T (cutOutsideVertices G (U i)) R a d γ
    (fun j hj => ha j (hTs hj)) hd hγ
    ((cutOutsideVertices_card_le G (U i)).trans hcut) hcover hmass
  let F := T.filter (R u)
  have hFT : F⊆T := Finset.filter_subset _ _
  have hFs : F⊆s := hFT.trans hTs
  have hFR : ∀ j ∈ F, R u j := fun j hj => (Finset.mem_filter.mp hj).2
  have hheavyF : γ/d < ∑ j ∈ F,a j := by
    convert hheavy using 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hh : R u j
    · simp only [R] at hh ⊢
      simp [hh]
    · simp only [R] at hh ⊢
      simp [hh]
  have hFne : F.Nonempty := by
    by_cases hn : F.Nonempty
    · exact hn
    · have hzero : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hh : γ/d<0 := by simpa [hzero] using hheavyF
      have hnonneg : (0:ℝ)≤γ/d := by positivity
      linarith
  obtain ⟨j₀,hj₀⟩ := hFne
  refine ⟨u,hu,F,hFs,⟨(hFR j₀ hj₀).1,?_,?_,?_⟩,?_⟩
  · intro j hj
    exact (hFR j hj).2
  · intro j hj
    have hg := hTgood j (hFT hj)
    have hpair := ((twoLink_eq_one_iff G U i j).mp
      (twoLink_eq_one_of_good G U p i j hg)).2.1
    exact connectedSet_deleted G.toSimpleGraph (↑(U i)) (↑(U j))
      (isConnectedSet_of_induce (hconn j (hFs hj))) (by exact_mod_cast hpair.symm)
  · intro j hj k hk hjk
    exact_mod_cast hdisj j (hFs hj) k (hFs hk) hjk
  · apply hheavyF.trans_le
    calc
      (∑ j ∈ F,a j) ≤ ∑ _j ∈ F,(1:ℝ) :=
        Finset.sum_le_sum fun j hj => ha1 j (hFs hj)
      _ = (F.card:ℝ) := by simp

/-- Arbitrary disjoint connected separators give large clean blocks. Boundary
control uses the actual region cuts; no cycle support or upper size bound is needed. -/
theorem exists_clean_chain_blocks {ι : Type*} [DecidableEq ι]
    (G : FiniteMultiGraph) (A P S : Finset G.Vertex) (u p : G.Vertex)
    (F : Finset ι) (U : ι → Finset G.Vertex) (q m ℓ d : ℕ)
    (hfamily : SeparatorFamily (deletedGraph G.toSimpleGraph (↑A)) u p F (fun i => ↑(U i)))
    (hu : u ∉ A) (hm : m*q < F.card)
    (hP : IsConnectedSet G.toSimpleGraph (↑P)) (hp : p ∈ P)
    (hPA : Disjoint P A) (hPU : ∀ i ∈ F, Disjoint P (U i))
    (hsize : ∀ i ∈ F, ℓ ≤ (U i).card)
    (hcut : ∀ i ∈ F, (G.cutEdges (U i)).card ≤ d) :
    ∃ (X : Fin m → Finset G.Vertex) (J : Finset (Fin m)),
      m ≤ J.card + (G.cutEdges A).card + S.card ∧
      (∀ l l', l ≠ l' → Disjoint (X l) (X l')) ∧
      (∀ l ∈ J, (q-1)*ℓ ≤ (X l).card ∧ (G.cutEdges (X l)).card ≤ 2*d ∧
        Disjoint (X l) (P ∪ S)) := by
  classical
  obtain ⟨lo, hi, inner, hends, hdisj, hin⟩ := hfamily.exists_blocks q m hm
  let X : Fin m → Finset G.Vertex := fun l => blockVertices G A (U (lo l)) (U (hi l)) u
  let bad := cutOutsideVertices G A ∪ S
  let J := Finset.univ.filter fun l : Fin m => Disjoint (X l) bad
  have hXdisj : ∀ l l', l ≠ l' → Disjoint (X l) (X l') := by
    intro l l' hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact Set.disjoint_left.mp (hdisj l l' hne)
      ((mem_blockVertices G A (U (lo l)) (U (hi l)) u v).mp hv)
      ((mem_blockVertices G A (U (lo l')) (U (hi l')) u v).mp hv')
  refine ⟨X, J, ?_, hXdisj, ?_⟩
  · have hh := clean_blocks_card_ge (Finset.univ : Finset (Fin m)) X bad
      (fun i _ j _ hij => hXdisj i j hij)
    have hb := Finset.card_union_le (cutOutsideVertices G A) S
    have hc := cutOutsideVertices_card_le G A
    have hh' : m ≤ J.card + bad.card := by simpa only [Finset.card_univ, Fintype.card_fin] using hh
    dsimp only [bad] at hh'
    omega
  · intro l hl
    have hgood : Disjoint (X l) bad := (Finset.mem_filter.mp hl).2
    have hclean : ∀ x ∈ X l, ∀ a ∈ A, ¬ G.toSimpleGraph.Adj x a := by
      intro x hx a ha hadj
      have hxA : x ∉ A := block_deleted_not_mem G.toSimpleGraph (↑A)
        (↑(U (lo l))) (↑(U (hi l))) hu ((mem_blockVertices _ _ _ _ _ _).mp hx)
      have hout := mem_cutOutsideVertices_of_adj G A ha hxA hadj.symm
      exact Finset.disjoint_left.mp hgood hx (Finset.mem_union_left S hout)
    have hbound : (G.cutEdges (X l)).card ≤ 2*d := by
      have hc := Finset.card_le_card
        (clean_block_cut_subset G A (U (lo l)) (U (hi l)) u hu hclean)
      have hh := Finset.card_union_le (G.cutEdges (U (lo l))) (G.cutEdges (U (hi l)))
      have hl := hcut _ (hends l).1
      have hr := hcut _ (hends l).2
      dsimp only [X]
      omega
    refine ⟨?_, hbound, ?_⟩
    · have hh := card_ge_disjoint_supports (inner l) U (X l) ℓ
        (fun i hi j hj hij => by exact_mod_cast hfamily.disj i ((hin l).1 hi) j ((hin l).1 hj) hij)
        (fun i hi v hv => (mem_blockVertices _ _ _ _ _ _).mpr ((hin l).2.2 i hi hv))
        (fun i hi => hsize i ((hin l).1 hi))
      rw [(hin l).2.1] at hh
      exact hh
    · have hmarker := block_deleted_disjoint_marker G.toSimpleGraph (↑A)
        (↑(U (lo l))) (↑(U (hi l))) (↑P) (hfamily.sep _ (hends l).2) hP hp
        (by exact_mod_cast hPA) (by exact_mod_cast hPU _ (hends l).2)
      apply Finset.disjoint_left.mpr
      intro v hv hvbad
      rcases Finset.mem_union.mp hvbad with hvP | hvS
      · exact Set.disjoint_left.mp hmarker ((mem_blockVertices _ _ _ _ _ _).mp hv) hvP
      · exact Finset.disjoint_left.mp hgood hv (Finset.mem_union_right _ hvS)


end Erdos1016.ExactMaximumSupport.Shortening.DisjointRegionChain

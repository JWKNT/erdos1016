import Erdos1016.ExactMaximum.GirthFive.LevelRegions
import Erdos1016.ExactMaximum.GirthFive.ManyRegions
import Erdos1016.Probability.Avoidance.PoleMarker

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Pieces at girth five

`exists_affine_bound_girth_five`: for every `k` there is `F` with this property. Let `M` be a
connected multigraph with all degrees at most three, without cycles of length less than five,
with cubic deficit at most `k` and cycle rank at least `F`. Then every boundary demand that is
supported on the vertices of degree less than three has forest proportion at most `3/5`.

Proof. Suppose that the proportion is more than `3/5`. By
`PoleMarker.exists_supported_demand_layer_bound` every distance level from a vertex `o` has at
most `W` vertices, where `W` depends on `k` only. So `M` has many levels. Take windows of `h`
consecutive levels. At most `k` windows have a vertex of degree less than three. For every
other window, `window_not_rigid` gives a word in every parity class of its level region that
is not a forest. So the level region has forest proportion at most `1 - 2^(-2hW)` in every
parity class. The regions of `2^(2hW)` windows are pairwise disjoint, and the product law
`affine_forest_density_le_prod` gives the proportion `(1 - 1/m)^m ≤ 1/2` with `m = 2^(2hW)`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph FiniteMultiGraph Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.ExactMaximumSupport.LargeGirth Erdos1016.PolynomialBound.Separation
open Erdos1016.Probability.PoleMarker

local instance piecesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Numerical and counting facts -/

theorem pow_one_sub_inv_le_half (m : ℕ) (hm : 0 < m) : (1 - 1 / (m : ℝ)) ^ m ≤ 1 / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have ht1 : 1 / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm']
    exact_mod_cast hm
  have hmt : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  have h1 : (2 : ℝ) ≤ (1 + 1 / (m : ℝ)) ^ m := by
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (m : ℝ) by linarith) m
    linarith
  have h2 : (1 - 1 / (m : ℝ)) ^ m * (1 + 1 / (m : ℝ)) ^ m ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  have h3 : (0 : ℝ) ≤ (1 - 1 / (m : ℝ)) ^ m := pow_nonneg (by linarith) m
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

/-- A property that fails at one point has density at most `1 - 1/N`. -/
theorem density_le_of_not {X : Type*} [Fintype X] (P : X → Prop) (z₀ : X) (h : ¬ P z₀) :
    Finite.density P ≤ 1 - 1 / (Fintype.card X : ℝ) := by
  have hz : Finite.count (fun x : X => x = z₀) = 1 := by simp [Finite.count]
  have hs : Finite.count P + Finite.count (fun x : X => x = z₀) ≤ Fintype.card X := by
    rw [Finite.count, Finite.count, ← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _x : X, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x = z₀
        · subst hx
          simp [h]
        · by_cases hp : P x <;> simp [hx, hp]
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨z₀⟩
  unfold Finite.density
  rw [div_le_iff₀ hn, sub_mul, one_mul, one_div, inv_mul_cancel₀ hn.ne']
  linarith

variable (N : FiniteMultiGraph)

/-- The restriction to the internal edges of a region has the same boundary at a vertex whose
edges are all internal. -/
theorem boundary_restrict_of_internal (U : Finset N.Vertex) (y : N.EdgeWord) {v : N.Vertex}
    (hall : ∀ e, (N.src e = v ∨ N.dst e = v) → e ∈ N.internalEdges U) :
    N.boundary (N.restrictEdges (N.internalEdges U) y) v = N.boundary y v := by
  show (∑ e, ((if N.src e = v then N.restrictEdges (N.internalEdges U) y e else 0) +
      (if N.dst e = v then N.restrictEdges (N.internalEdges U) y e else 0))) =
    ∑ e, ((if N.src e = v then y e else 0) + (if N.dst e = v then y e else 0))
  apply Finset.sum_congr rfl
  intro e _
  by_cases h1 : N.src e = v
  · have hr : N.restrictEdges (N.internalEdges U) y e = y e := by
      simp only [restrictEdges, if_pos (hall e (Or.inl h1))]
    rw [hr]
  · by_cases h2 : N.dst e = v
    · have hr : N.restrictEdges (N.internalEdges U) y e = y e := by
        simp only [restrictEdges, if_pos (hall e (Or.inr h2))]
      rw [hr]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

/-- The even words on the internal edges of a region: at most `2^(2|U|)`. -/
theorem card_internalCycleSpace_le (hmax : ∀ v, N.degree v ≤ 3) (U : Finset N.Vertex) :
    Fintype.card (N.internalCycleSpace U) ≤ 2 ^ (2 * U.card) := by
  have hcard : Fintype.card (N.internalCycleSpace U) =
      2 ^ Module.finrank F₂ (N.internalCycleSpace U) := by
    have h := Module.card_eq_pow_finrank (K := F₂) (V := N.internalCycleSpace U)
    simpa [F₂] using h
  have hrank : Module.finrank F₂ (N.internalCycleSpace U) =
      (PieceCore.Induced.graph N U).cycleRank :=
    ((PoleProduct.cycleEquiv N U).finrank_eq).symm
  have h1 := (PieceCore.Induced.graph N U).cycleRank_add_boundaryRank
  rw [PieceCore.Induced.edgeCount] at h1
  have h2 := N.sum_region_degree U
  have h3 : (∑ v ∈ U, N.degree v) ≤ U.card * 3 := by
    have := Finset.sum_le_card_nsmul U (fun v => N.degree v) 3 (fun v _ => hmax v)
    simpa [smul_eq_mul] using this
  rw [hcard, hrank]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- The vertices of the window `g`, with `s + 1` levels from `g h + 1`, are cubic. -/
def GoodWindow (o : N.Vertex) (h s g : ℕ) : Prop :=
  ∀ v, g * h + 1 ≤ N.toSimpleGraph.dist o v → N.toSimpleGraph.dist o v ≤ g * h + 1 + s →
    N.degree v = 3

/-- All windows are good, with at most `k` exceptions. -/
theorem card_good_windows (o : N.Vertex) (h s G k : ℕ) (hs : s < h)
    (hk : (Finset.univ.filter (fun v => N.degree v ≠ 3)).card ≤ k) :
    G ≤ Fintype.card {g : Fin G // GoodWindow N o h s g} + k := by
  rw [Fintype.card_subtype]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin G))) (fun g : Fin G => GoodWindow N o h s g)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hbad : (Finset.univ.filter (fun g : Fin G => ¬ GoodWindow N o h s g)).card ≤ k := by
    refine le_trans ?_ hk
    have hsub : Finset.univ.filter (fun g : Fin G => ¬ GoodWindow N o h s g) ⊆
        (Finset.univ.filter (fun v => N.degree v ≠ 3)).biUnion
          (fun v => Finset.univ.filter (fun g : Fin G =>
            (g : ℕ) * h + 1 ≤ N.toSimpleGraph.dist o v ∧
              N.toSimpleGraph.dist o v ≤ (g : ℕ) * h + 1 + s)) := by
      intro g hg
      have hg' : ¬ GoodWindow N o h s g := (Finset.mem_filter.mp hg).2
      unfold GoodWindow at hg'
      push_neg at hg'
      obtain ⟨v, hv1, hv2, hv3⟩ := hg'
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv3⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv1, hv2⟩⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    have hone := Finset.card_biUnion_le_card_mul
      (Finset.univ.filter (fun v => N.degree v ≠ 3))
      (fun v => Finset.univ.filter (fun g : Fin G =>
        (g : ℕ) * h + 1 ≤ N.toSimpleGraph.dist o v ∧
          N.toSimpleGraph.dist o v ≤ (g : ℕ) * h + 1 + s)) 1 ?_
    · simpa using hone
    · intro v _
      apply Finset.card_le_one.mpr
      intro g hg g' hg'
      have h1 := (Finset.mem_filter.mp hg).2
      have h2 := (Finset.mem_filter.mp hg').2
      apply Fin.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := Nat.mul_le_mul_right h (show (g : ℕ) + 1 ≤ g' from hlt)
        have e1 : ((g : ℕ) + 1) * h = (g : ℕ) * h + h := by ring
        omega
      · have := Nat.mul_le_mul_right h (show (g' : ℕ) + 1 ≤ g from hlt)
        have e1 : ((g' : ℕ) + 1) * h = (g' : ℕ) * h + h := by ring
        omega
  omega

/-- **Pieces at girth five.** -/
theorem exists_affine_bound_girth_five (k : ℕ) :
    ∃ F : ℕ, ∀ (M : FiniteMultiGraph), M.toSimpleGraph.Connected →
      (∀ v, M.degree v ≤ 3) → ¬ M.HasCycleShorterThan 5 →
      F ≤ M.cycleRank → M.cubicDeficit ≤ k →
      ∀ b : M.Demand, (∀ v, M.degree v = 3 → b v = 0) →
        affineForestProbability M b ≤ 3 / 5 := by
  obtain ⟨B, hB⟩ := exists_supported_demand_layer_bound
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ, W = B * (k + 2) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℕ, τ = 400 * (2 * W + 2) + 1 := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = 2 * W + 1 := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = n * τ + 1 := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, h = s + 1 := ⟨_, rfl⟩
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : ℕ, m₀ = 2 ^ (2 * (h * W)) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ, G = m₀ + k := ⟨_, rfl⟩
  refine ⟨W * (G * h + 1) + 1, ?_⟩
  intro M hconn hmax h5 hrank hdef b hb
  apply le_of_not_gt
  intro hq
  obtain ⟨o⟩ := hconn.nonempty
  -- few vertices of degree less than three
  have hdefcard : (Finset.univ.filter (fun v => M.degree v ≠ 3)).card ≤ k := by
    refine le_trans ?_ hdef
    unfold cubicDeficit
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : M.degree v ≠ 3
    · rw [if_pos hv]
      have := hmax v
      omega
    · rw [if_neg hv]
      exact Nat.zero_le _
  -- thin levels
  have hlayer : ∀ l : ℕ,
      (Finset.univ.filter (fun v => M.toSimpleGraph.dist o v = l)).card ≤ W := by
    intro l
    have hpc : (insert o (Finset.univ.filter (fun v => M.degree v ≠ 3))).card ≤ k + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hdefcard)
    have h1 := hB M (insert o (Finset.univ.filter (fun v => M.degree v ≠ 3))) o b hconn hmax
      (by
        intro v hv
        by_contra hne
        exact hv (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)))
      (Finset.mem_insert_self _ _)
      (by
        intro v hv
        apply hb v
        by_contra hne
        exact hv (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)))
      hq.le (l : ℤ)
    refine le_trans (Finset.card_le_card ?_) (h1.trans ?_)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, by rw [hv.2]⟩
    · rw [hWdef]
      exact (Nat.mul_le_mul_left B (Nat.pow_le_pow_left (by omega) 2)).trans (Nat.le_succ _)
  -- a longest shortest walk from `o`
  obtain ⟨t, _, ht⟩ := Finset.exists_max_image Finset.univ
    (fun v => M.toSimpleGraph.dist o v) ⟨o, Finset.mem_univ o⟩
  obtain ⟨A, hA⟩ := hconn.exists_walk_length_eq_dist o t
  have hshort : ∀ q : M.toSimpleGraph.Walk o t, A.length ≤ q.length := by
    intro q
    rw [hA]
    exact M.toSimpleGraph.dist_le q
  -- the walk is long
  have hWpos : 0 < W := by omega
  have hlong : G * h ≤ A.length := by
    have hV : M.vertexCount ≤ (A.length + 1) * W := by
      have hsub : (Finset.univ : Finset M.Vertex) ⊆ (Finset.range (A.length + 1)).biUnion
          (fun l => Finset.univ.filter (fun v => M.toSimpleGraph.dist o v = l)) := by
        intro v _
        have hv := ht v (Finset.mem_univ v)
        exact Finset.mem_biUnion.mpr ⟨M.toSimpleGraph.dist o v,
          Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_biUnion_le_card_mul (Finset.range (A.length + 1))
        (fun l => Finset.univ.filter (fun v => M.toSimpleGraph.dist o v = l)) W
        (fun l _ => hlayer l)
      rw [Finset.card_range] at h2
      rw [Finset.card_univ, Fintype.card_fin] at h1
      exact h1.trans h2
    have horder := M.order_add_two_eq_twice_rank_add_deficit hconn hmax
    have hmul : W * (G * h + 1) ≤ W * (A.length + 1) := by
      have e1 : (A.length + 1) * W = W * (A.length + 1) := Nat.mul_comm _ _
      omega
    have := Nat.le_of_mul_le_mul_left hmul hWpos
    omega
  -- the affine law as a law on the even words
  have hfiber : Nonempty (Parity.Fiber M.boundary b) := by
    by_contra hemp
    haveI : IsEmpty (Parity.Fiber M.boundary b) := not_nonempty_iff.mp hemp
    have h0 : affineForestProbability M b = 0 := by
      simp [affineForestProbability, Finite.density]
    rw [h0] at hq
    norm_num at hq
  obtain ⟨f⟩ := hfiber
  have he : affineForestProbability M b =
      Finite.density (fun z : M.CycleSpace => M.IsForestWord (z.1 + f.1)) :=
    (Finite.density_equiv (Parity.fiberEquivKernel M.boundary f).symm (fun _ => Iff.rfl)).symm
  -- the regions of the good windows
  have hsh : s < h := by omega
  have hgood := card_good_windows M o h s G k hsh hdefcard
  have hm₀pos : 0 < m₀ := by
    rw [hm₀def]
    positivity
  have hwin : ∀ g : Fin G, (g : ℕ) * h + 1 + n * τ + 1 ≤ A.length := by
    intro g
    have := Nat.mul_le_mul_right h (show (g : ℕ) + 1 ≤ G from g.2)
    have e1 : ((g : ℕ) + 1) * h = (g : ℕ) * h + h := by ring
    omega
  let U : {g : Fin G // GoodWindow M o h s g} → Finset M.Vertex := fun g =>
    levelRegion M.toSimpleGraph o ((g.1 : ℕ) * h + 1) ((g.1 : ℕ) * h + 1 + n * τ + 1)
      (A.getVert ((g.1 : ℕ) * h + 1))
  have hUdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have h1 := levelRegion_level M.toSimpleGraph o hvi
    have h2 := levelRegion_level M.toSimpleGraph o hvj
    have hne : (i.1 : ℕ) ≠ j.1 := fun h' => hij (Subtype.ext (Fin.ext h'))
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := Nat.mul_le_mul_right h (show (i.1 : ℕ) + 1 ≤ j.1 from hlt)
      have e1 : ((i.1 : ℕ) + 1) * h = (i.1 : ℕ) * h + h := by ring
      omega
    · have := Nat.mul_le_mul_right h (show (j.1 : ℕ) + 1 ≤ i.1 from hlt)
      have e1 : ((j.1 : ℕ) + 1) * h = (j.1 : ℕ) * h + h := by ring
      omega
  -- every parity class of a region has a word that is not a forest
  have hregion : ∀ (i : {g : Fin G // GoodWindow M o h s g}) (x : M.CycleSpace),
      Finite.density (fun z : M.internalCycleSpace (U i) =>
        M.IsForestWord (M.restrictEdges (M.internalEdges (U i)) (x.1 + z.1.1 + f.1))) ≤
        1 - 1 / (m₀ : ℝ) := by
    intro i x
    have hgi : GoodWindow M o h s i.1 := i.2
    have hcub : ∀ v, (i.1 : ℕ) * h + 1 ≤ M.toSimpleGraph.dist o v →
        M.toSimpleGraph.dist o v ≤ (i.1 : ℕ) * h + 1 + n * τ + 1 → M.degree v = 3 := by
      intro v hv1 hv2
      exact hgi v hv1 (by omega)
    have hwU : ∀ e, M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1) e ≠ 0 →
        e ∈ M.internalEdges (U i) := by
      intro e he
      by_contra hne
      apply he
      simp only [restrictEdges, if_neg hne]
    have hbw : ∀ v, (i.1 : ℕ) * h + 1 < M.toSimpleGraph.dist o v →
        M.toSimpleGraph.dist o v < (i.1 : ℕ) * h + 1 + n * τ + 1 →
        M.boundary (M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1)) v = 0 := by
      intro v hv1 hv2
      by_cases hvU : v ∈ U i
      · have hall : ∀ e, (M.src e = v ∨ M.dst e = v) → e ∈ M.internalEdges (U i) := by
          intro e he
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · by_cases h1 : M.src e = v
            · rw [h1]
              exact hvU
            · have h2 : M.dst e = v := he.resolve_left h1
              have hadj : M.toSimpleGraph.Adj v (M.src e) :=
                ⟨fun h' => h1 h'.symm, e, Or.inr ⟨rfl, h2⟩⟩
              exact levelRegion_inner M.toSimpleGraph o hconn hvU hv1 hv2 hadj
          · by_cases h2 : M.dst e = v
            · rw [h2]
              exact hvU
            · have h1 : M.src e = v := he.resolve_right h2
              have hadj : M.toSimpleGraph.Adj v (M.dst e) :=
                ⟨fun h' => h2 h'.symm, e, Or.inl ⟨h1, rfl⟩⟩
              exact levelRegion_inner M.toSimpleGraph o hconn hvU hv1 hv2 hadj
        rw [boundary_restrict_of_internal M (U i) _ hall, map_add]
        have hx0 : M.boundary x.1 = 0 := LinearMap.mem_ker.mp x.2
        have hfb : M.boundary f.1 = b := f.2
        rw [hx0, hfb]
        show (0 : F₂) + b v = 0
        rw [zero_add]
        exact hb v (hcub v (by omega) (by omega))
      · exact boundary_eq_zero_of_not_mem M (U i) _ hwU hvU
    obtain ⟨z₀, hz₀⟩ := window_not_rigid M hconn h5 hmax A hshort W τ n ((i.1 : ℕ) * h + 1)
      hlayer (by omega) (by omega) (hwin i.1) hcub
      (M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1)) hwU hbw
    have hword : ∀ z : M.internalCycleSpace (U i),
        M.restrictEdges (M.internalEdges (U i)) (x.1 + z.1.1 + f.1) =
          M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1) + z.1.1 := by
      intro z
      funext e
      by_cases hmem : e ∈ M.internalEdges (U i)
      · show M.restrictEdges (M.internalEdges (U i)) (x.1 + z.1.1 + f.1) e =
          M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1) e + z.1.1 e
        simp only [restrictEdges, if_pos hmem]
        show x.1 e + z.1.1 e + f.1 e = x.1 e + f.1 e + z.1.1 e
        exact add_right_comm _ _ _
      · show M.restrictEdges (M.internalEdges (U i)) (x.1 + z.1.1 + f.1) e =
          M.restrictEdges (M.internalEdges (U i)) (x.1 + f.1) e + z.1.1 e
        simp only [restrictEdges, if_neg hmem]
        rw [z.2 e hmem, add_zero]
    have hfail : ¬ M.IsForestWord
        (M.restrictEdges (M.internalEdges (U i)) (x.1 + z₀.1.1 + f.1)) := by
      rw [hword z₀]
      exact hz₀
    have hdens := density_le_of_not (fun z : M.internalCycleSpace (U i) =>
      M.IsForestWord (M.restrictEdges (M.internalEdges (U i)) (x.1 + z.1.1 + f.1))) z₀ hfail
    refine hdens.trans ?_
    have hUcard : (U i).card ≤ h * W := by
      have hc := levelRegion_card_le M.toSimpleGraph o W hlayer ((i.1 : ℕ) * h + 1)
        ((i.1 : ℕ) * h + 1 + n * τ + 1) (A.getVert ((i.1 : ℕ) * h + 1))
      have e1 : (i.1 : ℕ) * h + 1 + n * τ + 1 + 1 - ((i.1 : ℕ) * h + 1) = h := by omega
      rw [e1] at hc
      exact hc
    have hcard : Fintype.card (M.internalCycleSpace (U i)) ≤ m₀ := by
      rw [hm₀def]
      exact (card_internalCycleSpace_le M hmax (U i)).trans
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 2 hUcard))
    have hcpos : (0 : ℝ) < Fintype.card (M.internalCycleSpace (U i)) := by
      exact_mod_cast Fintype.card_pos
    have hcr : (Fintype.card (M.internalCycleSpace (U i)) : ℝ) ≤ (m₀ : ℝ) := by
      exact_mod_cast hcard
    have := one_div_le_one_div_of_le hcpos hcr
    linarith
  -- the product
  have hm₀r : (0 : ℝ) < m₀ := by exact_mod_cast hm₀pos
  have ha0 : (0 : ℝ) ≤ 1 - 1 / (m₀ : ℝ) := by
    have h1 : 1 / (m₀ : ℝ) ≤ 1 := by
      rw [div_le_one hm₀r]
      exact_mod_cast hm₀pos
    linarith
  have ha1 : 1 - 1 / (m₀ : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (m₀ : ℝ) := by positivity
    linarith
  have hprod := affine_forest_density_le_prod M f.1 U hUdisj (fun _ => 1 - 1 / (m₀ : ℝ))
    (fun _ => ha0) hregion
  rw [Finset.prod_const, Finset.card_univ] at hprod
  have hcardι : m₀ ≤ Fintype.card {g : Fin G // GoodWindow M o h s g} := by omega
  have hpow : (1 - 1 / (m₀ : ℝ)) ^ Fintype.card {g : Fin G // GoodWindow M o h s g} ≤
      (1 - 1 / (m₀ : ℝ)) ^ m₀ := pow_le_pow_of_le_one ha0 ha1 hcardι
  have hhalf := pow_one_sub_inv_le_half m₀ hm₀pos
  rw [he] at hq
  linarith

end Erdos1016.ExactMaximum.GirthFive

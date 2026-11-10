import Erdos1016.CycleCount.TriangleFamily
import Erdos1016.Graph.ConnectedCover

set_option autoImplicit false

/-!
# Counting cycles through a chord extension

Let `G` be connected with cycle rank `r`, and let `t ≤ r`. Choose `t`
independent edges and close each of them to a triangle by adding chords. The
extended graph has rank at most `r + a`, where `a` is the number of chords.

A cycle of `G` through a chosen edge meets the triangle family. Its lift, and
each of its `2^a` translates by new triangles, has a forest outside the
family. Hence at most `p * 2^r` cycles pass through a chosen edge, where `p`
is the outside-forest probability of the extension. At most `2^(r - t)`
cycles avoid all chosen edges.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.CycleCount
open PhysicalGraph ShortProof

theorem mem_edgeSupport_iff (H : PhysicalGraph) (x : H.Word) (e : H.Edge) :
    e ∈ H.edgeSupport x ↔ x e ≠ 0 := by
  simp [PhysicalGraph.edgeSupport]

/-- The cycle-count inequality for a connected graph, from a uniform bound on
the outside-forest probability of triangle families in connected extensions. -/
theorem card_cycleWord_le (G : PhysicalGraph) (hG : G.IsConnected) (t : ℕ)
    (ht : t ≤ G.cycleRank) (ht1 : 1 ≤ t) (B : ℝ)
    (hB : ∀ (H : PhysicalGraph) (F : Finset H.CycleWord), H.IsConnected →
      G.cycleRank ≤ H.cycleRank → F.Nonempty → F.card ≤ t →
      (∀ T ∈ F, H.wordLength T.1 = 3) →
      outsideForestProbability H (witnessSupportEdges H F) ≤ B) :
    (Fintype.card G.CycleWord : ℝ) ≤
      B * 2 ^ G.cycleRank + 2 ^ (G.cycleRank - t) := by
  classical
  obtain ⟨D, hDcard, hDavoid, hDwit⟩ := exists_independent_edges G t ht
  obtain ⟨C, F, y, hFcard, hFne, hF3, hFD, hyF, hyval⟩ :=
    exists_triangle_family G D hDwit
  have hHconn : (addChords G C).IsConnected := addChords_connected G C hG
  have hrank1 : G.cycleRank ≤ (addChords G C).cycleRank := cycleRank_le_addChords G C
  have hrank2 : (addChords G C).cycleRank ≤ G.cycleRank + C.count :=
    cycleRank_addChords_le G C
  have hDne : D.Nonempty := by
    rw [← Finset.card_pos, hDcard]
    omega
  have hp := hB (addChords G C) F hHconn hrank1 (hFne hDne)
    (hFcard.trans (le_of_eq hDcard)) hF3
  have hp0 := (outsideForestProbability_bounds (addChords G C)
    (witnessSupportEdges (addChords G C) F)).1
  have hB0 : 0 ≤ B := hp0.trans hp
  -- The forest-bearing elements of the extended cycle space.
  have hS : outsideForestProbability (addChords G C)
        (witnessSupportEdges (addChords G C) F) * 2 ^ (addChords G C).cycleRank =
      ((Finset.univ.filter fun x : (addChords G C).CycleSpace =>
        IsOutsideForest (addChords G C) (witnessSupportEdges (addChords G C) F)
          ((addChords G C).outsideCycleProjection
            (witnessSupportEdges (addChords G C) F) x)).card : ℝ) := by
    unfold outsideForestProbability
    rw [div_mul_cancel₀ _ (by positivity)]
  -- New triangles as cycle-space elements, and the translation map.
  let yz : Fin C.count → (addChords G C).CycleSpace :=
    fun j => ⟨(y j).1, LinearMap.mem_ker.mpr (y j).2.2.1⟩
  let Φ : G.CycleWord × (Fin C.count → F₂) → (addChords G C).CycleSpace := fun q =>
    liftCycleSpace G C ⟨q.1.1, LinearMap.mem_ker.mpr q.1.2.2.1⟩ + ∑ j, q.2 j • yz j
  have hΦval : ∀ (q : G.CycleWord × (Fin C.count → F₂)) (e : (addChords G C).Edge),
      (Φ q).1 e = liftWord G C q.1.1 e + ∑ j, q.2 j * (y j).1 e := by
    intro q e
    simp only [Φ, yz, liftCycleSpace, Submodule.coe_add, Submodule.coe_sum,
      Submodule.coe_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hynew : ∀ i j, (y j).1 (newEdge G C i) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij]
      exact (f2_cases _).resolve_left ((hyval i j).2 hij)
    · rw [if_neg hij]
      by_contra hne
      exact hij ((hyval i j).1 hne)
  have hΦnew : ∀ (q : G.CycleWord × (Fin C.count → F₂)) (i : Fin C.count),
      (Φ q).1 (newEdge G C i) = q.2 i := by
    intro q i
    rw [hΦval, liftWord_new, zero_add]
    simp [hynew]
  let A : Finset G.CycleWord := Finset.univ.filter fun c => ∃ e ∈ D, c.1 e ≠ 0
  have hinj : A.card * 2 ^ C.count ≤
      (Finset.univ.filter fun x : (addChords G C).CycleSpace =>
        IsOutsideForest (addChords G C) (witnessSupportEdges (addChords G C) F)
          ((addChords G C).outsideCycleProjection
            (witnessSupportEdges (addChords G C) F) x)).card := by
    have hprod : (A ×ˢ (Finset.univ : Finset (Fin C.count → F₂))).card =
        A.card * 2 ^ C.count := by
      rw [Finset.card_product, Finset.card_univ]
      simp [F₂]
    rw [← hprod]
    apply Finset.card_le_card_of_injOn Φ
    · intro q hq
      have hqA := (Finset.mem_product.mp hq).1
      obtain ⟨e, heD, hce⟩ := (Finset.mem_filter.mp hqA).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hproj : (addChords G C).outsideCycleProjection
            (witnessSupportEdges (addChords G C) F) (Φ q) =
          (addChords G C).restrictOutsideWord
            (witnessSupportEdges (addChords G C) F) (liftCycleWord G C q.1).1 := by
        funext f
        rw [outsideCycleProjection_apply]
        show (Φ q).1 f.1 = liftWord G C q.1.1 f.1
        rw [hΦval]
        have hz : ∀ j, (y j).1 f.1 = 0 := by
          intro j
          by_contra hne
          apply f.2
          exact Finset.mem_biUnion.mpr
            ⟨y j, hyF j, (mem_edgeSupport_iff _ _ _).2 hne⟩
        simp [hz]
      rw [hproj]
      apply cycle_outside_isForest (addChords G C) _ (liftCycleWord G C q.1)
      obtain ⟨T, hTF, hTe⟩ := hFD e heD
      refine ⟨oldEdge G C e, Finset.mem_biUnion.mpr
        ⟨T, hTF, (mem_edgeSupport_iff _ _ _).2 hTe⟩, ?_⟩
      rw [liftCycleWord_old]
      exact hce
    · intro q _ q' _ h
      have h2 : q.2 = q'.2 := by
        funext i
        have h' := congrArg
          (fun x : (addChords G C).CycleSpace => x.1 (newEdge G C i)) h
        simpa only [hΦnew] using h'
      have h1 : q.1 = q'.1 := by
        apply Subtype.ext
        funext e
        have h' := congrArg
          (fun x : (addChords G C).CycleSpace => x.1 (oldEdge G C e)) h
        simp only [hΦval, liftWord_old] at h'
        rw [h2] at h'
        exact add_right_cancel h'
      exact Prod.ext h1 h2
  -- Cycles that avoid every chosen edge.
  have havoid : (Finset.univ.filter fun c : G.CycleWord => ¬ ∃ e ∈ D, c.1 e ≠ 0).card ≤
      (avoiding G D).card := by
    apply Finset.card_le_card_of_injOn
      (fun c : G.CycleWord => (⟨c.1, LinearMap.mem_ker.mpr c.2.2.1⟩ : G.CycleSpace))
    · intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      refine (mem_avoiding G D _).2 ?_
      intro e he
      by_contra hne
      exact hc' ⟨e, he, hne⟩
    · intro c _ c' _ h
      have h' : c.1 = c'.1 := congrArg (fun z : G.CycleSpace => z.1) h
      exact Subtype.ext h'
  have havoidcard : (avoiding G D).card = 2 ^ (G.cycleRank - t) := by
    have hpow : (2 : ℕ) ^ G.cycleRank = 2 ^ (G.cycleRank - t) * 2 ^ t := by
      rw [← pow_add, Nat.sub_add_cancel ht]
    rw [hpow] at hDavoid
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hDavoid
  have htotal : Fintype.card G.CycleWord =
      A.card + (Finset.univ.filter fun c : G.CycleWord => ¬ ∃ e ∈ D, c.1 e ≠ 0).card := by
    rw [← Finset.card_univ]
    exact (Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset G.CycleWord)) (fun c => ∃ e ∈ D, c.1 e ≠ 0)).symm
  -- Real arithmetic.
  have hpowa : (0 : ℝ) < 2 ^ C.count := by positivity
  have hA : (A.card : ℝ) ≤ B * 2 ^ G.cycleRank := by
    have h1 : (A.card : ℝ) * 2 ^ C.count ≤
        outsideForestProbability (addChords G C)
          (witnessSupportEdges (addChords G C) F) * 2 ^ (addChords G C).cycleRank := by
      rw [hS]
      exact_mod_cast hinj
    have h2 : outsideForestProbability (addChords G C)
          (witnessSupportEdges (addChords G C) F) * 2 ^ (addChords G C).cycleRank ≤
        B * 2 ^ (addChords G C).cycleRank :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    have h3 : (2 : ℝ) ^ (addChords G C).cycleRank ≤ 2 ^ (G.cycleRank + C.count) :=
      pow_le_pow_right₀ (by norm_num) hrank2
    have h4 : B * (2 : ℝ) ^ (addChords G C).cycleRank ≤
        B * 2 ^ (G.cycleRank + C.count) := mul_le_mul_of_nonneg_left h3 hB0
    have h5 : (A.card : ℝ) * 2 ^ C.count ≤ (B * 2 ^ G.cycleRank) * 2 ^ C.count := by
      calc (A.card : ℝ) * 2 ^ C.count ≤ B * 2 ^ (G.cycleRank + C.count) :=
            (h1.trans h2).trans h4
        _ = (B * 2 ^ G.cycleRank) * 2 ^ C.count := by rw [pow_add]; ring
    exact le_of_mul_le_mul_right h5 hpowa
  have hA' : ((Finset.univ.filter
      fun c : G.CycleWord => ¬ ∃ e ∈ D, c.1 e ≠ 0).card : ℝ) ≤ 2 ^ (G.cycleRank - t) := by
    have h := havoid
    rw [havoidcard] at h
    exact_mod_cast h
  rw [htotal]
  push_cast
  linarith

end Erdos1016.CycleCount

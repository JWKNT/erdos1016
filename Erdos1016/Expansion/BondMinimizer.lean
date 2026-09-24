import Erdos1016.Decomposition.Descent.ExteriorMerge

set_option autoImplicit false

/-!
# A failing expansion inequality admits a bond cut

The proof minimizes the boundary/order ratio over nonempty shores of size
at most half, then minimizes shore size among the minimizers. Neither shore
connectedness nor a Cheeger-minimizer oracle is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.SafeCore
local instance instSafeCoreBondMinimizerPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

def relativeCut (U A : Finset G.Vertex) : Finset G.Edge := crossing G A (U \ A)

def relativeCutSize (U A : Finset G.Vertex) : ℕ := (relativeCut G U A).card

/-- Empty sides make a zero right-hand side. Singletons therefore expand
at every requested threshold, the convention in the manuscript. -/
def HasExpansion (U : Finset G.Vertex) (h : ℝ) : Prop :=
  ∀ A ⊆ U, h * (min A.card (U \ A).card : ℕ) ≤ (relativeCutSize G U A : ℝ)

def smallShores (U : Finset G.Vertex) : Finset (Finset G.Vertex) :=
  U.powerset.filter fun A =>
    A.Nonempty ∧ (U \ A).Nonempty ∧ A.card ≤ (U \ A).card

def shoreRatio (U A : Finset G.Vertex) : ℝ :=
  (relativeCutSize G U A : ℝ) / (A.card : ℝ)

@[simp] theorem mem_smallShores (U A : Finset G.Vertex) :
    A ∈ smallShores G U ↔
      A ⊆ U ∧ A.Nonempty ∧ (U \ A).Nonempty ∧ A.card ≤ (U \ A).card := by
  simp only [smallShores, Finset.mem_filter, Finset.mem_powerset]

theorem relativeCut_complement {U A : Finset G.Vertex} (hAU : A ⊆ U) :
    relativeCut G U (U \ A) = relativeCut G U A := by
  have heq : U \ (U \ A) = A := by
    ext v
    simp only [Finset.mem_sdiff]
    constructor
    · tauto
    · intro hv
      exact ⟨hAU hv, by tauto⟩
  unfold relativeCut
  rw [heq, crossing_comm]

theorem relativeCutSize_complement {U A : Finset G.Vertex} (hAU : A ⊆ U) :
    relativeCutSize G U (U \ A) = relativeCutSize G U A := by
  simp only [relativeCutSize, relativeCut_complement G hAU]

theorem card_add_sdiff {U A : Finset G.Vertex} (hAU : A ⊆ U) :
    A.card + (U \ A).card = U.card := by
  have h := Finset.card_sdiff_add_card_eq_card hAU
  omega

/-- The cut identity inside U, still counting original labels. -/
theorem relativeCutSize_union {U A B : Finset G.Vertex}
    (hA : A ⊆ U) (hB : B ⊆ U) (hd : Disjoint A B) :
    relativeCutSize G U A + relativeCutSize G U B =
      relativeCutSize G U (A ∪ B) + 2 * crossSize G A B := by
  have hdis : ∀ v, ¬(v ∈ A ∧ v ∈ B) := fun v h => Finset.disjoint_left.1 hd h.1 h.2
  have hp (e : G.Edge) :
      (if e ∈ relativeCut G U A then 1 else 0) +
        (if e ∈ relativeCut G U B then 1 else 0) =
      (if e ∈ relativeCut G U (A ∪ B) then 1 else 0) +
        2 * (if e ∈ crossing G A B then 1 else 0) := by
    simp only [relativeCut, mem_crossing, Finset.mem_sdiff, Finset.mem_union]
    by_cases sa : G.src e ∈ A <;> by_cases sb : G.src e ∈ B <;>
      by_cases su : G.src e ∈ U <;> by_cases da : G.dst e ∈ A <;>
      by_cases db : G.dst e ∈ B <;> by_cases du : G.dst e ∈ U <;>
      all_goals
        have hsrcAU : G.src e ∈ A → G.src e ∈ U := fun hx => hA hx
        have hsrcBU : G.src e ∈ B → G.src e ∈ U := fun hx => hB hx
        have hdstAU : G.dst e ∈ A → G.dst e ∈ U := fun hx => hA hx
        have hdstBU : G.dst e ∈ B → G.dst e ∈ U := fun hx => hB hx
        have hsrcDis : ¬(G.src e ∈ A ∧ G.src e ∈ B) := by
          intro hx
          exact hdis (G.src e) ⟨hx.1, hx.2⟩
        have hdstDis : ¬(G.dst e ∈ A ∧ G.dst e ∈ B) := by
          intro hx
          exact hdis (G.dst e) ⟨hx.1, hx.2⟩
        simp_all
  have hs := congrArg (fun f : G.Edge → ℕ => ∑ e, f e) (funext hp)
  have hcard (C : Finset G.Edge) : C.card = ∑ e, (if e ∈ C then 1 else 0) := by
    classical
    calc
      C.card = ∑ e ∈ C, (1 : ℕ) := by simp
      _ = ∑ e, (if e ∈ C then 1 else 0) := by
        symm
        rw [Finset.sum_ite_mem Finset.univ C]
        simp
  calc
    relativeCutSize G U A + relativeCutSize G U B =
        (∑ e, (if e ∈ relativeCut G U A then 1 else 0)) +
          ∑ e, (if e ∈ relativeCut G U B then 1 else 0) := by
      change (relativeCut G U A).card + (relativeCut G U B).card = _
      rw [hcard, hcard]
    _ = ∑ e, ((if e ∈ relativeCut G U A then 1 else 0) +
        (if e ∈ relativeCut G U B then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ e, ((if e ∈ relativeCut G U (A ∪ B) then 1 else 0) +
        2 * (if e ∈ crossing G A B then 1 else 0)) := hs
    _ = relativeCutSize G U (A ∪ B) + 2 * crossSize G A B := by
      rw [Finset.sum_add_distrib]
      change (∑ e, (if e ∈ relativeCut G U (A ∪ B) then 1 else 0)) +
          (∑ e, 2 * (if e ∈ crossing G A B then 1 else 0)) = _
      rw [← hcard (relativeCut G U (A ∪ B)),
        ← Finset.mul_sum Finset.univ
          (fun e : G.Edge => if e ∈ crossing G A B then 1 else 0) 2,
        ← hcard (crossing G A B)]
      rw [relativeCutSize, crossSize]

theorem disconnected_split {U : Finset G.Vertex} (hne : U.Nonempty)
    (hn : ¬ ConnectedRegion G U) :
    ∃ A B : Finset G.Vertex, A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = U ∧ crossing G A B = ∅ := by
  have hnot : ¬ ∀ A ⊆ U, A.Nonempty → (U \ A).Nonempty →
      (crossing G A (U \ A)).Nonempty := by
    intro h
    exact hn ((connectedRegion_iff_cuts G U).2 ⟨hne, h⟩)
  push_neg at hnot
  obtain ⟨A, hAU, hA, hB, hcut⟩ := hnot
  refine ⟨A, U \ A, hA, hB, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.2 (by
      intro v hv hv'
      exact (Finset.mem_sdiff.1 hv').2 hv)
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro h
      rcases h with h | h
      · exact hAU h
      · exact h.1
    · tauto
  · exact Finset.not_nonempty_iff_eq_empty.1 hcut

private theorem finite_minimum {α : Type*} [DecidableEq α] {β : Type*} [LinearOrder β]
    (P : Finset α) (hne : P.Nonempty) (f : α → β) :
    ∃ a ∈ P, ∀ b ∈ P, f a ≤ f b := by
  let B := P.image f
  have hB : B.Nonempty := hne.image f
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 (Finset.min'_mem B hB)
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [hfa]
  exact Finset.min'_le B (f b) (Finset.mem_image.2 ⟨b, hb, rfl⟩)

private theorem finite_lex_minimum {α : Type*} [DecidableEq α]
    (P : Finset α) (hne : P.Nonempty) (f : α → ℝ) (g : α → ℕ) :
    ∃ a ∈ P, (∀ b ∈ P, f a ≤ f b) ∧
      (∀ b ∈ P, f b = f a → g a ≤ g b) := by
  obtain ⟨a, ha, hmin⟩ := finite_minimum P hne f
  let Q := P.filter fun b => f b = f a
  have hQ : Q.Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, rfl⟩⟩
  obtain ⟨b, hb, hg⟩ := finite_minimum Q hQ g
  obtain ⟨hbP, hba⟩ := Finset.mem_filter.1 hb
  refine ⟨b, hbP, ?_, ?_⟩
  · intro c hc
    rw [hba]
    exact hmin c hc
  · intro c hc hcb
    exact hg c (Finset.mem_filter.2 ⟨hc, hcb.trans hba⟩)

theorem expansion_of_minimal_small_shore {U S : Finset G.Vertex}
    (hS : S ∈ smallShores G U)
    (hmin : ∀ A ∈ smallShores G U, shoreRatio G U S ≤ shoreRatio G U A) :
    HasExpansion G U (shoreRatio G U S) := by
  intro A hAU
  by_cases hA : A.Nonempty
  · by_cases hB : (U \ A).Nonempty
    · rcases le_total A.card (U \ A).card with hsmall | hsmall
      · have hcan := (mem_smallShores G U A).2 ⟨hAU, hA, hB, hsmall⟩
        have hn : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA
        simpa only [min_eq_left hsmall] using (le_div_iff₀ hn).1 (hmin A hcan)
      · have heq : U \ (U \ A) = A := by
          ext v
          simp only [Finset.mem_sdiff]
          constructor
          · tauto
          · intro hv
            exact ⟨hAU hv, by tauto⟩
        have hcan : U \ A ∈ smallShores G U := by
          apply (mem_smallShores G U _).2
          exact ⟨Finset.sdiff_subset, hB, by simpa only [heq] using hA,
            by simpa only [heq] using hsmall⟩
        have hn : 0 < ((U \ A).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
        have h := (le_div_iff₀ hn).1 (hmin (U \ A) hcan)
        simpa only [min_eq_right hsmall, relativeCutSize_complement G hAU] using h
    · have he : U \ A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hB
      simp only [he, Finset.card_empty, Nat.min_zero, Nat.cast_zero, mul_zero]
      positivity
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
    subst A
    simp only [Finset.card_empty, Nat.zero_min, Nat.cast_zero, mul_zero]
    positivity

/-- The minimum-ratio shore of minimum size has both shores connected. -/
theorem minimal_shore_is_bond {U S : Finset G.Vertex}
    (hU : ConnectedRegion G U) (hS : S ∈ smallShores G U)
    (hmin : ∀ A ∈ smallShores G U, shoreRatio G U S ≤ shoreRatio G U A)
    (htie : ∀ A ∈ smallShores G U, shoreRatio G U A = shoreRatio G U S →
      S.card ≤ A.card) :
    ConnectedRegion G S ∧ ConnectedRegion G (U \ S) := by
  classical
  obtain ⟨hSU, hSne, hTne, hhalf⟩ := (mem_smallShores G U S).1 hS
  let k := shoreRatio G U S
  have kpos : 0 < k := by
    apply div_pos
    · have hcutpos : (relativeCut G U S).Nonempty := by
        exact ((connectedRegion_iff_cuts G U).1 hU).2 S hSU hSne hTne
      exact_mod_cast Finset.card_pos.2 hcutpos
    · exact_mod_cast Finset.card_pos.2 hSne
  have sizes := card_add_sdiff G hSU
  have exactS : (relativeCutSize G U S : ℝ) = k * (S.card : ℝ) := by
    dsimp [k, shoreRatio]
    rw [div_mul_cancel₀ _ (by exact_mod_cast (Finset.card_pos.2 hSne).ne')]
  have allcuts := expansion_of_minimal_small_shore G hS hmin
  have strict (A : Finset G.Vertex) (hA : A ∈ smallShores G U) (hcard : A.card < S.card) :
      k * (A.card : ℝ) < relativeCutSize G U A := by
    have hr : k < shoreRatio G U A := by
      by_contra hh
      have heq : shoreRatio G U A = k := le_antisymm (le_of_not_gt hh) (hmin A hA)
      have := htie A hA heq
      omega
    have hpos : 0 < (A.card : ℝ) := by
      exact_mod_cast Finset.card_pos.2 ((mem_smallShores G U A).1 hA).2.1
    exact (lt_div_iff₀ hpos).1 hr
  have hconnS : ConnectedRegion G S := by
    by_contra hn
    obtain ⟨A, B, hA, hB, hd, hab, hcross⟩ := disconnected_split G hSne hn
    have hAS : A ⊆ S := by rw [← hab]; exact Finset.subset_union_left
    have hBS : B ⊆ S := by rw [← hab]; exact Finset.subset_union_right
    have hAU := hAS.trans hSU
    have hBU := hBS.trans hSU
    have habcard : A.card + B.card = S.card := by rw [← Finset.card_union_of_disjoint hd, hab]
    have haPos := Finset.card_pos.2 hA
    have hbPos := Finset.card_pos.2 hB
    have haTotal := card_add_sdiff G hAU
    have hbTotal := card_add_sdiff G hBU
    have haSmall : A.card ≤ (U \ A).card := by omega
    have hbSmall : B.card ≤ (U \ B).card := by omega
    have haComp : (U \ A).Nonempty := Finset.card_pos.1 (by omega)
    have hbComp : (U \ B).Nonempty := Finset.card_pos.1 (by omega)
    have hstrict := strict A ((mem_smallShores G U A).2 ⟨hAU, hA, haComp, haSmall⟩)
      (by omega)
    have hbound := allcuts B hBU
    rw [min_eq_left hbSmall] at hbound
    have hsum := relativeCutSize_union G hAU hBU hd
    have hzero : crossSize G A B = 0 := by simp [crossSize, hcross]
    rw [hab, hzero, Nat.mul_zero, Nat.add_zero] at hsum
    have hsumR : (relativeCutSize G U A : ℝ) + relativeCutSize G U B =
        relativeCutSize G U S := by exact_mod_cast hsum
    have hcardR : (A.card : ℝ) + B.card = S.card := by exact_mod_cast habcard
    have hbad : k * (S.card : ℝ) < k * (S.card : ℝ) := by
      calc
        k * (S.card : ℝ) = k * (A.card : ℝ) + k * (B.card : ℝ) := by
          rw [← hcardR, mul_add]
        _ < (relativeCutSize G U A : ℝ) + relativeCutSize G U B :=
          add_lt_add_of_lt_of_le hstrict hbound
        _ = k * (S.card : ℝ) := hsumR.trans exactS
    exact (lt_irrefl _ hbad)
  refine ⟨hconnS, ?_⟩
  by_contra hn
  obtain ⟨A, B, hA, hB, hd, hab, hcross⟩ := disconnected_split G hTne hn
  have hAT : A ⊆ U \ S := by rw [← hab]; exact Finset.subset_union_left
  have hBT : B ⊆ U \ S := by rw [← hab]; exact Finset.subset_union_right
  have hAU := hAT.trans Finset.sdiff_subset
  have hBU := hBT.trans Finset.sdiff_subset
  have habcard : A.card + B.card = (U \ S).card := by
    rw [← Finset.card_union_of_disjoint hd, hab]
  have haPos := Finset.card_pos.2 hA
  have hbPos := Finset.card_pos.2 hB
  have haTotal := card_add_sdiff G hAU
  have hbTotal := card_add_sdiff G hBU
  have hsum := relativeCutSize_union G hAU hBU hd
  have hzero : crossSize G A B = 0 := by simp [crossSize, hcross]
  rw [hab, hzero, Nat.mul_zero, Nat.add_zero, relativeCutSize_complement G hSU] at hsum
  have hsumR : (relativeCutSize G U A : ℝ) + relativeCutSize G U B =
      relativeCutSize G U S := by exact_mod_cast hsum
  have noLargeA : A.card ≤ (U \ A).card := by
    by_contra hnA
    have hsmall : (U \ A).card ≤ A.card := by omega
    have hbound := allcuts A hAU
    rw [min_eq_right hsmall] at hbound
    have hcomp : (S.card : ℝ) < ((U \ A).card : ℝ) := by exact_mod_cast (by omega : S.card < (U \ A).card)
    have hbad : k * (S.card : ℝ) < k * (S.card : ℝ) := by
      calc
        k * (S.card : ℝ) < k * ((U \ A).card : ℝ) := mul_lt_mul_of_pos_left hcomp kpos
        _ ≤ (relativeCutSize G U A : ℝ) := hbound
        _ ≤ (relativeCutSize G U A : ℝ) + relativeCutSize G U B :=
          le_add_of_nonneg_right (Nat.cast_nonneg _)
        _ = k * (S.card : ℝ) := hsumR.trans exactS
    exact lt_irrefl _ hbad
  have noLargeB : B.card ≤ (U \ B).card := by
    by_contra hnB
    have hsmall : (U \ B).card ≤ B.card := by omega
    have hbound := allcuts B hBU
    rw [min_eq_right hsmall] at hbound
    have hcomp : (S.card : ℝ) < ((U \ B).card : ℝ) := by exact_mod_cast (by omega : S.card < (U \ B).card)
    have hbad : k * (S.card : ℝ) < k * (S.card : ℝ) := by
      calc
        k * (S.card : ℝ) < k * ((U \ B).card : ℝ) := mul_lt_mul_of_pos_left hcomp kpos
        _ ≤ (relativeCutSize G U B : ℝ) := hbound
        _ ≤ (relativeCutSize G U A : ℝ) + relativeCutSize G U B :=
          le_add_of_nonneg_left (Nat.cast_nonneg _)
        _ = k * (S.card : ℝ) := hsumR.trans exactS
    exact lt_irrefl _ hbad
  have hbA := allcuts A hAU
  have hbB := allcuts B hBU
  rw [min_eq_left noLargeA] at hbA
  rw [min_eq_left noLargeB] at hbB
  have hTleS : (U \ S).card ≤ S.card := by
    have hr : k * ((U \ S).card : ℝ) ≤ k * (S.card : ℝ) := by
      calc
        k * ((U \ S).card : ℝ) = k * (A.card : ℝ) + k * (B.card : ℝ) := by
          rw [← habcard, Nat.cast_add, mul_add]
        _ ≤ (relativeCutSize G U A : ℝ) + relativeCutSize G U B := add_le_add hbA hbB
        _ = _ := hsumR.trans exactS
    exact_mod_cast (mul_le_mul_left kpos).1 hr
  have hstrict := strict A ((mem_smallShores G U A).2
    ⟨hAU, hA, Finset.card_pos.1 (by omega), noLargeA⟩) (by omega)
  have hT_eq : (U \ S).card = S.card := Nat.le_antisymm hTleS hhalf
  have hbad : k * (S.card : ℝ) < k * (S.card : ℝ) := by
    calc
      k * (S.card : ℝ) = k * (A.card : ℝ) + k * (B.card : ℝ) := by
        rw [← hT_eq, ← habcard, Nat.cast_add, mul_add]
      _ < (relativeCutSize G U A : ℝ) + relativeCutSize G U B :=
        add_lt_add_of_lt_of_le hstrict hbB
      _ = _ := hsumR.trans exactS
  exact lt_irrefl _ hbad

/-- An actual connected-shore cut, not an assumed Cheeger-minimizer object. -/
theorem exists_bond_of_not_expands {U : Finset G.Vertex} {h : ℝ}
    (hU : ConnectedRegion G U) (hfail : ¬ HasExpansion G U h) :
    ∃ s : BondSplit G U,
      (crossSize G s.left s.right : ℝ) <
        h * (min s.left.card s.right.card : ℕ) := by
  have hf : ∃ A ⊆ U,
      (relativeCutSize G U A : ℝ) < h * (min A.card (U \ A).card : ℕ) := by
    unfold HasExpansion at hfail
    push_neg at hfail
    exact hfail
  obtain ⟨A, hAU, hbad⟩ := hf
  have hA : A.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.1 hn
    simp only [he, Finset.card_empty, Nat.zero_min, Nat.cast_zero, mul_zero] at hbad
    exact not_lt_of_ge (Nat.cast_nonneg _) hbad
  have hB : (U \ A).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.1 hn
    simp only [he, Finset.card_empty, Nat.min_zero, Nat.cast_zero, mul_zero] at hbad
    exact not_lt_of_ge (Nat.cast_nonneg _) hbad
  have hP : (smallShores G U).Nonempty := by
    rcases le_total A.card (U \ A).card with hc | hc
    · exact ⟨A, (mem_smallShores G U A).2 ⟨hAU, hA, hB, hc⟩⟩
    · have heq : U \ (U \ A) = A := by
        ext v
        simp only [Finset.mem_sdiff]
        constructor
        · tauto
        · intro hv
          exact ⟨hAU hv, by tauto⟩
      refine ⟨U \ A, (mem_smallShores G U _).2 ?_⟩
      exact ⟨Finset.sdiff_subset, hB, by simpa only [heq] using hA,
        by simpa only [heq] using hc⟩
  obtain ⟨S, hS, hmin, htie⟩ := finite_lex_minimum (smallShores G U) hP
    (shoreRatio G U) Finset.card
  have hsides := minimal_shore_is_bond G hU hS hmin htie
  have hs := (mem_smallShores G U S).1 hS
  have hr : shoreRatio G U S < h := by
    have hlo := expansion_of_minimal_small_shore G hS hmin A hAU
    have hpos : 0 < (min A.card (U \ A).card : ℕ) :=
      lt_min (Finset.card_pos.2 hA) (Finset.card_pos.2 hB)
    have hposR : (0 : ℝ) < (min A.card (U \ A).card : ℕ) := by exact_mod_cast hpos
    exact (mul_lt_mul_right hposR).1 (lt_of_le_of_lt hlo hbad)
  let s : BondSplit G U := {
    left := S
    right := U \ S
    disjoint := Finset.disjoint_left.2 (by
      intro v hv hv'
      exact (Finset.mem_sdiff.1 hv').2 hv)
    union_eq := by
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hv | hv)
        · exact hs.1 hv
        · exact hv.1
      · intro hv
        by_cases hvs : v ∈ S
        · exact Or.inl hvs
        · exact Or.inr ⟨hv, hvs⟩
    left_connected := hsides.1
    right_connected := hsides.2 }
  refine ⟨s, ?_⟩
  have hn : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs.2.1
  have hh := (div_lt_iff₀ hn).1 hr
  simpa only [s, min_eq_left hs.2.2.2, crossSize, relativeCutSize, relativeCut] using hh

end Erdos1016.SafeCore

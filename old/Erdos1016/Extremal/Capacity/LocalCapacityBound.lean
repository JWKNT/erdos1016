import Erdos1016.Extremal.Capacity.AlphaCapacity
import Erdos1016.Extremal.Capacity.RestrictionMonotonicity
import Erdos1016.Extremal.Capacity.Tail

set_option autoImplicit false

/-!
# The numerical tail of the finite `α`-to-`Φ` bridge

This file isolates the final estimate in the greedy proof from §2. Given the
edge/rank certificate produced by the greedy cycle extraction, this estimate
and a supremum argument imply the paper's finite bridge. Constructing that
certificate inside an arbitrary graph remains a separate combinatorial step.
-/

namespace Erdos1016.Proof.FiniteAlphaBridge

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Extremal

private theorem six_mul_le_two_pow (R : ℕ) (hR : 5 ≤ R) :
    6 * R ≤ 2 ^ R := by
  induction R, hR using Nat.le_induction with
  | base => norm_num
  | @succ n hn ih =>
      have hpow : 6 ≤ 2 ^ n := by
        have h6n : 6 ≤ 6 * n := by omega
        exact h6n.trans ih
      rw [Nat.pow_succ]
      omega

/-- For every greedy terminal rank `p ≥ 2R`, the residual edge-count term
`(2^R + 3p)/2^p` is at most the error `2^(1-R)` in the paper. -/
theorem greedy_residual_error_le (R p : ℕ) (hR : 5 ≤ R) (hp : 2 * R ≤ p) :
    ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (1 - (R : ℝ)) := by
  have hnat : 2 ^ R + 3 * p ≤ 2 ^ (p + 1 - R) := by
    have hbase : 2 ^ R + 3 * (2 * R) ≤ 2 ^ (2 * R + 1 - R) := by
      have h6 := six_mul_le_two_pow R hR
      have hsum : 2 ^ R + 3 * (2 * R) ≤ 2 ^ R + 2 ^ R := by
        have heq : 3 * (2 * R) = 6 * R := by omega
        rw [heq]
        exact Nat.add_le_add_left h6 _
      have hpow : 2 ^ R + 2 ^ R = 2 ^ (R + 1) := by
        rw [Nat.pow_succ]
        omega
      calc
        2 ^ R + 3 * (2 * R) ≤ 2 ^ R + 2 ^ R := hsum
        _ = 2 ^ (R + 1) := hpow
        _ = 2 ^ (2 * R + 1 - R) := by congr 1 <;> omega
    have hstep : ∀ q : ℕ, 2 * R ≤ q →
        2 ^ R + 3 * q ≤ 2 ^ (q + 1 - R) := by
      intro q hq
      induction q, hq using Nat.le_induction with
      | base => simpa using hbase
      | @succ q hq ih =>
          have hexp : 3 ≤ 2 ^ (q + 1 - R) := by
            have hlarge : 3 ≤ q + 1 - R := by omega
            have hbound := six_mul_le_two_pow (q + 1 - R) (by omega)
            have hthree : 3 ≤ 6 * (q + 1 - R) := by omega
            exact hthree.trans hbound
          have heq : q + 1 + 1 - R = (q + 1 - R) + 1 := by omega
          rw [heq, Nat.pow_succ, Nat.mul_two]
          omega
    exact hstep p hp
  have hcast : ((2 ^ R + 3 * p : ℕ) : ℝ) ≤
      ((2 ^ (p + 1 - R) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hexpCast : ((p + 1 - R : ℕ) : ℝ) =
      (p : ℝ) + 1 - (R : ℝ) := by
    rw [Nat.cast_sub (by omega : R ≤ p + 1)]
    push_cast
    ring
  have hmul : (2 : ℝ) ^ (1 - (R : ℝ)) * (2 : ℝ) ^ p =
      (2 : ℝ) ^ (p + 1 - (R : ℝ)) := by
    rw [← Real.rpow_natCast (2 : ℝ) p]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnum : (2 : ℝ) ^ R + 3 * p ≤
      (2 : ℝ) ^ (1 - (R : ℝ)) * (2 : ℝ) ^ p := by
    calc
      (2 : ℝ) ^ R + 3 * p = ((2 ^ R + 3 * p : ℕ) : ℝ) := by norm_cast
      _ ≤ ((2 ^ (p + 1 - R) : ℕ) : ℝ) := hcast
      _ = (2 : ℝ) ^ (p + 1 - (R : ℝ)) := by
        rw [← hexpCast]
        norm_cast
      _ = _ := hmul.symm
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ p)).2
  nlinarith [hnum]

/-- Exact certificate required from the greedy graph construction: the
restricted local capacity is at most the global tail capacity plus the
rank-dependent edge-count term. -/
def GreedyCertificate (R : ℕ) (φ : ℝ) (G : PhysicalGraph) : Prop :=
  ∃ p : ℕ, 2 * R ≤ p ∧
    G.normalizedLinearForestCapacity ≤
      φ + ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p

/-- Edge-support form of the greedy certificate. This is the useful target
for formalizing the cycle-by-cycle extraction: `E` is its retained edge set,
`p` its cycle rank, and the final inequality is the accumulated edge budget. -/
def EdgeBudgetCertificate (R : ℕ) (φ : ℝ) (G : PhysicalGraph) : Prop :=
  ∃ E : Finset G.Edge, ∃ p : ℕ,
    2 * R ≤ p ∧ G.restrictedCycleRank E = p ∧
      ((G.restrictPhysical E).edgeCount + 1 : ℝ) ≤
        φ * (2 : ℝ) ^ p + (2 : ℝ) ^ R + 3 * p

/-- The edge-budget certificate implies the local-capacity estimate using
restriction monotonicity and the elementary count of possible forest lengths. -/
theorem greedyCertificate_of_edgeBudget
    (R : ℕ) (φ : ℝ) (G : PhysicalGraph)
    (hcert : EdgeBudgetCertificate R φ G) : GreedyCertificate R φ G := by
  rcases hcert with ⟨E, p, hp, hrank, hbudget⟩
  refine ⟨p, hp, ?_⟩
  let H := G.restrictPhysical E
  have hmon : G.normalizedLinearForestCapacity ≤ H.normalizedLinearForestCapacity := by
    exact Erdos1016.Proof.CapacityBridge.normalizedLinearForestCapacity_le_restrictPhysical G E
  have hmult : H.maxLinearForestMultiplicity ≤ H.edgeCount + 1 := by
    unfold maxLinearForestMultiplicity
    apply Finset.sup_le
    intro t ht
    exact H.linearForestMultiplicity_le_edgeCount_add_one t
  have hdim : H.cycleRank = p := by
    dsimp [H]
    rw [G.restrictPhysical_cycleRank]
    exact hrank
  have hlocal : H.normalizedLinearForestCapacity ≤
      ((H.edgeCount + 1 : ℕ) : ℝ) / (2 : ℝ) ^ p := by
    unfold normalizedLinearForestCapacity
    rw [hdim]
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hmult
    · positivity
  have hbudget' : ((H.edgeCount + 1 : ℕ) : ℝ) ≤
      (φ + ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p) *
        (2 : ℝ) ^ p := by
    have hpD : 0 < (2 : ℝ) ^ p := by positivity
    have hbudgetR : ((H.edgeCount + 1 : ℕ) : ℝ) ≤
        φ * (2 : ℝ) ^ p + (2 : ℝ) ^ R + 3 * p := by
      simpa [H] using hbudget
    calc
      ((H.edgeCount + 1 : ℕ) : ℝ) ≤
          φ * (2 : ℝ) ^ p + (2 : ℝ) ^ R + 3 * p := hbudgetR
      _ = (φ + ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p) *
            (2 : ℝ) ^ p := by
        field_simp
        ring
  have hpD : 0 < (2 : ℝ) ^ p := by positivity
  have hbudgetDiv : ((H.edgeCount + 1 : ℕ) : ℝ) / (2 : ℝ) ^ p ≤
      φ + ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p :=
    (div_le_iff₀ hpD).2 (by nlinarith [hbudget'])
  exact hmon.trans (hlocal.trans hbudgetDiv)

/-- Extend a word supported on an edge set `E` by zero to a larger edge set
`F`. -/
private def extendRestrictedWordLinear (G : PhysicalGraph)
    (E F : Finset G.Edge) (hEF : E ⊆ F) :
    G.RestrictedWord E →ₗ[F₂] G.RestrictedWord F where
  toFun x e := if he : e.1 ∈ E then x ⟨e.1, he⟩ else 0
  map_add' x y := by
    funext e
    by_cases he : e.1 ∈ E <;> simp [he]
  map_smul' a x := by
    funext e
    by_cases he : e.1 ∈ E <;> simp [he]

/-- If a new edge set contains a cycle that was not already supported on the
old set, the restricted cycle rank increases strictly. This is the local
rank-jump fact needed at each step of the greedy extraction. -/
theorem restrictedCycleRank_lt_of_new_cycle
    (G : PhysicalGraph) (E F : Finset G.Edge) (C : G.CycleWord)
    (hEF : E ⊆ F)
    (hcycle : G.edgeSupport C.1 ⊆ F)
    (hnew : ¬ G.edgeSupport C.1 ⊆ E) :
    G.restrictedCycleRank E < G.restrictedCycleRank F := by
  classical
  obtain ⟨e, heC, heE⟩ := Finset.not_subset.mp hnew
  have heF : e ∈ F := hcycle heC
  let f : G.RestrictedCycleSpace E →ₗ[F₂] G.RestrictedCycleSpace F :=
    LinearMap.codRestrict (G.RestrictedCycleSpace F)
      ((extendRestrictedWordLinear G E F hEF).comp
        (G.RestrictedCycleSpace E).subtype) (by
          intro x
          change G.restrictedBoundary F
              (extendRestrictedWordLinear G E F hEF x.1) = 0
          change G.boundary (G.extendWord F
              (extendRestrictedWordLinear G E F hEF x.1)) = 0
          have hword : G.extendWord F
                (extendRestrictedWordLinear G E F hEF x.1) =
              G.extendWord E x.1 := by
            funext q
            by_cases hq : q ∈ E
            · have hqF := hEF hq
              simp [extendWord, extendRestrictedWordLinear, hq, hqF]
            · by_cases hqF : q ∈ F
              · simp [extendWord, extendRestrictedWordLinear, hq, hqF]
              · simp [extendWord, extendRestrictedWordLinear, hq, hqF]
          rw [hword]
          change G.restrictedBoundary E x.1 = 0
          exact x.2)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext q
    have hv : (f x).1 = (f y).1 :=
      congrArg (fun z : G.RestrictedCycleSpace F => (z.1 : G.RestrictedWord F)) hxy
    have heq := congrFun hv ⟨q.1, hEF q.2⟩
    simpa [f, extendRestrictedWordLinear] using heq
  let y : G.RestrictedCycleSpace F := by
    refine ⟨G.restrictWord F C.1, ?_⟩
    change G.boundary (G.extendWord F (G.restrictWord F C.1)) = 0
    have hzero : ∀ q, q ∉ F → C.1 q = 0 := by
      intro q hq
      by_contra hnot
      have hmem : q ∈ G.edgeSupport C.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      exact hq (hcycle hmem)
    rw [G.extend_restrict_of_outside_zero F C.1 hzero]
    exact C.2.2.1
  have hy : y ∉ Set.range f := by
    rintro ⟨x, hx⟩
    have hv := congrArg Subtype.val hx
    have heq := congrFun hv ⟨e, heF⟩
    simp [y, f, extendRestrictedWordLinear, restrictWord, heE] at heq
    have hnonzero : C.1 e ≠ 0 := by
      simpa [PhysicalGraph.edgeSupport] using heC
    exact hnonzero heq.symm
  have hcard := Fintype.card_lt_of_injective_of_not_mem f hf hy
  have hcardE : Fintype.card (G.RestrictedCycleSpace E) =
      2 ^ G.restrictedCycleRank E := by
    simpa [F₂, restrictedCycleRank] using
      (Module.card_eq_pow_finrank (K := F₂) (V := G.RestrictedCycleSpace E))
  have hcardF : Fintype.card (G.RestrictedCycleSpace F) =
      2 ^ G.restrictedCycleRank F := by
    simpa [F₂, restrictedCycleRank] using
      (Module.card_eq_pow_finrank (K := F₂) (V := G.RestrictedCycleSpace F))
  rw [hcardE, hcardF] at hcard
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hcard

/-- Reindex a host cycle onto the physical edge restriction. -/
noncomputable def restrictCycleWord (G : PhysicalGraph) (E : Finset G.Edge)
    (C : G.CycleWord) : (G.restrictPhysical E).Word :=
  (G.restrictPhysicalWordEquiv E).symm (G.restrictWord E C.1)

private theorem restrictPhysical_src_symm (G : PhysicalGraph) (E : Finset G.Edge)
    (e : G.RestrictedEdge E) :
    (G.restrictPhysical E).src ((G.restrictedEdgeEquiv E).symm e) = G.src e.1 := by
  simp [restrictPhysical, restrictedEdgeEquiv]

private theorem restrictPhysical_dst_symm (G : PhysicalGraph) (E : Finset G.Edge)
    (e : G.RestrictedEdge E) :
    (G.restrictPhysical E).dst ((G.restrictedEdgeEquiv E).symm e) = G.dst e.1 := by
  simp [restrictPhysical, restrictedEdgeEquiv]

private theorem restrictedSelectedGraph_eq_of_cycle_support (G : PhysicalGraph)
    (E : Finset G.Edge) (C : G.CycleWord)
    (hE : G.edgeSupport C.1 ⊆ E) :
    G.restrictedSelectedGraph E (G.restrictWord E C.1) = G.selectedGraph C.1 := by
  ext u v
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact ⟨e.1, by simpa [restrictWord] using he, Or.inl h⟩
    · exact ⟨e.1, by simpa [restrictWord] using he, Or.inr h⟩
  · rintro ⟨e, he, h | h⟩
    · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      exact ⟨⟨e, heE⟩, by simpa [restrictWord] using he, Or.inl h⟩
    · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      exact ⟨⟨e, heE⟩, by simpa [restrictWord] using he, Or.inr h⟩

private theorem restrictedSelectedDegree_eq_of_cycle_support (G : PhysicalGraph)
    (E : Finset G.Edge) (C : G.CycleWord)
    (hE : G.edgeSupport C.1 ⊆ E) (v : G.Vertex) :
    G.restrictedSelectedDegree E (G.restrictWord E C.1) v =
      G.selectedDegree C.1 v := by
  classical
  let A := {e : G.RestrictedEdge E //
    G.restrictWord E C.1 e ≠ 0 ∧ G.incident e.1 v}
  let B := {e : G.Edge // C.1 e ≠ 0 ∧ G.incident e v}
  let f : A ≃ B := {
    toFun := fun e => ⟨e.1.1, by
      constructor
      · simpa [restrictWord] using e.2.1
      · exact e.2.2⟩
    invFun := fun e => by
      have heE : e.1 ∈ E := hE
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2.1⟩)
      exact ⟨⟨e.1, heE⟩, by
        constructor
        · simpa [restrictWord] using e.2.1
        · exact e.2.2⟩
    left_inv := by intro e; apply Subtype.ext; rfl
    right_inv := by intro e; apply Subtype.ext; rfl }
  have hcard := Fintype.card_congr f
  simpa [A, B, restrictedSelectedDegree, PhysicalGraph.selectedDegree,
    Fintype.card_coe, Fintype.card_subtype] using hcard

private theorem restrictCycle_selectedGraph_eq (G : PhysicalGraph)
    (E : Finset G.Edge) (C : G.CycleWord) :
    (G.restrictPhysical E).selectedGraph (restrictCycleWord G E C) =
      G.restrictedSelectedGraph E (G.restrictWord E C.1) := by
  ext u v
  constructor
  · rintro ⟨i, hi, h | h⟩
    · refine ⟨G.restrictedEdgeEquiv E i, ?_, ?_⟩
      · simpa [restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord] using hi
      · exact Or.inl ⟨by simpa [restrictPhysical] using h.1,
          by simpa [restrictPhysical] using h.2⟩
    · refine ⟨G.restrictedEdgeEquiv E i, ?_, ?_⟩
      · simpa [restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord] using hi
      · exact Or.inr ⟨by simpa [restrictPhysical] using h.1,
          by simpa [restrictPhysical] using h.2⟩
  · rintro ⟨e, he, h | h⟩
    · let i := (G.restrictedEdgeEquiv E).symm e
      refine ⟨i, ?_, ?_⟩
      · simpa [restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord, i] using he
      · exact Or.inl ⟨by simpa [restrictPhysical, i] using h.1,
          by simpa [restrictPhysical, i] using h.2⟩
    · let i := (G.restrictedEdgeEquiv E).symm e
      refine ⟨i, ?_, ?_⟩
      · simpa [restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord, i] using he
      · exact Or.inr ⟨by simpa [restrictPhysical, i] using h.1,
          by simpa [restrictPhysical, i] using h.2⟩

private theorem restrictCycle_selectedDegree_eq (G : PhysicalGraph)
    (E : Finset G.Edge) (C : G.CycleWord) (v : G.Vertex) :
    (G.restrictPhysical E).selectedDegree (restrictCycleWord G E C) v =
      G.restrictedSelectedDegree E (G.restrictWord E C.1) v := by
  classical
  let H := G.restrictPhysical E
  let x := restrictCycleWord G E C
  let A := {i : H.Edge // x i ≠ 0 ∧ H.incident i v}
  let B := {e : G.RestrictedEdge E // G.restrictWord E C.1 e ≠ 0 ∧ G.incident e.1 v}
  let f : A ≃ B := {
    toFun := fun i => ⟨G.restrictedEdgeEquiv E i.1, by
      constructor
      · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord] using i.2.1
      · simpa [restrictPhysical, restrictedEdgeEquiv] using i.2.2⟩
    invFun := fun e => ⟨(G.restrictedEdgeEquiv E).symm e.1, by
      constructor
      · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
          restrictedEdgeEquiv, restrictWord] using e.2.1
      · rcases e.2.2 with h | h
        · exact Or.inl ((restrictPhysical_src_symm G E e.1).trans h)
        · exact Or.inr ((restrictPhysical_dst_symm G E e.1).trans h)⟩
    left_inv := by intro i; apply Subtype.ext; simp
    right_inv := by intro e; apply Subtype.ext; simp }
  have hcard := Fintype.card_congr f
  simpa [A, B, H, x, restrictCycleWord, PhysicalGraph.selectedDegree,
    restrictedSelectedDegree, Fintype.card_coe, Fintype.card_subtype] using hcard

/-- A host cycle whose support is contained in E remains a cycle in the
physical restriction to E, with exactly the same length. -/
theorem restrictCycleWord_isCycle
    (G : PhysicalGraph) (E : Finset G.Edge) (C : G.CycleWord)
    (hE : G.edgeSupport C.1 ⊆ E) :
    ∃ D : (G.restrictPhysical E).CycleWord,
      D.1 = restrictCycleWord G E C := by
  classical
  let H := G.restrictPhysical E
  let x := restrictCycleWord G E C
  have hout : ∀ e, e ∉ E → C.1 e = 0 := by
    intro e he
    by_contra hn
    have hs : e ∈ G.edgeSupport C.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact he (hE hs)
  have hext := G.extend_restrict_of_outside_zero E C.1 hout
  have hxne : x ≠ 0 := by
    intro hx
    have hrestrict : G.restrictWord E C.1 = 0 := by
      have h := congrArg (G.restrictPhysicalWordEquiv E) hx
      simpa [x, restrictCycleWord] using h
    have hCzero : C.1 = 0 := by
      rw [← hext, hrestrict]
      funext e
      simp [extendWord]
    exact C.2.1 hCzero
  refine ⟨⟨x, ?_⟩, rfl⟩
  refine ⟨hxne, ?_, ?_, ?_⟩
  · change H.boundary x = 0
    rw [G.restrictPhysical_boundary E x]
    have hxrestrict : G.restrictPhysicalWordEquiv E x =
        G.restrictWord E C.1 := by
      simp [x, restrictCycleWord]
    rw [hxrestrict]
    change G.boundary (G.extendWord E (G.restrictWord E C.1)) = 0
    rw [hext]
    exact C.2.2.1
  · rw [restrictCycle_selectedGraph_eq]
    rw [restrictedSelectedGraph_eq_of_cycle_support G E C hE]
    have hused : H.usedVertices x = G.usedVertices C.1 := by
      ext v
      simp only [PhysicalGraph.usedVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨e, he, h | h⟩
        · refine ⟨(G.restrictedEdgeEquiv E e).1, ?_, Or.inl ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord] using he
          · simpa [restrictPhysical] using h
        · refine ⟨(G.restrictedEdgeEquiv E e).1, ?_, Or.inr ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord] using he
          · simpa [restrictPhysical] using h
      · rintro ⟨e, he, h | h⟩
        · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          refine ⟨(G.restrictedEdgeEquiv E).symm ⟨e, heE⟩, ?_, Or.inl ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord]
          · exact (restrictPhysical_src_symm G E ⟨e, heE⟩).trans h
        · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          refine ⟨(G.restrictedEdgeEquiv E).symm ⟨e, heE⟩, ?_, Or.inr ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord]
          · exact (restrictPhysical_dst_symm G E ⟨e, heE⟩).trans h
    rw [hused]
    exact C.2.2.2.1
  · intro v hv
    have hused : H.usedVertices x = G.usedVertices C.1 := by
      ext u
      simp only [PhysicalGraph.usedVertices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨e, he, h | h⟩
        · refine ⟨(G.restrictedEdgeEquiv E e).1, ?_, Or.inl ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord] using he
          · simpa [restrictPhysical] using h
        · refine ⟨(G.restrictedEdgeEquiv E e).1, ?_, Or.inr ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord] using he
          · simpa [restrictPhysical] using h
      · rintro ⟨e, he, h | h⟩
        · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          refine ⟨(G.restrictedEdgeEquiv E).symm ⟨e, heE⟩, ?_, Or.inl ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord]
          · exact (restrictPhysical_src_symm G E ⟨e, heE⟩).trans h
        · have heE : e ∈ E := hE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
          refine ⟨(G.restrictedEdgeEquiv E).symm ⟨e, heE⟩, ?_, Or.inr ?_⟩
          · simpa [x, restrictCycleWord, restrictPhysicalWordEquiv,
              restrictedEdgeEquiv, restrictWord]
          · exact (restrictPhysical_dst_symm G E ⟨e, heE⟩).trans h
    have hv' : v ∈ G.usedVertices C.1 := by
      rw [← hused]
      exact hv
    rw [restrictCycle_selectedDegree_eq]
    rw [restrictedSelectedDegree_eq_of_cycle_support G E C hE v]
    exact C.2.2.2.2 v hv'

theorem restrictCycleWord_length
    (G : PhysicalGraph) (E : Finset G.Edge) (C : G.CycleWord)
    (hE : G.edgeSupport C.1 ⊆ E) :
    (G.restrictPhysical E).wordLength (restrictCycleWord G E C) = G.wordLength C.1 := by
  have h := G.restrictPhysical_wordLength E (restrictCycleWord G E C)
  rw [h]
  have hpart := G.wordLength_partition E C.1
  have hout : G.outsideWordLength E (G.restrictOutsideWord E C.1) = 0 := by
    unfold outsideWordLength
    apply Finset.card_eq_zero.mpr
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hn
      have hs : e.1 ∈ G.edgeSupport C.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [restrictOutsideWord] using hn⟩
      exact False.elim (e.2 (hE hs))
    · intro hn
      simpa using hn
  have hrestricted : G.restrictedWordLength E (G.restrictWord E C.1) = G.wordLength C.1 := by
    rw [hpart, hout, Nat.add_zero]
  simpa [restrictCycleWord] using hrestricted







/-- The greedy certificate lifts uniformly over all graphs to the finite
`α`-to-tail bridge. The only graph-specific input is `GreedyCertificate` for
each graph covering the target interval. -/
theorem alphaCapacity_le_tail_of_greedyCertificate
    (R : ℕ) (hR : 5 ≤ R)
    (hcert : ∀ G : PhysicalGraph, G.InitialCoverage (2 ^ (2 * R) + 1) →
      GreedyCertificate R (tailCapacity R) G) :
    alphaCapacity (2 ^ (2 * R) + 1) ≤
      tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
  unfold alphaCapacity
  apply csSup_le (alphaCapacitySet_nonempty _)
  rintro a ⟨G, hG, rfl⟩
  obtain ⟨p, hp, hlocal⟩ := hcert G hG
  calc
    G.normalizedLinearForestCapacity ≤
        tailCapacity R + ((2 : ℝ) ^ R + 3 * p) / (2 : ℝ) ^ p := hlocal
    _ ≤ tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
      gcongr
      exact greedy_residual_error_le R p hR hp

/-- Equivalent bridge statement under the direct edge-set extraction
hypothesis. This exposes exactly the remaining graph-specific obligation. -/
theorem alphaCapacity_le_tail_of_edgeBudgetCertificate
    (R : ℕ) (hR : 5 ≤ R)
    (hcert : ∀ G : PhysicalGraph, G.InitialCoverage (2 ^ (2 * R) + 1) →
      EdgeBudgetCertificate R (tailCapacity R) G) :
    alphaCapacity (2 ^ (2 * R) + 1) ≤
      tailCapacity R + (2 : ℝ) ^ (1 - (R : ℝ)) := by
  apply alphaCapacity_le_tail_of_greedyCertificate R hR
  intro G hG
  exact greedyCertificate_of_edgeBudget R (tailCapacity R) G (hcert G hG)

end Erdos1016.Proof.FiniteAlphaBridge

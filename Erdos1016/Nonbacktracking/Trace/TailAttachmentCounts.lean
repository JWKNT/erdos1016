import Erdos1016.Nonbacktracking.Trace.SeamReduction

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Nonbacktracking

variable {G : PhysicalGraph}
local instance tailKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Dart choices that can be attached around a closed run while preserving
nonbacktracking at both attachment points. -/
abbrev ClosedRunAttachmentChoices (n : ℕ)
    (core : ClosedEndpointRuns (G := G) n) :=
  {d : Dart G // Next G d core.1.1 ∧
    Next G core.1.2.1 (reverse G d)}

/-- For a cyclically reduced core, the two core incidences at the attachment
vertex are distinct. A degree-three vertex therefore has at most one unused
incidence available for the first tail dart. -/
theorem closedRunAttachmentChoices_card_le_one
    (hmax : ∀ v, G.degree v ≤ 3) (n : ℕ)
    (core : ReducedClosedEndpointRuns (G := G) n) :
    Fintype.card (ClosedRunAttachmentChoices (G := G) n core.1) ≤ 1 := by
  classical
  let v := tail G core.1.1.1
  let c := core.1.1.1
  let e := core.1.1.2.1
  let r := reverse G e
  have hclosed : tail G c = head G e := core.1.2
  have hc : tail G c = v := rfl
  have hr : tail G r = v := by
    dsimp [r, v]
    rw [tail_reverse, hclosed]
  have hcr : c ≠ r := by
    intro h
    apply core.2
    have := congrArg (reverse G) h
    simpa [c, r] using this.symm
  let enc : (ClosedRunAttachmentChoices (G := G) n core.1 ⊕ Unit) ⊕ Unit →
      {x : Dart G // tail G x = v} := fun z =>
    match z with
    | Sum.inl (Sum.inl d) => ⟨reverse G d.1, by
        have h := d.2.1.1
        dsimp [v, c] at h
        simpa [head_reverse] using h⟩
    | Sum.inl (Sum.inr _) => ⟨c, hc⟩
    | Sum.inr _ => ⟨r, hr⟩
  have henc : Function.Injective enc := by
    intro x y h
    cases x with
    | inl x => cases x with
      | inl dx => cases y with
        | inl y => cases y with
          | inl dy =>
              have hrev : reverse G dx.1 = reverse G dy.1 := congrArg Subtype.val h
              have hd : dx.1 = dy.1 := (reverseEquiv G).injective hrev
              exact congrArg (fun z => Sum.inl (Sum.inl z)) (Subtype.ext hd)
          | inr _ =>
              have heq : reverse G dx.1 = c := congrArg Subtype.val h
              have hn := dx.2.1.2
              exact False.elim (hn (by simpa [c] using heq.symm))
        | inr _ =>
            have heq : reverse G dx.1 = r := congrArg Subtype.val h
            have hn := dx.2.2.2
            apply False.elim (hn (by simpa [r] using heq))
      | inr _ => cases y with
        | inl y => cases y with
          | inl dy =>
              have heq : c = reverse G dy.1 := congrArg Subtype.val h
              have hn := dy.2.1.2
              exact False.elim (hn (by simpa [c] using heq))
          | inr u => cases u; rfl
        | inr _ =>
            have heq : c = r := congrArg Subtype.val h
            exact False.elim (hcr heq)
    | inr _ => cases y with
      | inl y => cases y with
        | inl dy =>
            have heq : r = reverse G dy.1 := congrArg Subtype.val h
            have hn := dy.2.2.2
            apply False.elim (hn (by simpa [r] using heq.symm))
        | inr _ =>
            have heq : r = c := congrArg Subtype.val h
            exact False.elim (hcr heq.symm)
      | inr u => cases u; rfl
  have hcard := Fintype.card_le_of_injective enc henc
  have hsum : Fintype.card ((ClosedRunAttachmentChoices (G := G) n core.1 ⊕ Unit) ⊕ Unit) =
      Fintype.card (ClosedRunAttachmentChoices (G := G) n core.1) + 2 := by simp
  have hcard' : Fintype.card (ClosedRunAttachmentChoices (G := G) n core.1) + 2 ≤
      G.degree v := by
    calc
      _ = Fintype.card ((ClosedRunAttachmentChoices (G := G) n core.1 ⊕ Unit) ⊕ Unit) :=
        hsum.symm
      _ ≤ Fintype.card {x : Dart G // tail G x = v} := hcard
      _ = G.degree v := Proof.WalkPrefix.card_starting_darts G v
  have hdeg := hmax v
  have hbound : Fintype.card (ClosedRunAttachmentChoices (G := G) n core.1) + 2 ≤ 3 :=
    hcard'.trans hdeg
  have hbound' : Fintype.card (ClosedRunAttachmentChoices (G := G) n core.1) + 2 ≤ 1 + 2 := by
    simpa using hbound
  exact (Nat.add_le_add_iff_right).mp hbound'

/-- Without a reduced-core condition, an attachment still has at most two
choices, from the ordinary subcubic predecessor bound. -/
theorem closedRunAttachmentChoices_card_le_two
    (hmax : ∀ v, G.degree v ≤ 3) (n : ℕ)
    (core : ClosedEndpointRuns (G := G) n) :
    Fintype.card (ClosedRunAttachmentChoices (G := G) n core) ≤ 2 := by
  classical
  let f : ClosedRunAttachmentChoices (G := G) n core →
      {d : Dart G // Next G d core.1.1} := fun d => ⟨d.1, d.2.1⟩
  have hinj : Function.Injective f := by
    intro d e h
    apply Subtype.ext
    exact congrArg (fun x : {d : Dart G // Next G d core.1.1} => x.1) h
  exact le_trans (Fintype.card_le_of_injective _ hinj)
    (seamPredecessor_card_le_two (G := G) hmax core.1.1)

/-- Split a dependent sum over a finite proposition into its true and false
subfamilies. -/
def sigmaSubtypeSplit {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (F : α → Type*) :
    (Σ a : α, F a) ≃
      (Σ a : {a : α // P a}, F a.1) ⊕ (Σ a : {a : α // ¬ P a}, F a.1) := by
  classical
  refine
    { toFun := fun x => if h : P x.1 then Sum.inl ⟨⟨x.1, h⟩, x.2⟩
        else Sum.inr ⟨⟨x.1, h⟩, x.2⟩
      invFun := Sum.elim (fun x => ⟨x.1.1, x.2⟩) (fun x => ⟨x.1.1, x.2⟩)
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨a, b⟩
    by_cases h : P a <;> simp [h]
  · intro x
    rcases x with (⟨⟨a, h⟩, b⟩ | ⟨⟨a, h⟩, b⟩) <;> simp [h]

/-- One reversed endpoint seam is encoded by its stripped closed core and
the first attachment dart, with both endpoint transitions retained. -/
def seamTailChoiceEncoding (n : ℕ) : ClosedSeamRuns (G := G) n →
    Σ core : ClosedEndpointRuns (G := G) n,
      ClosedRunAttachmentChoices (G := G) n core
  | z => by
      let p := (seamClosedEquiv (G := G) n).symm z
      let raw := seamStrip n p.2
      let hc : tail G raw.1 = head G raw.2.1 :=
        seamStrip_preserves_closed_endpoints (G := G) n p.2
      exact ⟨⟨raw, hc⟩,
        ⟨p.1, seamStrip_boundary_steps (G := G) n p.2⟩⟩

theorem seamTailChoiceEncoding_injective (n : ℕ) :
    Function.Injective (seamTailChoiceEncoding (G := G) n) := by
  intro z w h
  have hcore : (seamTailChoiceEncoding (G := G) n z).1 =
      (seamTailChoiceEncoding (G := G) n w).1 := congrArg Sigma.fst h
  have hdart : (seamTailChoiceEncoding (G := G) n z).2.1 =
      (seamTailChoiceEncoding (G := G) n w).2.1 := congrArg (fun x => x.2.1) h
  let p := (seamClosedEquiv (G := G) n).symm z
  let q := (seamClosedEquiv (G := G) n).symm w
  have henc : seamCoreEncoding (G := G) n p = seamCoreEncoding (G := G) n q := by
    exact Sigma.ext hdart (heq_of_eq (congrArg Subtype.val hcore))
  have hpq : p = q := seamCoreEncoding_injective (G := G) n henc
  exact (seamClosedEquiv (G := G) n).symm.injective hpq

/-- The complement of the reduced-core subtype is exactly the reversed-seam
subtype. -/
def nonReducedClosedEquivSeamed (n : ℕ) :
    {core : ClosedEndpointRuns (G := G) n //
      ¬ core.1.2.1 ≠ reverse G core.1.1} ≃
    SeamedClosedEndpointRuns (G := G) n where
  toFun core := ⟨core.1, not_ne_iff.mp core.2⟩
  invFun core := ⟨core.1, not_ne_iff.mpr core.2⟩
  left_inv core := by apply Subtype.ext; rfl
  right_inv core := by apply Subtype.ext; rfl



/-- A bad endpoint seam strips into a closed core. It has one attachment
choice if that core is already cyclically reduced, and at most two choices if
the core still has a reversed seam. -/
theorem closedSeamRuns_card_le_reduced_add_twice_seamed (n : ℕ)
    (hmax : ∀ v, G.degree v ≤ 3) :
    Fintype.card (ClosedSeamRuns (G := G) n) ≤
      Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
        2 * Fintype.card (SeamedClosedEndpointRuns (G := G) n) := by
  classical
  let A := ClosedEndpointRuns (G := G) n
  let P : A → Prop := fun core => core.1.2.1 ≠ reverse G core.1.1
  let F : A → Type := fun core => ClosedRunAttachmentChoices (G := G) n core
  have hsplit : Fintype.card (Σ core : A, F core) =
      Fintype.card (Σ core : {core : A // P core}, F core.1) +
        Fintype.card (Σ core : {core : A // ¬ P core}, F core.1) := by
    have he := Fintype.card_congr (sigmaSubtypeSplit (α := A) P F)
    simpa using he
  have hgood : Fintype.card (Σ core : {core : A // P core}, F core.1) ≤
      Fintype.card {core : A // P core} := by
    rw [Fintype.card_sigma]
    calc
      (∑ core : {core : A // P core}, Fintype.card (F core.1)) ≤
          ∑ _core : {core : A // P core}, 1 := by
        apply Finset.sum_le_sum
        intro core _
        simpa [F] using closedRunAttachmentChoices_card_le_one (G := G)
          hmax n ⟨core.1, core.2⟩
      _ = Fintype.card {core : A // P core} := by simp
  have hbad : Fintype.card (Σ core : {core : A // ¬ P core}, F core.1) ≤
      2 * Fintype.card {core : A // ¬ P core} := by
    rw [Fintype.card_sigma]
    calc
      (∑ core : {core : A // ¬ P core}, Fintype.card (F core.1)) ≤
          ∑ _core : {core : A // ¬ P core}, 2 := by
        apply Finset.sum_le_sum
        intro core _
        simpa [F] using closedRunAttachmentChoices_card_le_two (G := G)
          hmax n core.1
      _ = 2 * Fintype.card {core : A // ¬ P core} := by simp [Nat.mul_comm]
  have hgood_eq : Fintype.card {core : A // P core} =
      Fintype.card (ReducedClosedEndpointRuns (G := G) n) := by
    rfl
  have hbad_eq : Fintype.card {core : A // ¬ P core} =
      Fintype.card (SeamedClosedEndpointRuns (G := G) n) :=
    Fintype.card_congr (nonReducedClosedEquivSeamed (G := G) n)
  calc
    Fintype.card (ClosedSeamRuns (G := G) n) ≤
        Fintype.card (Σ core : A, F core) :=
      Fintype.card_le_of_injective (seamTailChoiceEncoding (G := G) n)
        (seamTailChoiceEncoding_injective (G := G) n)
    _ = Fintype.card (Σ core : {core : A // P core}, F core.1) +
        Fintype.card (Σ core : {core : A // ¬ P core}, F core.1) := hsplit
    _ ≤ Fintype.card {core : A // P core} +
        2 * Fintype.card {core : A // ¬ P core} := Nat.add_le_add hgood hbad
    _ = Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
        2 * Fintype.card (SeamedClosedEndpointRuns (G := G) n) := by
      rw [hgood_eq, hbad_eq]

/-- Unnormalized tail-count kernel. The index `i` is the number of extra
reversed pairs beyond the core-facing attachment. -/
def reducedRunTailCount (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n / 2), 2 ^ i * R (n - 2 * (i + 1))

theorem reducedRunTailCount_succ_two (R : ℕ → ℕ) (n : ℕ) :
    reducedRunTailCount R (n + 2) = R n + 2 * reducedRunTailCount R n := by
  unfold reducedRunTailCount
  have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
  rw [hdiv, Finset.sum_range_succ']
  have hfirst : n + 2 - 2 * (0 + 1) = n := by omega
  rw [hfirst, pow_zero, one_mul]
  rw [Nat.add_comm]
  apply congrArg (fun x : ℕ => R n + x)
  calc
    (∑ i ∈ Finset.range (n / 2), 2 ^ (i + 1) *
        R (n + 2 - 2 * (i + 1 + 1))) =
      ∑ i ∈ Finset.range (n / 2), 2 * (2 ^ i * R (n - 2 * (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hidx : n + 2 - 2 * (i + 1 + 1) = n - 2 * (i + 1) := by omega
        rw [pow_succ, hidx]
        ring
    _ = 2 * (∑ i ∈ Finset.range (n / 2), 2 ^ i * R (n - 2 * (i + 1))) := by
      rw [Finset.mul_sum]

theorem seamedClosedEndpointRuns_card_zero :
    Fintype.card (SeamedClosedEndpointRuns (G := G) 0) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨?_⟩
  intro z
  exact (run_zero_seam_impossible (G := G) z.1.1.2.2) z.2

theorem seamedClosedEndpointRuns_card_one :
    Fintype.card (SeamedClosedEndpointRuns (G := G) 1) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨?_⟩
  intro z
  exact (run_one_seam_impossible (G := G) z.1.1.2.2) z.2

/-- Iterating the split one-seam estimate yields the source's exact
`2^(j-1)` tail multiplicity before normalization. -/
theorem seamedClosedEndpointRuns_card_le_reducedRunTailCount
    (hmax : ∀ v, G.degree v ≤ 3) :
    ∀ n, Fintype.card (SeamedClosedEndpointRuns (G := G) n) ≤
      reducedRunTailCount (fun k => Fintype.card (ReducedClosedEndpointRuns (G := G) k)) n := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          simp [seamedClosedEndpointRuns_card_zero, reducedRunTailCount]
      | succ k =>
          cases k with
          | zero =>
              simp [seamedClosedEndpointRuns_card_one, reducedRunTailCount]
          | succ n =>
              have hrec := closedSeamRuns_card_le_reduced_add_twice_seamed
                (G := G) n hmax
              have hsmall := ih n (by omega)
              rw [reducedRunTailCount_succ_two]
              calc
                Fintype.card (SeamedClosedEndpointRuns (G := G) (n + 2)) ≤
                    Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
                      2 * Fintype.card (SeamedClosedEndpointRuns (G := G) n) := hrec
                _ ≤ Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
                      2 * reducedRunTailCount
                        (fun k => Fintype.card (ReducedClosedEndpointRuns (G := G) k)) n :=
                  Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsmall) _

/-- Count ordinary closed endpoint runs by cyclically reduced cores with the
source tail coefficients. -/
theorem closedEndpointRuns_card_le_reducedRunTailCount
    (hmax : ∀ v, G.degree v ≤ 3) (n : ℕ) :
    Fintype.card (ClosedEndpointRuns (G := G) n) ≤
      Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
        reducedRunTailCount
          (fun k => Fintype.card (ReducedClosedEndpointRuns (G := G) k)) n := by
  calc
    Fintype.card (ClosedEndpointRuns (G := G) n) ≤
        Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
          Fintype.card (SeamedClosedEndpointRuns (G := G) n) :=
      closedEndpointRuns_card_le_reduced_add_seamed (G := G) n
    _ ≤ Fintype.card (ReducedClosedEndpointRuns (G := G) n) +
          reducedRunTailCount
            (fun k => Fintype.card (ReducedClosedEndpointRuns (G := G) k)) n :=
      Nat.add_le_add_left
        (seamedClosedEndpointRuns_card_le_reducedRunTailCount (G := G) hmax n) _

end Erdos1016.Nonbacktracking
end

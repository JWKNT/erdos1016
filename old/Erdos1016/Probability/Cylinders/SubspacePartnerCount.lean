import Mathlib

set_option autoImplicit false

/-!
# Counting exceptional partners by pair encodings

The graphical cylinder argument assigns a two-dimensional common plane in a
fixed cut-coordinate space to each exceptional partner.  Triple-intersection
control makes these planes distinct.  This file isolates the finite counting
step: an injective encoding of partners by ordered pairs in a space of size at
most `2^d` gives at most `2^(2d)` partners.
-/

namespace Erdos1016.Proof.PartnerCounting



/-- The number of elements in a finite-dimensional binary subspace is
`2^dimension`, so a dimension bound supplies the size bound needed above. -/
theorem subspace_card_le_pow_dim
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Fintype W]
    (S : Submodule (ZMod 2) W) [Fintype S]
    (d : ℕ) (hS : Module.finrank (ZMod 2) S ≤ d) :
    Fintype.card S ≤ 2 ^ d := by
  have hc : Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
    simpa [Nat.card_eq_fintype_card] using h
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hS

abbrev F₂ := ZMod 2

/-- The type of all two-dimensional subspaces contained in `S`. -/
def PlanesIn {W : Type*} [AddCommGroup W] [Module F₂ W]
    (S : Submodule F₂ W) :=
  {P : Submodule F₂ W // P ≤ S ∧ Module.finrank F₂ P = 2}

def PairIntersection {W : Type*} [AddCommGroup W] [Module F₂ W]
    (S T : Submodule F₂ W) : Submodule F₂ W := S ⊓ T

def TripleIntersection {W : Type*} [AddCommGroup W] [Module F₂ W]
    (S T U : Submodule F₂ W) : Submodule F₂ W := PairIntersection S T ⊓ U

noncomputable instance planesInFintype
    {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
    (S : Submodule F₂ W) : Fintype (PlanesIn S) := by
  classical
  letI : Fintype (Submodule F₂ W) := inferInstance
  letI : DecidablePred (fun P : Submodule F₂ W =>
      P ≤ S ∧ Module.finrank F₂ P = 2) := Classical.decPred _
  change Fintype {P : Submodule F₂ W // P ≤ S ∧ Module.finrank F₂ P = 2}
  exact Fintype.subtype
    (Finset.univ.filter (fun P : Submodule F₂ W => P ≤ S ∧ Module.finrank F₂ P = 2))
    (by simp)

/-- The plane selected for partner `i`, viewed as a plane in the fixed space `S`. -/
def selectedPlane {W ι : Type*} [AddCommGroup W] [Module F₂ W]
    (S : Submodule F₂ W) (T : ι → Submodule F₂ W) (E : ι → Prop)
    [DecidablePred E] (P : {i : ι // E i} → Submodule F₂ W)
    (hPdim : ∀ i, Module.finrank F₂ (P i) = 2)
    (hPbelow : ∀ i, P i ≤ S ⊓ T i.1)
    (i : {i : ι // E i}) : PlanesIn S := by
  classical
  refine ⟨P i, ?_, ?_⟩
  · exact (hPbelow i).trans inf_le_left
  · exact hPdim i

/-- Selected common planes for distinct partners are distinct.  Equality would
put a two-dimensional space inside the triple intersection. -/
theorem selected_planes_injective
    {W ι : Type*} [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W]
    [Fintype W] [Fintype ι]
    (S : Submodule F₂ W) (T : ι → Submodule F₂ W)
    (E : ι → Prop) [DecidablePred E]
    (P : {i : ι // E i} → Submodule F₂ W)
    (hPdim : ∀ i, Module.finrank F₂ (P i) = 2)
    (hPbelow : ∀ i, P i ≤ S ⊓ T i.1)
    (htriple : ∀ (i j : {i : ι // E i}), i.val ≠ j.val →
      Module.finrank F₂ (TripleIntersection S (T i.val) (T j.val)) ≤ 1) :
    Function.Injective (selectedPlane S T E P hPdim hPbelow) := by
  intro i j hij
  by_cases hval : i.val = j.val
  · apply Subtype.ext
    exact hval
  have hpEq : P i = P j := congrArg (fun q : PlanesIn S => q.1) hij
  have hPtoJ : P i ≤ T j.1 := by
    have h := hpEq ▸ hPbelow j
    exact le_trans h inf_le_right
  have hPtoTriple : P i ≤ TripleIntersection S (T i.val) (T j.val) := by
    exact le_inf (hPbelow i) hPtoJ
  have hmono := Submodule.finrank_mono hPtoTriple
  have hupper := htriple i j hval
  rw [hPdim i] at hmono
  omega

/-- The actual partner set injects into the set of planes in `S`, so its
cardinality is at most the number of such planes. -/
theorem exceptional_partners_le_number_of_planes
    {W ι : Type*} [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W]
    [Fintype W] [Fintype ι]
    (S : Submodule F₂ W) (T : ι → Submodule F₂ W)
    (E : ι → Prop) [DecidablePred E]
    (P : {i : ι // E i} → Submodule F₂ W)
    (hPdim : ∀ i, Module.finrank F₂ (P i) = 2)
    (hPbelow : ∀ i, P i ≤ S ⊓ T i.1)
    (htriple : ∀ (i j : {i : ι // E i}), i.val ≠ j.val →
      Module.finrank F₂ (TripleIntersection S (T i.val) (T j.val)) ≤ 1) :
    Fintype.card {i : ι // E i} ≤ Fintype.card (PlanesIn S) := by
  classical
  exact Fintype.card_le_of_injective (selectedPlane S T E P hPdim hPbelow)
    (selected_planes_injective S T E P hPdim hPbelow htriple)

/-- A chosen ordered independent pair spanning each plane, obtained from its
two-dimensional rank. -/
noncomputable def planeBasis {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] (S : Submodule F₂ W) (P : PlanesIn S) :
    {v : Fin 2 → P.1 // LinearIndependent F₂ v} := by
  let h := exists_linearIndependent_of_le_finrank
    (R := F₂) (M := P.1) (n := 2) (by rw [P.2.2])
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def planePair {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] (S : Submodule F₂ W) (P : PlanesIn S) : S × S :=
  (⟨((planeBasis S P).1 0 : P.1), P.2.1 ((planeBasis S P).1 0).2⟩,
   ⟨((planeBasis S P).1 1 : P.1), P.2.1 ((planeBasis S P).1 1).2⟩)

theorem plane_eq_span_basisPair {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] (S : Submodule F₂ W) (P : PlanesIn S) :
    P.1 = Submodule.span F₂ (Set.range (fun i : Fin 2 =>
      ((planeBasis S P).1 i : W))) := by
  let v : Fin 2 → P.1 := (planeBasis S P).1
  have hv : LinearIndependent F₂ (fun i => (v i : W)) :=
    (planeBasis S P).2.map' P.1.subtype P.1.ker_subtype
  have hspan : Module.finrank F₂
      (Submodule.span F₂ (Set.range (fun i : Fin 2 => (v i : W)))) = 2 := by
    simpa using (finrank_span_eq_card hv)
  have hle : Submodule.span F₂ (Set.range (fun i : Fin 2 => (v i : W))) ≤ P.1 :=
    Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact (v i).2)
  have hdim : Module.finrank F₂
      (Submodule.span F₂ (Set.range (fun i : Fin 2 => (v i : W)))) =
        Module.finrank F₂ P.1 := by
    rw [hspan, P.2.2]
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

/-- In a binary space of dimension at most `d`, the number of two-planes is
at most the number of ordered pairs of vectors, hence at most `2^(2d)`. -/
theorem number_of_planes_le_two_pow_two_mul
    {W : Type*} [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W]
    [Fintype W] (S : Submodule F₂ W) (d : ℕ)
    (hS : Module.finrank F₂ S ≤ d) :
    Fintype.card (PlanesIn S) ≤ 2 ^ (2 * d) := by
  classical
  have henc : Function.Injective (planePair S) := by
    intro P Q hpq
    have h0 : ((planeBasis S P).1 0 : W) = ((planeBasis S Q).1 0 : W) := by
      have h := congrArg (fun z : S => (z : W)) (congrArg Prod.fst hpq)
      simpa [planePair] using h
    have h1 : ((planeBasis S P).1 1 : W) = ((planeBasis S Q).1 1 : W) := by
      have h := congrArg (fun z : S => (z : W)) (congrArg Prod.snd hpq)
      simpa [planePair] using h
    have hvec : (fun i : Fin 2 => ((planeBasis S P).1 i : W)) =
        (fun i : Fin 2 => ((planeBasis S Q).1 i : W)) := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hrange : Set.range (fun i : Fin 2 => ((planeBasis S P).1 i : W)) =
        Set.range (fun i : Fin 2 => ((planeBasis S Q).1 i : W)) := by
      rw [hvec]
    have hrange' := congrArg (Submodule.span F₂) hrange
    have hp : P.1 = Q.1 := by
      calc
        P.1 = Submodule.span F₂ (Set.range (fun i : Fin 2 =>
            ((planeBasis S P).1 i : W))) := plane_eq_span_basisPair S P
        _ = Submodule.span F₂ (Set.range (fun i : Fin 2 =>
            ((planeBasis S Q).1 i : W))) := hrange'
        _ = Q.1 := (plane_eq_span_basisPair S Q).symm
    apply Subtype.ext
    exact hp
  have hcardS : Fintype.card S ≤ 2 ^ d := subspace_card_le_pow_dim S d hS
  calc
    Fintype.card (PlanesIn S) ≤ Fintype.card (S × S) :=
      Fintype.card_le_of_injective (planePair S) henc
    _ = Fintype.card S * Fintype.card S := by simp
    _ ≤ 2 ^ d * 2 ^ d := Nat.mul_le_mul hcardS hcardS
    _ = 2 ^ (2 * d) := by rw [← pow_add]; congr 1; omega

end Erdos1016.Proof.PartnerCounting

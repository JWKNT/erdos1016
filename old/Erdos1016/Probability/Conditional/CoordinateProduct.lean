import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ManyRegionsFiberDecomposition

open Erdos1016

local notation "𝔽" => F₂

variable {E ι O : Type*} {B : ι → Type*}
  [Fintype E] [Fintype ι] [∀ i, Fintype (B i)] [Fintype O]

def splitWord (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (x : E → 𝔽) : (O → 𝔽) × ((i : ι) → B i → 𝔽) :=
  (fun o => x (edgeDecomposition.symm (Sum.inl o)),
    fun i b => x (edgeDecomposition.symm (Sum.inr ⟨i, b⟩)))

def glueWord (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (z : (O → 𝔽) × ((i : ι) → B i → 𝔽)) : E → 𝔽 := fun e =>
  match edgeDecomposition e with
  | Sum.inl o => z.1 o
  | Sum.inr ⟨i, b⟩ => z.2 i b

private theorem glue_split (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (x : E → 𝔽) : glueWord edgeDecomposition (splitWord edgeDecomposition x) = x := by
  funext e
  cases h : edgeDecomposition e with
  | inl o =>
      simp only [glueWord, h]
      have he : edgeDecomposition.symm (Sum.inl o) = e := by
        apply edgeDecomposition.injective
        simpa using h.symm
      exact congrArg x he
  | inr ib =>
      simp only [glueWord, h]
      have he : edgeDecomposition.symm (Sum.inr ib) = e := by
        apply edgeDecomposition.injective
        simpa using h.symm
      rcases ib with ⟨i, b⟩
      exact congrArg x he

private theorem split_glue (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (z : (O → 𝔽) × ((i : ι) → B i → 𝔽)) :
    splitWord edgeDecomposition (glueWord edgeDecomposition z) = z := by
  apply Prod.ext
  · funext o
    simp [splitWord, glueWord]
  · funext i b
    simp [splitWord, glueWord]

noncomputable def splitEquiv
    (edgeDecomposition : E ≃ (O ⊕ Σ i, B i)) :
    (E → 𝔽) ≃ ((O → 𝔽) × ((i : ι) → B i → 𝔽)) where
  toFun := splitWord edgeDecomposition
  invFun := glueWord edgeDecomposition
  left_inv := glue_split edgeDecomposition
  right_inv := split_glue edgeDecomposition

/-- The fiber of feasible global words above one fixed outside word is the
Cartesian product of the region completion sets, provided feasibility splits
into an outside condition and independent local conditions. -/
def globalFiber (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (feasible : (E → 𝔽) → Prop) (outside : O → 𝔽) :=
  {x : E → 𝔽 // feasible x ∧
    (splitEquiv edgeDecomposition x).1 = outside}

def localProductFiber (feasibleOutside : (O → 𝔽) → Prop)
    (localFeasible : (i : ι) → (O → 𝔽) → (B i → 𝔽) → Prop)
    (outside : O → 𝔽) :=
  {z : (i : ι) → B i → 𝔽 //
    feasibleOutside outside ∧ ∀ i, localFeasible i outside (z i)}

noncomputable def globalFiber_equiv_localProductFiber
    (edgeDecomposition : E ≃ (O ⊕ Σ i, B i))
    (feasible : (E → 𝔽) → Prop)
    (feasibleOutside : (O → 𝔽) → Prop)
    (localFeasible : (i : ι) → (O → 𝔽) → (B i → 𝔽) → Prop)
    (hfactor : ∀ x, feasible x ↔
      feasibleOutside (splitEquiv edgeDecomposition x).1 ∧
        ∀ i, localFeasible i (splitEquiv edgeDecomposition x).1
          ((splitEquiv edgeDecomposition x).2 i))
    (outside : O → 𝔽) :
    globalFiber edgeDecomposition feasible outside ≃
      localProductFiber feasibleOutside localFeasible outside where
  toFun x := by
    let s := splitEquiv edgeDecomposition x.1
    refine ⟨s.2, ?_⟩
    have hf := (hfactor x.1).1 x.2.1
    exact ⟨x.2.2 ▸ hf.1, fun i => x.2.2 ▸ hf.2 i⟩
  invFun z := by
    let x := (splitEquiv edgeDecomposition).symm (outside, z.1)
    have hs : splitEquiv edgeDecomposition x = (outside, z.1) :=
      (splitEquiv edgeDecomposition).right_inv (outside, z.1)
    refine ⟨x, ?_⟩
    constructor
    · apply (hfactor x).2
      rw [hs]
      exact z.2
    · exact congrArg Prod.fst hs
  left_inv x := by
    apply Subtype.ext
    change (splitEquiv edgeDecomposition).symm
      (outside, (splitEquiv edgeDecomposition x.1).2) = x.1
    have hout : (splitEquiv edgeDecomposition x.1).1 = outside := x.2.2
    have hp : (outside, (splitEquiv edgeDecomposition x.1).2) =
        splitEquiv edgeDecomposition x.1 := Prod.ext hout.symm rfl
    calc
      _ = (splitEquiv edgeDecomposition).symm
          (splitEquiv edgeDecomposition x.1) := congrArg
            (splitEquiv edgeDecomposition).symm hp
      _ = x.1 := (splitEquiv edgeDecomposition).left_inv x.1
  right_inv z := by
    apply Subtype.ext
    change ((splitEquiv edgeDecomposition)
      ((splitEquiv edgeDecomposition).symm (outside, z.1))).2 = z.1
    exact congrArg Prod.snd ((splitEquiv edgeDecomposition).right_inv
      (outside, z.1))







end Erdos1016.Proof.ManyRegionsFiberDecomposition

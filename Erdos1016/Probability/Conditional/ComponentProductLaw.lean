import Erdos1016.Extremal.Capacity.CompositionProbability

set_option autoImplicit false

/-!
# Product law for componentwise events

The graph-specific component decomposition is still to be constructed.  This
module isolates the finite probability calculation it must provide: a
bijection from the global state space to a product of component state spaces,
under which the event is the intersection of local events.
-/

noncomputable section

namespace Erdos1016.Proof.ActiveComponentProbability

open scoped BigOperators

/-- Uniform density on a finite state space. -/
noncomputable def density {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact (Fintype.card {x : Ω // P x} : ℝ) / Fintype.card Ω

/-- A product-space event has exactly the product of its component densities.
The equivalence is the exact algebraic decomposition needed from an active
component construction. -/
theorem density_eq_prod_of_equiv
    {Ω : Type*} [Fintype Ω]
    {ι : Type*} [Fintype ι]
    (α : ι → Type*) (inst : ∀ i, Fintype (α i))
    (e : Ω ≃ ((i : ι) → α i))
    (P : Ω → Prop) (Q : ∀ i, α i → Prop)
    (hP : ∀ x, P x ↔ ∀ i, Q i (e x i)) :
    density P = ∏ i, density (Q i) := by
  classical
  letI : ∀ i, Fintype (α i) := inst
  letI : DecidablePred P := Classical.decPred P
  letI : ∀ i, DecidablePred (Q i) := fun i => Classical.decPred (Q i)
  let toFun : {x : Ω // P x} → ((i : ι) → {a : α i // Q i a}) :=
    fun x i => ⟨e x.1 i, (hP x.1).mp x.2 i⟩
  let invFun : ((i : ι) → {a : α i // Q i a}) → {x : Ω // P x} :=
    fun x => by
      let y : Ω := e.symm (fun i => (x i).1)
      have heval (i : ι) : e y i = (x i).1 := by simp [y]
      exact ⟨y, (hP y).mpr (fun i => heval i ▸ (x i).2)⟩
  have hleft (x : {x : Ω // P x}) : invFun (toFun x) = x := by
    apply Subtype.ext
    dsimp [invFun, toFun]
    simp
  have hright (x : (i : ι) → {a : α i // Q i a}) : toFun (invFun x) = x := by
    funext i
    apply Subtype.ext
    dsimp [invFun, toFun]
    simp
  let localEquiv : {x : Ω // P x} ≃ ((i : ι) → {a : α i // Q i a}) :=
    Equiv.ofBijective toFun ⟨
      (fun a b hab => by
        calc
          a = invFun (toFun a) := (hleft a).symm
          _ = invFun (toFun b) := congrArg invFun hab
          _ = b := hleft b),
      (fun b => ⟨invFun b, hright b⟩)⟩
  have hnum : Fintype.card {x : Ω // P x} =
      ∏ i, Fintype.card {a : α i // Q i a} := by
    calc
      _ = Fintype.card ((i : ι) → {a : α i // Q i a}) :=
        Fintype.card_congr localEquiv
      _ = ∏ i, Fintype.card {a : α i // Q i a} := by simp
  have hden : Fintype.card Ω = ∏ i, Fintype.card (α i) := by
    calc
      _ = Fintype.card ((i : ι) → α i) := Fintype.card_congr e
      _ = ∏ i, Fintype.card (α i) := by simp
  have hnumR : (Fintype.card {x : Ω // P x} : ℝ) =
      ∏ i, (Fintype.card {a : α i // Q i a} : ℝ) := by exact_mod_cast hnum
  have hdenR : (Fintype.card Ω : ℝ) =
      ∏ i, (Fintype.card (α i) : ℝ) := by exact_mod_cast hden
  unfold density
  change (Fintype.card {x : Ω // P x} : ℝ) / (Fintype.card Ω : ℝ) =
    ∏ i, (Fintype.card {a : α i // Q i a} : ℝ) /
      (Fintype.card (α i) : ℝ)
  rw [hnumR, hdenR, Finset.prod_div_distrib]

/-- A product of probabilities is at most each factor when every other
factor lies in `[0,1]`. -/
theorem prod_le_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i₀ : ι) : (∏ i, p i) ≤ p i₀ := by
  classical
  rw [← Finset.mul_prod_erase (s := Finset.univ) (f := p)
    (Finset.mem_univ i₀)]
  have hrest : 0 ≤ ∏ i ∈ Finset.univ.erase i₀, p i :=
    Finset.prod_nonneg fun i hi => hp0 i
  have hrest1 : ∏ i ∈ Finset.univ.erase i₀, p i ≤ 1 :=
    Finset.prod_le_one (fun i hi => hp0 i) (fun i hi => hp1 i)
  nlinarith [mul_le_mul_of_nonneg_left hrest1 (hp0 i₀)]



/-- A factored global density strictly above `q > 1/2` forces every local
component density to exceed one half. -/
theorem component_gt_half_of_prod_gt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hglobal : (1 / 2 : ℝ) < ∏ i, p i) :
    ∀ i, (1 / 2 : ℝ) < p i := by
  intro i
  have hle := prod_le_factor p hp0 hp1 i
  linarith



end Erdos1016.Proof.ActiveComponentProbability

end

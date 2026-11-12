import Erdos1016.ExactMaximum.NetCircuits

set_option autoImplicit false

/-!
# Cycles and paths of a part of a network

Let `p` be a set of edges of a network `N`. The network `N.sub p` has the same vertices and the
edges that satisfy `p`. A word of `N.sub p`, extended by zero, is a word of `N` within `p`.

This file proves that the extension keeps degrees and the selected graph. So a word of the part
is a cycle (a path from `s` to `t`) if and only if its extension is one, and

* the number of cycles of `N.sub p` is the number of cycles of `N` within `p` (`numCycles_sub`);
* the number of paths of `N.sub p` from `s` to `t` is the number of paths of `N` from `s` to `t`
  within `p` (`numPaths_sub`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Words within a set of edges -/

/-- Every edge of `x` satisfies `p`. -/
def Within (x : E → Bit) (p : E → Prop) : Prop := ∀ e, x e ≠ 0 → p e

omit [Fintype E] in
theorem within_extend (p : E → Prop) (y : {e : E // p e} → Bit) : Within (extend p y) p :=
  fun _ he => prop_of_extend_ne_zero p y he

omit [Fintype E] in
theorem within_restrict (x : E → Bit) (p : E → Prop) : Within (restrict x p) p :=
  fun e he => ((restrict_ne_zero_iff x p e).1 he).1

omit [Fintype E] in
/-- A word within `p` is zero at an edge that does not satisfy `p`. -/
theorem Within.eq_zero {x : E → Bit} {p : E → Prop} (h : Within x p) {e : E} (he : ¬ p e) :
    x e = 0 :=
  Classical.not_not.1 fun hne => he (h e hne)

omit [Fintype V] [Fintype E] in
/-- A sub-word of a word within `p` is within `p`. -/
theorem Within.of_isSubword {N : Network V E} {x y : N.Word} {p : E → Prop} (h : Within x p)
    (hsub : N.IsSubword y x) : Within y p := fun e he => h e (hsub e he)

/-- The word of the part that agrees with `x` on the edges that satisfy `p`. -/
def pull (p : E → Prop) (x : E → Bit) : {e : E // p e} → Bit := fun e => x e.1

omit [Fintype E] in
theorem pull_extend (p : E → Prop) (y : {e : E // p e} → Bit) : pull p (extend p y) = y := by
  funext e
  exact extend_apply_of_pos p y e.2

omit [Fintype E] in
theorem extend_pull (p : E → Prop) {x : E → Bit} (h : Within x p) :
    extend p (pull p x) = x := by
  funext e
  by_cases hp : p e
  · exact extend_apply_of_pos p _ hp
  · rw [extend_apply_of_neg p _ hp]
    exact (h.eq_zero hp).symm

omit [Fintype E] in
theorem extend_injective (p : E → Prop) :
    Function.Injective (extend p : ({e : E // p e} → Bit) → E → Bit) := by
  intro y y' h
  rw [← pull_extend p y, ← pull_extend p y', h]

omit [Fintype E] in
theorem extend_zero (p : E → Prop) : extend p (0 : {e : E // p e} → Bit) = 0 := by
  funext e
  by_cases hp : p e
  · rw [extend_apply_of_pos p _ hp]
    rfl
  · rw [extend_apply_of_neg p _ hp]
    rfl

omit [Fintype E] in
theorem extend_ne_zero_iff (p : E → Prop) (y : {e : E // p e} → Bit) :
    extend p y ≠ 0 ↔ y ≠ 0 := by
  constructor
  · intro h hy
    apply h
    rw [hy, extend_zero]
  · intro h hy
    apply h
    apply extend_injective p
    rw [hy, extend_zero]

/-! ### Degrees and the selected graph -/

omit [Fintype V] in
/-- The extension by zero keeps the degrees. -/
theorem deg_extend (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (y : {e : E // p e} → Bit) (v : V) :
    N.deg (extend p y) v = (N.sub p).deg y v := by
  rw [deg_eq_sum, deg_eq_sum,
    sum_eq_sum_sub p (fun e => if extend p y e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v) then 1 else 0)]
  · apply Finset.sum_congr rfl
    intro e _
    show (if extend p y e.1 ≠ 0 ∧ (N.src e.1 = v ∨ N.dst e.1 = v) then 1 else 0) =
      if y e ≠ 0 ∧ (N.src e.1 = v ∨ N.dst e.1 = v) then 1 else 0
    rw [extend_apply_of_pos p y e.2]
  · intro e he
    rw [extend_apply_of_neg p y he]
    simp

omit [Fintype V] [Fintype E] in
/-- The extension by zero keeps the selected graph. -/
theorem selectedGraph_extend (N : Network V E) (p : E → Prop) (y : {e : E // p e} → Bit) :
    N.selectedGraph (extend p y) = (N.sub p).selectedGraph y := by
  ext u w
  constructor
  · rintro ⟨e, he, h⟩
    have hp := prop_of_extend_ne_zero p y he
    refine ⟨⟨e, hp⟩, ?_, h⟩
    rw [← extend_apply_of_pos p y hp]
    exact he
  · rintro ⟨e, he, h⟩
    refine ⟨e.1, ?_, h⟩
    rw [extend_apply_of_pos p y e.2]
    exact he

/-! ### Cycles and paths -/

omit [Fintype V] in
/-- A word of the part is a cycle if and only if its extension is a cycle. -/
theorem isCycleWord_extend_iff (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (y : {e : E // p e} → Bit) :
    N.IsCycleWord (extend p y) ↔ (N.sub p).IsCycleWord y := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(extend_ne_zero_iff p y).1 h1, fun v => ?_, fun u v hu hv => ?_⟩
    · rw [← N.deg_extend p y v]
      exact h2 v
    · rw [← N.selectedGraph_extend p y]
      apply h3 u v
      · rw [N.deg_extend p y u]
        exact hu
      · rw [N.deg_extend p y v]
        exact hv
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(extend_ne_zero_iff p y).2 h1, fun v => ?_, fun u v hu hv => ?_⟩
    · rw [N.deg_extend p y v]
      exact h2 v
    · rw [N.selectedGraph_extend p y]
      apply h3 u v
      · rw [← N.deg_extend p y u]
        exact hu
      · rw [← N.deg_extend p y v]
        exact hv

omit [Fintype V] in
/-- A word of the part is a path from `s` to `t` if and only if its extension is one. -/
theorem isPathWord_extend_iff (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (s t : V) (y : {e : E // p e} → Bit) :
    N.IsPathWord s t (extend p y) ↔ (N.sub p).IsPathWord s t y := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨h0, ?_, ?_, fun v hvs hvt => ?_, fun v hv => ?_⟩
    · rw [← N.deg_extend p y s]
      exact h1
    · rw [← N.deg_extend p y t]
      exact h2
    · rw [← N.deg_extend p y v]
      exact h3 v hvs hvt
    · rw [← N.selectedGraph_extend p y]
      apply h4 v
      rw [N.deg_extend p y v]
      exact hv
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨h0, ?_, ?_, fun v hvs hvt => ?_, fun v hv => ?_⟩
    · rw [N.deg_extend p y s]
      exact h1
    · rw [N.deg_extend p y t]
      exact h2
    · rw [N.deg_extend p y v]
      exact h3 v hvs hvt
    · rw [N.selectedGraph_extend p y]
      apply h4 v
      rw [← N.deg_extend p y v]
      exact hv

omit [Fintype V] in
/-- **The cycles of a part.** The number of cycles of `N.sub p` is the number of cycles of `N`
within `p`. -/
theorem numCycles_sub (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}] :
    (N.sub p).numCycles = Nat.card {x : N.Word // N.IsCycleWord x ∧ Within x p} := by
  let f : {y : (N.sub p).Word // (N.sub p).IsCycleWord y} →
      {x : N.Word // N.IsCycleWord x ∧ Within x p} := fun y =>
    ⟨extend p y.1, (N.isCycleWord_extend_iff p y.1).2 y.2, within_extend p y.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val h
      exact Subtype.ext (extend_injective p h')
    · rintro ⟨x, hx, hw⟩
      refine ⟨⟨pull p x, ?_⟩, ?_⟩
      · rw [← N.isCycleWord_extend_iff p, extend_pull p hw]
        exact hx
      · exact Subtype.ext (extend_pull p hw)
  exact Nat.card_eq_of_bijective f hf

omit [Fintype V] in
/-- **The paths of a part.** The number of paths of `N.sub p` from `s` to `t` is the number of
paths of `N` from `s` to `t` within `p`. -/
theorem numPaths_sub (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}] (s t : V) :
    (N.sub p).numPaths s t = Nat.card {x : N.Word // N.IsPathWord s t x ∧ Within x p} := by
  let f : {y : (N.sub p).Word // (N.sub p).IsPathWord s t y} →
      {x : N.Word // N.IsPathWord s t x ∧ Within x p} := fun y =>
    ⟨extend p y.1, (N.isPathWord_extend_iff p s t y.1).2 y.2, within_extend p y.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h' : (f a).1 = (f b).1 := congrArg Subtype.val h
      exact Subtype.ext (extend_injective p h')
    · rintro ⟨x, hx, hw⟩
      refine ⟨⟨pull p x, ?_⟩, ?_⟩
      · rw [← N.isPathWord_extend_iff p, extend_pull p hw]
        exact hx
      · exact Subtype.ext (extend_pull p hw)
  exact Nat.card_eq_of_bijective f hf

end Erdos1016.BoundaryTrace.Network

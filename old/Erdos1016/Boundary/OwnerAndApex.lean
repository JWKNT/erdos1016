import Erdos1016.Boundary.ParitySpace

set_option autoImplicit false

/-!
# Literal owner and one-apex networks

The joint linear state space is identified with the complete cycle space of
an ACTUAL labelled graph. The apex identifies exterior vertices only; it
retains every internal edge and every cut-edge label separately.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace Ported

variable {U V EI EO P : Type*}
  [Fintype U] [Fintype V] [Fintype EI] [Fintype EO] [Fintype P]
  {I : Network U EI} {O : Network V EO}

/-- The original graph reconstructed with individually labelled inside,
cut, and outside edges. -/
def owner (L : Ported I O P) : Network (U ⊕ V) ((EI ⊕ P) ⊕ EO) where
  src := Sum.elim (Sum.elim (Sum.inl ∘ I.src) (Sum.inl ∘ L.inside)) (Sum.inr ∘ O.src)
  dst := Sum.elim (Sum.elim (Sum.inl ∘ I.dst) (Sum.inr ∘ L.outside)) (Sum.inr ∘ O.dst)
  noLoops := by
    intro e
    rcases e with (e | p) | e
    · exact fun h => I.noLoops e (Sum.inl.inj h)
    · exact fun h => Sum.noConfusion h
    · exact fun h => O.noLoops e (Sum.inr.inj h)

/-- Replace the entire exterior by ONE apex, without discarding cut labels. -/
def apex (L : Ported I O P) : Network (U ⊕ Unit) (EI ⊕ P) where
  src := Sum.elim (Sum.inl ∘ I.src) (Sum.inl ∘ L.inside)
  dst := Sum.elim (Sum.inl ∘ I.dst) (fun _ => Sum.inr ())
  noLoops := by
    intro e
    rcases e with e | p
    · exact fun h => I.noLoops e (Sum.inl.inj h)
    · exact fun h => Sum.noConfusion h

def ownerWordEquiv (L : Ported I O P) : L.owner.Word ≃ L.FullWord where
  toFun w := ((fun e => w (Sum.inl (Sum.inl e)),
    fun p => w (Sum.inl (Sum.inr p))), fun e => w (Sum.inr e))
  invFun w := Sum.elim (Sum.elim w.1.1 w.1.2) w.2
  left_inv w := by
    funext e
    rcases e with (e | p) | e <;> rfl
  right_inv w := by
    rcases w with ⟨⟨x, y⟩, z⟩
    rfl

def apexWordEquiv (L : Ported I O P) : L.apex.Word ≃ L.LocalWord where
  toFun w := (fun e => w (Sum.inl e), fun p => w (Sum.inr p))
  invFun w := Sum.elim w.1 w.2
  left_inv w := by funext e; cases e <;> rfl
  right_inv w := by rcases w with ⟨x, y⟩; rfl

@[simp] theorem owner_boundary_inside (L : Ported I O P)
    (w : L.owner.Word) (u : U) :
    L.owner.boundary w (Sum.inl u) =
      L.localBoundary (L.ownerWordEquiv w).1 u := by
  simp [owner, ownerWordEquiv, localBoundary, Network.boundary_apply,
    Fintype.sum_sum_type, push_apply, add_assoc, add_left_comm, add_comm]

@[simp] theorem owner_boundary_outside (L : Ported I O P)
    (w : L.owner.Word) (v : V) :
    L.owner.boundary w (Sum.inr v) =
      O.boundary (L.ownerWordEquiv w).2 v +
        push L.outside (L.ownerWordEquiv w).1.2 v := by
  simp [owner, ownerWordEquiv, Network.boundary_apply,
    Fintype.sum_sum_type, push_apply, add_assoc, add_left_comm, add_comm]

@[simp] theorem apex_boundary_inside (L : Ported I O P)
    (w : L.apex.Word) (u : U) :
    L.apex.boundary w (Sum.inl u) = L.localBoundary (L.apexWordEquiv w) u := by
  simp [apex, apexWordEquiv, localBoundary, Network.boundary_apply,
    Fintype.sum_sum_type, push_apply, add_assoc, add_left_comm, add_comm]

@[simp] theorem apex_boundary_apex (L : Ported I O P) (w : L.apex.Word) :
    L.apex.boundary w (Sum.inr ()) = total (L.apexWordEquiv w).2 := by
  simp [apex, apexWordEquiv, Network.boundary_apply, Fintype.sum_sum_type,
    push_apply, total_apply]

theorem owner_boundary_zero_iff (L : Ported I O P) (w : L.owner.Word) :
    L.owner.boundary w = 0 ↔ L.fullBoundary (L.ownerWordEquiv w) = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · funext u
      simpa only [owner_boundary_inside] using congrFun h (Sum.inl u)
    · funext v
      simpa only [owner_boundary_outside] using congrFun h (Sum.inr v)
  · intro h
    funext v
    rcases v with u | v
    · simpa only [owner_boundary_inside] using congrFun (congrArg Prod.fst h) u
    · simpa only [owner_boundary_outside] using congrFun (congrArg Prod.snd h) v

theorem apex_boundary_zero_iff (L : Ported I O P) (w : L.apex.Word) :
    L.apex.boundary w = 0 ↔ L.localBoundary (L.apexWordEquiv w) = 0 := by
  constructor
  · intro h
    funext u
    simpa only [apex_boundary_inside] using congrFun h (Sum.inl u)
  · intro h
    funext v
    rcases v with u | v
    · simpa only [apex_boundary_inside] using congrFun h u
    · cases v
      rw [apex_boundary_apex]
      exact L.local_cut_even ⟨L.apexWordEquiv w, h⟩

/-- Complete owner words, not an arbitrary local model or selected family. -/
def ownerCycleEquiv (L : Ported I O P) : L.owner.CycleSpace ≃ L.FullSpace where
  toFun w := ⟨L.ownerWordEquiv w.1, (L.owner_boundary_zero_iff w.1).1 w.2⟩
  invFun w := ⟨L.ownerWordEquiv.symm w.1, (L.owner_boundary_zero_iff _).2 (by
    rw [Equiv.apply_symm_apply]
    exact w.2)⟩
  left_inv w := Subtype.ext (L.ownerWordEquiv.symm_apply_apply w.1)
  right_inv w := Subtype.ext (L.ownerWordEquiv.apply_symm_apply w.1)

/-- The apex equation is redundant once all internal equations hold. -/
def apexCycleEquiv (L : Ported I O P) : L.apex.CycleSpace ≃ L.LocalSpace where
  toFun w := ⟨L.apexWordEquiv w.1, (L.apex_boundary_zero_iff w.1).1 w.2⟩
  invFun w := ⟨L.apexWordEquiv.symm w.1, (L.apex_boundary_zero_iff _).2 (by
    rw [Equiv.apply_symm_apply]
    exact w.2)⟩
  left_inv w := Subtype.ext (L.apexWordEquiv.symm_apply_apply w.1)
  right_inv w := Subtype.ext (L.apexWordEquiv.apply_symm_apply w.1)

/-- The event can be any property of the retained internal physical word. -/
def ownerFraction (L : Ported I O P) (Good : I.Word → Prop) : ℝ :=
  Finite.density (fun w : L.owner.CycleSpace => Good (L.ownerWordEquiv w.1).1.1)

def apexFraction (L : Ported I O P) (Good : I.Word → Prop) : ℝ :=
  Finite.density (fun w : L.apex.CycleSpace => Good (L.apexWordEquiv w.1).1)

theorem ownerFraction_eq_full (L : Ported I O P) (Good : I.Word → Prop) :
    L.ownerFraction Good =
      Finite.density (fun w : L.FullSpace => Good w.1.1.1) := by
  exact Finite.density_equiv L.ownerCycleEquiv (by intro w; rfl)

theorem apexFraction_eq_local (L : Ported I O P) (Good : I.Word → Prop) :
    L.apexFraction Good =
      Finite.density (fun w : L.LocalSpace => Good w.1.1) := by
  exact Finite.density_equiv L.apexCycleEquiv (by intro w; rfl)

/-- Source Section 17.2, on explicit physical networks. -/
theorem ownerFraction_le_apexFraction (L : Ported I O P) (c₀ : O.Component)
    (Good : I.Word → Prop) :
    L.ownerFraction Good ≤
      (2 : ℝ) ^ (Fintype.card O.Component - 1) * L.apexFraction Good := by
  rw [L.ownerFraction_eq_full, L.apexFraction_eq_local]
  exact L.full_density_le_local_density c₀ (fun w => Good w.1.1)



end Ported
end Erdos1016.BoundaryTrace

import Erdos1016.CycleSpace.Graphical.VertexStarSpaces

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalRegionContraction

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Pull a functional on the contracted cycle space back along restriction. -/
def dualPullback (f : V →ₗ[F] W) : (W →ₗ[F] F) →ₗ[F] (V →ₗ[F] F) where
  toFun φ := φ.comp f
  map_add' φ ψ := by
    ext v
    rfl
  map_smul' a φ := by
    ext v
    rfl

/-- Surjectivity of cycle restriction makes pullback on duals injective. -/
theorem dualPullback_injective (f : V →ₗ[F] W)
    (hf : Function.Surjective f) : Function.Injective (dualPullback f) := by
  intro φ ψ h
  ext w
  obtain ⟨v, rfl⟩ := hf w
  have hv := congrArg (fun g : V →ₗ[F] F => g v) h
  exact hv



end Erdos1016.Proof.GraphicalRegionContraction

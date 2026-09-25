import Erdos1016.Extremal.Capacity.PureCycleBound

set_option autoImplicit false

/-!
# Cyclic-region witness to a nonzero local parity kernel

This small bridge packages the basic local input needed by the many-region
conditional product argument: an actual host cycle contained in a region
gives a nonzero restricted cycle-space vector.
-/

noncomputable section

namespace Erdos1016.Proof.ManyRegionsCycleKernelBridge

open Erdos1016
open Erdos1016.PhysicalGraph

/-- Any nonzero host cycle word supported in `E` restricts to a nonzero
element of the cycle space on `E`. -/
theorem exists_nonzero_restrictedCycleSpace_of_supported_cycle
    (G : PhysicalGraph) (E : Finset G.Edge)
    (hcycle : ∃ C : G.CycleWord, ∀ e, C.1 e ≠ 0 → e ∈ E) :
    ∃ z : G.RestrictedCycleSpace E, z ≠ 0 := by
  classical
  obtain ⟨C, hC⟩ := hcycle
  let z : G.RestrictedCycleSpace E := ⟨G.restrictWord E C.1, by
    change G.restrictedBoundary E (G.restrictWord E C.1) = 0
    change G.boundary (G.extendWord E (G.restrictWord E C.1)) = 0
    have hout : ∀ e, e ∉ E → C.1 e = 0 := by
      intro e he
      by_contra hne
      exact he (hC e hne)
    rw [G.extend_restrict_of_outside_zero E C.1 hout]
    exact C.2.2.1⟩
  refine ⟨z, ?_⟩
  intro hz
  apply C.2.1
  funext e
  by_cases he : e ∈ E
  · have h := congrFun (congrArg Subtype.val hz) ⟨e, he⟩
    simpa [z, restrictWord] using h
  · have hout : ∀ f, f ∉ E → C.1 f = 0 := by
      intro f hf
      by_contra hne
      exact hf (hC f hne)
    exact hout e he

end Erdos1016.Proof.ManyRegionsCycleKernelBridge

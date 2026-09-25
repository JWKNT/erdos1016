import Erdos1016.Probability.Conditional.CycleFactorization
import Erdos1016.Cycles.Filtering.ReturnMassAccounting

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ExternalReturnFilter

open Erdos1016.BoundaryDecay

local instance retainedReturnFilterDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The literal retained-cycle condition in the safe region used by the
manuscript's short-return deletion. The external path and its attachment
vertices lie in `V`; its endpoints on the base cycle are distinct, and the
path avoids the base cycle. -/
def NoShortExternalReturnWithin (G : PhysicalGraph) (V C : Finset G.Vertex)
    (q : ℕ) : Prop :=
  ∀ (r s u v : G.Vertex) (hu : u ∈ C) (hv : v ∈ C), u ≠ v →
    G.toSimpleGraph.Adj r u → G.toSimpleGraph.Adj s v →
    ∀ p : G.toSimpleGraph.Walk r s, p.IsPath →
      (∀ z, z ∈ p.support → z ∈ V) →
      (∀ z, z ∈ p.support → z ∉ C) → q < p.length + 2

/-- The manuscript's accepted family: remove each base cycle admitting a
short external return inside the specified safe region. -/
def acceptedShortReturnCycles (G : PhysicalGraph) (V : Finset G.Vertex)
    (bases : Finset G.CycleWord) (q : ℕ) : Finset G.CycleWord :=
  bases.filter fun C =>
    NoShortExternalReturnWithin G V (Cycle.vertices C) q

theorem mem_acceptedShortReturnCycles
    (G : PhysicalGraph) (V : Finset G.Vertex)
    (bases : Finset G.CycleWord) (q : ℕ) (C : G.CycleWord) :
    C ∈ acceptedShortReturnCycles G V bases q ↔
      C ∈ bases ∧
        NoShortExternalReturnWithin G V (Cycle.vertices C) q := by
  simp [acceptedShortReturnCycles]







/-- A no-return filter applied inside a safe region transfers to any
complement component lying inside that region. The cycle and the component
are disjoint, so a path in the component is an external path for the cycle. -/
theorem noShortExternalReturnThrough_of_region
    {G : PhysicalGraph} (R V C : Finset G.Vertex) (q : ℕ)
    (hRV : R ⊆ V)
    (hdisj : Disjoint R C)
    (hreturn : NoShortExternalReturnWithin G V C q) :
    ConditionalMoments.NoShortExternalReturnThrough G R C q := by
  intro r s u v hr hs hu hv huv hru hsv p hp
  let incl : G.toSimpleGraph.induce (↑R : Set G.Vertex) →g G.toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := by intro a b hab; exact hab }
  let p' : G.toSimpleGraph.Walk r s := p.map incl
  have hp' : p'.IsPath :=
    (SimpleGraph.Walk.map_isPath_iff_of_injective Subtype.val_injective).2 hp
  have hregion : ∀ z, z ∈ p'.support → z ∈ V := by
    intro z hz
    have hz' : ∃ a, a ∈ p.support ∧ incl a = z := by
      simpa [p', SimpleGraph.Walk.support_map] using hz
    obtain ⟨a, ha, haz⟩ := hz'
    have hazval : a.1 = z := by simpa [incl] using haz
    exact hazval ▸ hRV a.2
  have houtside : ∀ z, z ∈ p'.support → z ∉ C := by
    intro z hz hzC
    have hz' : ∃ a, a ∈ p.support ∧ incl a = z := by
      simpa [p', SimpleGraph.Walk.support_map] using hz
    obtain ⟨a, ha, haz⟩ := hz'
    have hazval : a.1 = z := by simpa [incl] using haz
    exact (Finset.disjoint_left.mp hdisj a.2 (hazval ▸ hzC))
  have h := hreturn r s u v hu hv huv hru hsv p' hp' hregion houtside
  simpa [p'] using h





end Erdos1016.Proof.ExternalReturnFilter
end

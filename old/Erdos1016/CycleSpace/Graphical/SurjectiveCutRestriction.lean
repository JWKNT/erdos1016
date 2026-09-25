import Erdos1016.CycleSpace.Graphical.MultigraphCutFunctionals

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalActualCutMultigraphSurjective

open Erdos1016
open Erdos1016.Proof.GraphicalActualCutMultigraphBridge

local notation "𝔽" => ZMod 2

/-- Extend a quotient edge word to the original edge set by zero away from
the image of the quotient edge labels. -/
def rawLiftWord {G : PhysicalGraph} (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge) (y : M.EdgeWord) : G.Word := by
  classical
  exact fun a => if h : ∃ e, edgeMap e = a then y (Classical.choose h) else 0

theorem rawLiftWord_on_edge {G : PhysicalGraph} (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge) (hinj : Function.Injective edgeMap)
    (y : M.EdgeWord) (e : M.Edge) :
    rawLiftWord M edgeMap y (edgeMap e) = y e := by
  classical
  let h : ∃ e', edgeMap e' = edgeMap e := ⟨e, rfl⟩
  have hchosen : Classical.choose h = e := hinj (Classical.choose_spec h)
  simp [rawLiftWord, h, hchosen]

/-- If every quotient cycle's raw edge lift can be corrected by an original
word that vanishes on all quotient edge labels, restriction of cycle spaces
is surjective.

For a contraction by connected fibers, the correction words should be
constructed separately inside each fiber. Their existence is the
fiberwise-even T-join step; this theorem handles the remaining linear
restriction argument. -/
theorem restrictCycles_surjective_of_internalBoundaryRepair
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge)
    (hinj : Function.Injective edgeMap)
    (hcycle : ∀ x : G.CycleSpace,
      M.boundary (restrictWord M edgeMap x.1) = 0)
    (hrepair : ∀ y : M.CycleSpace, ∃ z : G.Word,
      G.boundary z = G.boundary (rawLiftWord M edgeMap y.1) ∧
      ∀ e : M.Edge, z (edgeMap e) = 0) :
    Function.Surjective (restrictCycles G M edgeMap hcycle) := by
  intro y
  obtain ⟨z, hzBoundary, hzZero⟩ := hrepair y
  let xword : G.Word := rawLiftWord M edgeMap y.1 + z
  have hxcycle : G.boundary xword = 0 := by
    change G.boundary (rawLiftWord M edgeMap y.1 + z) = 0
    rw [G.boundary.map_add, hzBoundary]
    ext v
    have htwo : (2 : 𝔽) = 0 := by decide
    calc
      G.boundary (rawLiftWord M edgeMap y.1) v +
          G.boundary (rawLiftWord M edgeMap y.1) v =
        (2 : 𝔽) * G.boundary (rawLiftWord M edgeMap y.1) v := by ring
      _ = 0 := by rw [htwo]; simp
  let x : G.CycleSpace := ⟨xword, hxcycle⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext e
  change rawLiftWord M edgeMap y.1 (edgeMap e) + z (edgeMap e) = y.1 e
  rw [rawLiftWord_on_edge M edgeMap hinj y.1 e, hzZero e]
  simp

end Erdos1016.Proof.GraphicalActualCutMultigraphSurjective

end

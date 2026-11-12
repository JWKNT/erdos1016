import Erdos1016.ExactMaximumSupport.PathForestProbability

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Translate a prescribed path to the uniform cycle space

Translation by an actual demand representative preserves edges where it vanishes.
Every affine forest therefore yields a cycle-space word forest on those edges.
The representative can be any prescribed path with the given endpoints.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PathExteriorProbability
open FiniteMultiGraph Probability Probability.PoleMarker

local instance exteriorPathDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- An actual representative transfers affine forest mass to untouched physical edges. -/
theorem affineForestProbability_le_restricted (G : FiniteMultiGraph) (b : G.Demand)
    (a : G.EdgeWord) (hb : G.boundary a=b) (E : Finset G.Edge)
    (hzero : ∀ e∈E,a e=0) :
    affineForestProbability G b ≤
      Finite.density (fun z : G.CycleSpace => G.IsForestWord (G.restrictEdges E z.1)) := by
  let f : Parity.Fiber G.boundary b := ⟨a,hb⟩
  have he : affineForestProbability G b =
      Finite.density (fun z : G.CycleSpace => G.IsForestWord (z.1+f.1)) :=
    (Finite.density_equiv (Parity.fiberEquivKernel G.boundary f).symm (fun _ => Iff.rfl)).symm
  rw [he]
  have hi (z : G.CycleSpace) (hz : G.IsForestWord (z.1+f.1)) :
      G.IsForestWord (G.restrictEdges E z.1) := by
    have hh := hz.restrictEdges E
    have hword : G.restrictEdges E (z.1+f.1)=G.restrictEdges E z.1 := by
      funext e
      by_cases hm : e∈E
      · have hf : f.1 e=0 := hzero e hm
        simp [restrictEdges,hm,hf]
      · simp [restrictEdges,hm]
    rw [hword] at hh
    exact hh
  exact div_le_div_of_nonneg_right (Finite.count_mono hi) (by positivity)

/-- The designated representative need not be the shortest path or a chosen marker repair. -/
theorem restrictedForestProbability_ge_501 (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (hG : G.toSimpleGraph.Connected) (s t : G.Vertex) (hst : s≠t)
    (hpaths : 501*2^G.cycleRank≤1000*G.looplessNetwork.numPaths s t)
    (a : G.EdgeWord) (hb : G.boundary a=G.looplessNetwork.pathDemand s t)
    (E : Finset G.Edge) (hzero : ∀ e∈E,a e=0) :
    (501/1000:ℝ) ≤
      Finite.density (fun z : G.CycleSpace => G.IsForestWord (G.restrictEdges E z.1)) :=
  (PathForestProbability.affineForestProbability_ge_501 G hloop hG s t hst hpaths).trans
    (affineForestProbability_le_restricted G _ a hb E hzero)

end Erdos1016.ExactMaximumSupport.PathExteriorProbability

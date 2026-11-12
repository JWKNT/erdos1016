import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.NetCircuits
import Erdos1016.Graph.Multigraph.ForestCharacterization
import Erdos1016.ExactMaximumSupport.PoleMarkerMargin

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Path counts give the actual affine forest probability

A forest with two odd vertices is a path between those vertices.
The full affine parity fiber has exactly two to the rank elements.
These facts identify the path density with the physical affine forest law.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.PathForestProbability
open FiniteMultiGraph BoundaryTrace Probability Probability.PoleMarker

local instance pathForestDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (hloop : G.IsLoopless)

/-- Relabel all nonloop coordinates back to the original physical labels. -/
def liftWord (x : G.looplessNetwork.Word) : G.EdgeWord := fun e => x ⟨e,hloop e⟩

@[simp] theorem nonloop_lift (x : G.looplessNetwork.Word) :
    G.nonloopWord (liftWord G hloop x) = x := rfl

@[simp] theorem lift_nonloop (x : G.EdgeWord) :
    liftWord G hloop (G.nonloopWord x) = x := rfl

theorem boundary_lift (x : G.looplessNetwork.Word) :
    G.boundary (liftWord G hloop x) = G.looplessNetwork.boundary x := by
  rw [← G.nonloopWord_boundary, nonloop_lift]

include hloop

/-- Network paths are forests with the original physical edge labels. -/
theorem forest_of_path {s t : G.Vertex} (x : G.EdgeWord)
    (hx : G.looplessNetwork.IsPathWord s t (G.nonloopWord x)) : G.IsForestWord x := by
  apply (G.isForestWord_iff_no_even_support x).mpr
  intro seed hsub
  have hz : G.nonloopWord seed.1 = 0 := hx.eq_zero_of_even_subword
    (fun e he => hsub e.1 he) (by rw [G.nonloopWord_boundary]; exact seed.2)
  funext e
  exact congrFun hz ⟨e,hloop e⟩

/-- A forest with the path demand has no other selected component. -/
theorem path_of_forest {s t : G.Vertex} (hst : s ≠ t) (x : G.EdgeWord)
    (hb : G.boundary x = G.looplessNetwork.pathDemand s t) (hx : G.IsForestWord x) :
    G.looplessNetwork.IsPathWord s t (G.nonloopWord x) := by
  apply (G.looplessNetwork.isPathWord_iff_minimal s t _).mpr
  refine ⟨hst, by rw [G.nonloopWord_boundary]; exact hb, ?_⟩
  intro y hsub hy
  have hz : liftWord G hloop y = 0 := G.word_eq_zero_of_boundary_zero_of_forest _
    (by rw [boundary_lift]; exact hy)
    (hx.mono (fun e he => hsub ⟨e,hloop e⟩ he))
  funext e
  exact congrFun hz e.1

/-- The affine forest count equals the path count, with parallel labels retained. -/
theorem affine_forest_count_eq (s t : G.Vertex) (hst : s ≠ t) :
    Finite.count (fun x : Parity.Fiber G.boundary (G.looplessNetwork.pathDemand s t) =>
      G.IsForestWord x.1) = (G.looplessNetwork.numPaths s t : ℝ) := by
  rw [BoundaryTrace.count_eq_subtype_card]
  congr 1
  let f : {x : Parity.Fiber G.boundary (G.looplessNetwork.pathDemand s t) //
      G.IsForestWord x.1} →
      {x : G.looplessNetwork.Word // G.looplessNetwork.IsPathWord s t x} :=
    fun x => ⟨G.nonloopWord x.1.1,path_of_forest G hloop hst x.1.1 x.1.2 x.2⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext e
    exact congrFun (congrArg Subtype.val hab) ⟨e,hloop e⟩
  · intro y
    refine ⟨⟨⟨liftWord G hloop y.1,?_⟩,?_⟩,?_⟩
    · rw [boundary_lift]
      exact y.2.boundary_eq
    · apply forest_of_path G hloop
      simpa only [nonloop_lift] using y.2
    · exact Subtype.ext (nonloop_lift G hloop y.1)

/-- Exact path density under the complete uniform affine parity law. -/
theorem affineForestProbability_eq_path_density (hG : G.toSimpleGraph.Connected)
    (s t : G.Vertex) (hst : s ≠ t) :
    affineForestProbability G (G.looplessNetwork.pathDemand s t) =
      (G.looplessNetwork.numPaths s t : ℝ)/(2:ℝ)^G.cycleRank := by
  obtain ⟨p⟩ := hG s t
  let w : Parity.Fiber G.boundary (G.looplessNetwork.pathDemand s t) :=
    ⟨G.walkWord p,by
      rw [G.boundary_walkWord]
      funext v
      by_cases hs : v=s <;> by_cases ht : v=t <;>
        simp [Network.pathDemand,vertexUnit,Pi.single_apply,hs,ht]⟩
  have hcard : Fintype.card (Parity.Fiber G.boundary (G.looplessNetwork.pathDemand s t)) =
      2^G.cycleRank := by
    rw [← Nat.card_eq_fintype_card]
    exact Parity.fiber_natCard G.boundary w
  simp only [affineForestProbability,Finite.density,affine_forest_count_eq G hloop s t hst,
    hcard,Nat.cast_pow,Nat.cast_ofNat]

/-- The integer path-richness premise gives the exact margin used by the layer theorem. -/
theorem affineForestProbability_ge_501 (hG : G.toSimpleGraph.Connected)
    (s t : G.Vertex) (hst : s ≠ t)
    (hpaths : 501*2^G.cycleRank ≤ 1000*G.looplessNetwork.numPaths s t) :
    (501/1000:ℝ) ≤ affineForestProbability G (G.looplessNetwork.pathDemand s t) := by
  rw [affineForestProbability_eq_path_density G hloop hG s t hst]
  apply (le_div_iff₀ (by positivity)).mpr
  have h : (501:ℝ)*2^G.cycleRank ≤ 1000*(G.looplessNetwork.numPaths s t:ℝ) := by
    exact_mod_cast hpaths
  linarith

omit hloop in
/-- Path richness bounds all distance layers in the actual multigraph. -/
theorem exists_path_layer_bound_501 :
    ∃ B : ℕ, ∀ (G : FiniteMultiGraph) (ports : Finset G.Vertex) (s t : G.Vertex),
      G.IsLoopless → G.toSimpleGraph.Connected → (∀ v,G.degree v≤3) →
      (∀ v,v∉ports → G.degree v=3) → s∈ports → t∈ports → s≠t →
      501*2^G.cycleRank ≤ 1000*G.looplessNetwork.numPaths s t →
      ∀ j : ℤ,(Finset.univ.filter fun v => (G.toSimpleGraph.dist s v : ℤ)=j).card ≤
        B*(ports.card+1)^2 := by
  obtain ⟨B,hB⟩ := PoleMarkerMargin.exists_supported_demand_layer_bound_501
  refine ⟨B,?_⟩
  intro G ports s t hloop hG hdeg hcubic hs ht hst hp
  apply hB G ports s (G.looplessNetwork.pathDemand s t) hG hdeg hcubic hs
  · intro v hv
    have hvs : v≠s := by rintro rfl; exact hv hs
    have hvt : v≠t := by rintro rfl; exact hv ht
    simp [Network.pathDemand,Pi.single_apply,hvs,hvt]
  · exact affineForestProbability_ge_501 G hloop hG s t hst hp

end Erdos1016.ExactMaximumSupport.PathForestProbability

import Erdos1016.CycleSpace.Graphical.EvenAssignmentStarBound
import Erdos1016.CycleSpace.Graphical.LinkRange

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalTripleStarBoundGraph

open Erdos1016
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalLinkPairSpan
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalTripleStarBound
open Erdos1016.Proof.GraphicalAbstractLinks

local notation "F₂" => ZMod 2

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The link map with codomain restricted to the even assignments. -/
def linkMapToEven (G : PhysicalGraph) (u v : G.Vertex) (hne : u ≠ v) :
    G.CycleSpace →ₗ[F₂] EvenLinkAssignments (ι := LinkIndex G u v) where
  toFun x := ⟨linkMap G u v x, by
    change totalLinkParity (linkMap G u v x) = 0
    exact GraphicalLinkTotalParity.linkMap_totalParity_eq_zero G u v hne x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (linkMap G u v) x y
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (linkMap G u v) a x

/-- Restricting the link map's codomain does not change its kernel. -/
theorem ker_linkMapToEven (G : PhysicalGraph) (u v : G.Vertex) (hne : u ≠ v) :
    LinearMap.ker (linkMapToEven G u v hne) = LinearMap.ker (linkMap G u v) := by
  ext x
  simp [LinearMap.mem_ker, linkMapToEven]

/-- Graph transfer step for the three-star estimate.  The graph-specific
inputs are the exact two-star link-kernel decomposition and the fact that
third-vertex-avoiding cycles realize every even link assignment with the
distinguished coordinate zero. -/
theorem tripleStar_finrank_le_one_of_linkFactorization
    (G : PhysicalGraph) (u v w : G.Vertex)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    [Nonempty (LinkIndex G u v)]
    (k : LinkIndex G u v)
    (hker : LinearMap.ker (linkMap G u v) =
      cyclesAvoidingVertex G u ⊔ cyclesAvoidingVertex G v)
    (haway : evenAssignmentsAway (ι := LinkIndex G u v) k ≤
      LinearMap.range
        ((linkMapToEven G u v huv).comp (cyclesAvoidingVertex G w).subtype)) :
    Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1 := by
  classical
  let f := linkMapToEven G u v huv
  let W := cyclesAvoidingVertex G w
  have hf : Function.Surjective f := by
    intro z
    have hz : z.1 ∈ EvenLinkAssignments (ι := LinkIndex G u v) := z.2
    letI : Nonempty (LinkIndex G u v) := ‹Nonempty (LinkIndex G u v)›
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp
      (evenLinkAssignments_le_linkMap_range G u v huv hz)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa [f, linkMapToEven] using hx
  have hkerf : LinearMap.ker f =
      cyclesAvoidingVertex G u ⊔ cyclesAvoidingVertex G v := by
    rw [ker_linkMapToEven, hker]
  have haway' : evenAssignmentsAway (ι := LinkIndex G u v) k ≤
      LinearMap.range (f.comp W.subtype) := by
    simpa [f, W] using haway
  have htriple : tripleStarSpace G u v w ≤
      (LinearMap.ker f ⊔ W).dualAnnihilator := by
    intro φ hφ
    have hu : φ ∈ vertexStarSpace G u := hφ.1.1
    have hv : φ ∈ vertexStarSpace G v := hφ.1.2
    have hw : φ ∈ vertexStarSpace G w := hφ.2
    have hku : φ ∈ (LinearMap.ker f).dualAnnihilator := by
      rw [hkerf, Submodule.dualAnnihilator_sup_eq]
      constructor
      · exact (Submodule.mem_dualAnnihilator φ).2 fun x hx =>
          vertexStarSpace_annihilates_avoiding G u φ hu ⟨x, hx⟩
      · exact (Submodule.mem_dualAnnihilator φ).2 fun x hx =>
          vertexStarSpace_annihilates_avoiding G v φ hv ⟨x, hx⟩
    have hww : φ ∈ W.dualAnnihilator :=
      (Submodule.mem_dualAnnihilator φ).2 fun x hx =>
        vertexStarSpace_annihilates_avoiding G w φ hw ⟨x, hx⟩
    rw [Submodule.dualAnnihilator_sup_eq]
    exact ⟨hku, hww⟩
  calc
    Module.finrank F₂ (tripleStarSpace G u v w) ≤
        Module.finrank F₂ ((LinearMap.ker f ⊔ W).dualAnnihilator) :=
      Submodule.finrank_mono htriple
    _ ≤ 1 := Erdos1016.Proof.GraphicalTripleStarBound.finrank_dualAnnihilator_kerSup_le_one
      f hf W k haway'

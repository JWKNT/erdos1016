import Erdos1016.Probability.Cylinders.TripleLowerBound
import Erdos1016.Probability.Finite.LinearImages
import Erdos1016.Probability.Moments.WeightedSecondMoment
import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false
noncomputable section

namespace Erdos1016.FiniteMultiGraph
open BoundaryDecay

/-- Actual restriction of an even edge word to a finite set of labelled edges. -/
def observeEdges (G : FiniteMultiGraph) (E : Finset G.Edge) :
    G.CycleSpace →ₗ[F₂] (E → F₂) where
  toFun x e := x.1 e.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The event prescribing the seed's coordinates on `E`, with feasibility
witnessed by the actual seed even word itself. -/
def MatchesSeed (G : FiniteMultiGraph) (E : Finset G.Edge)
    (seed x : G.CycleSpace) : Prop := G.observeEdges E x = G.observeEdges E seed

theorem matchesSeed_probability (G : FiniteMultiGraph) (E : Finset G.Edge)
    (seed : G.CycleSpace) :
    Finite.density (G.MatchesSeed E seed) =
      1 / (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range (G.observeEdges E)) := by
  unfold MatchesSeed Finite.density
  rw [BoundaryTrace.count_eq_subtype_card]
  exact Proof.SelectedTripleCylinder.fiberProbability_eq (G.observeEdges E)
    (G.observeEdges E seed) ⟨seed, rfl⟩

/-- A feasible prescription of `m` edge coordinates has probability at least
`2^(-m)`. This includes loops and parallel labels without special cases. -/
theorem matchesSeed_probability_ge (G : FiniteMultiGraph) (E : Finset G.Edge)
    (seed : G.CycleSpace) :
    1 / (2 : ℝ) ^ E.card ≤ Finite.density (G.MatchesSeed E seed) := by
  rw [G.matchesSeed_probability]
  have hd : Module.finrank F₂ (LinearMap.range (G.observeEdges E)) ≤ E.card := by
    have h := Submodule.finrank_mono
      (show LinearMap.range (G.observeEdges E) ≤ (⊤ : Submodule F₂ (E → F₂)) from le_top)
    simpa using h
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hd)

theorem zeroCoordinates_probability_ge (G : FiniteMultiGraph) (E : Finset G.Edge) :
    1 / (2 : ℝ) ^ E.card ≤
      Finite.density (fun x : G.CycleSpace => ∀ e ∈ E, x.1 e = 0) := by
  have he : G.MatchesSeed E 0 = fun x : G.CycleSpace => ∀ e ∈ E, x.1 e = 0 := by
    funext x
    apply propext
    constructor
    · intro h e he
      exact congrFun h ⟨e, he⟩
    · intro h
      funext e
      exact h e.1 e.2
  simpa only [he] using G.matchesSeed_probability_ge E 0

def seedSupport (G : FiniteMultiGraph) (seed : G.CycleSpace) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => seed.1 e ≠ 0

/-- For a cycle seed, prescribing its nonzero coordinates is precisely the
all-cycle-edges-selected event. The definition is useful for any even seed. -/
def SelectedSeed (G : FiniteMultiGraph) (seed x : G.CycleSpace) : Prop :=
  ∀ e, seed.1 e ≠ 0 → x.1 e ≠ 0

theorem selectedSeed_iff_matches (G : FiniteMultiGraph) (seed x : G.CycleSpace) :
    G.SelectedSeed seed x ↔ G.MatchesSeed (G.seedSupport seed) seed x := by
  constructor
  · intro h
    funext e
    have he : seed.1 e.1 ≠ 0 := (Finset.mem_filter.mp e.2).2
    have hx := h e.1 he
    have hseed : seed.1 e.1 = 1 := by
      have htwo := ZMod.val_lt (seed.1 e.1)
      apply ZMod.val_injective
      have hn : (seed.1 e.1).val ≠ 0 := by simpa using he
      norm_num [F₂, ZMod.val_one_eq_one_mod] at htwo ⊢
      omega
    have hsel : x.1 e.1 = 1 := by
      have htwo := ZMod.val_lt (x.1 e.1)
      apply ZMod.val_injective
      have hn : (x.1 e.1).val ≠ 0 := by simpa using hx
      norm_num [F₂, ZMod.val_one_eq_one_mod] at htwo ⊢
      omega
    exact hsel.trans hseed.symm
  · intro h e he
    have hm : e ∈ G.seedSupport seed := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    have hh := congrFun h ⟨e, hm⟩
    change x.1 e = seed.1 e at hh
    rw [hh]
    exact he

theorem selectedSeed_probability_ge (G : FiniteMultiGraph) (seed : G.CycleSpace) :
    1 / (2 : ℝ) ^ (G.seedSupport seed).card ≤ Finite.density (G.SelectedSeed seed) := by
  have he : G.SelectedSeed seed = G.MatchesSeed (G.seedSupport seed) seed := by
    funext x
    exact propext (G.selectedSeed_iff_matches seed x)
  rw [he]
  exact G.matchesSeed_probability_ge _ seed

/-- The normalized cycle indicator in the shorter proof, on the actual
uniform multigraph cycle space. -/
def normalizedSeedIndicator (G : FiniteMultiGraph) (seed : G.CycleSpace) :
    G.CycleSpace → ℝ :=
  normalizedIndicator (G.SelectedSeed seed) (1 / (2 : ℝ) ^ (G.seedSupport seed).card)

theorem normalizedSeedIndicator_bounds (G : FiniteMultiGraph) (seed x : G.CycleSpace) :
    0 ≤ G.normalizedSeedIndicator seed x ∧ G.normalizedSeedIndicator seed x ≤ 1 := by
  have h := G.selectedSeed_probability_ge seed
  exact ⟨normalizedIndicator_nonneg _ _ (by positivity) x,
    normalizedIndicator_le_one _ _ h (lt_of_lt_of_le (by positivity) h) x⟩

theorem average_normalizedSeedIndicator (G : FiniteMultiGraph) (seed : G.CycleSpace) :
    average (G.normalizedSeedIndicator seed) = 1 / (2 : ℝ) ^ (G.seedSupport seed).card := by
  apply average_normalizedIndicator
  exact (lt_of_lt_of_le (by positivity) (G.selectedSeed_probability_ge seed)).ne'

end Erdos1016.FiniteMultiGraph

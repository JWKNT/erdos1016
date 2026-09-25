import Erdos1016.Cycles.Filtering.ReturnMassAccounting
import Erdos1016.Cycles.Filtering.ReturnRunCounts
import Erdos1016.Nonbacktracking.Walks.PathRunEncoding

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ExternalReturnPathMass

open scoped BigOperators
open Erdos1016.BoundaryDecay
open Erdos1016.Proof.ExternalReturnFilter
open Erdos1016.Proof.PathEndpointRunInjection

variable (G : PhysicalGraph)

/-- Ordered endpoint pairs lying on a physical cycle word. -/
def cycleEndpointPairs (C : G.CycleWord) : Finset (G.Vertex × G.Vertex) :=
  Finset.univ.filter fun p =>
    p.1 ∈ Cycle.vertices C ∧ p.2 ∈ Cycle.vertices C

/-- The total weighted mass of all fixed-endpoint simple paths of lengths
`s < a ≤ L`, summed over the ordered endpoint pairs of each short physical
cycle word. This counts a superset of any paths satisfying extra externality
conditions. -/
theorem short_cycle_simple_path_mass_le
    (bases : Finset G.CycleWord) (s L D : ℕ)
    (hshort : ∀ C ∈ bases, G.wordLength C.1 ≤ L)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hg : Erdos1016.Nonbacktracking.ShortWalks.GirthGreater
      G.toSimpleGraph D)
    (hs : 0 < s) (hshortGirth : 2 * s ≤ D) :
    (∑ C ∈ bases, (1 / 2 : ℝ) ^ G.wordLength C.1 *
      (∑ p ∈ cycleEndpointPairs G C, ∑ a ∈ Finset.Ioc s L,
        (Fintype.card (FixedEndpointSimplePaths G a p.1 p.2) : ℝ) *
          (1 / 2 : ℝ) ^ a)) ≤
      (3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s *
        (∑ C ∈ bases, (1 / 2 : ℝ) ^ G.wordLength C.1) := by
  classical
  let endpoints : G.CycleWord → Finset (G.Vertex × G.Vertex) :=
    cycleEndpointPairs G
  let weight : G.CycleWord → ℝ := fun C => (1 / 2 : ℝ) ^ G.wordLength C.1
  let count : G.CycleWord → (G.Vertex × G.Vertex) → ℕ → ℕ :=
    fun _ p a => Fintype.card (FixedEndpointSimplePaths G a p.1 p.2)
  have hendpoint (C : G.CycleWord) (hC : C ∈ bases) :
      (endpoints C).card ≤ L ^ 2 := by
    have hsupport : (Cycle.vertices C).card ≤ L := by
      rw [← Erdos1016.BoundaryDecay.Cycle.length_eq_vertices_card C]
      exact hshort C hC
    have hsubset : endpoints C ⊆ Cycle.vertices C ×ˢ Cycle.vertices C := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨_, hp1, hp2⟩
      exact Finset.mem_product.mpr ⟨hp1, hp2⟩
    have hfilter : (endpoints C).card ≤
        (Cycle.vertices C ×ˢ Cycle.vertices C).card := Finset.card_le_card hsubset
    calc
      (endpoints C).card ≤ (Cycle.vertices C).card * (Cycle.vertices C).card := by
        simpa using hfilter
      _ = (Cycle.vertices C).card ^ 2 := by ring
      _ ≤ L ^ 2 := Nat.pow_le_pow_left hsupport 2
  have hcount (C : G.CycleWord) (hC : C ∈ bases)
      (p : G.Vertex × G.Vertex) (hp : p ∈ endpoints C)
      (a : ℕ) (ha : a ∈ Finset.Ioc s L) :
      count C p a ≤ 3 * 2 ^ (a - s - 1) := by
    have hrun := endpointRuns_card_le_suffix_budget G hmin hmax D a s p.1 p.2
      hg hs (Finset.mem_Ioc.mp ha).1 hshortGirth
    have hpath := fixedEndpointSimplePaths_card_le_endpointRuns G a p.1 p.2
    dsimp [count]
    exact hpath.trans hrun
  have hweight (C : G.CycleWord) (hC : C ∈ bases) : 0 ≤ weight C := by
    dsimp [weight]
    positivity
  simpa [endpoints, weight, count] using
    (base_endpoint_suffix_mass_le (bases := bases) endpoints weight count s L
      hweight hendpoint hcount)

end Erdos1016.Proof.ExternalReturnPathMass
end

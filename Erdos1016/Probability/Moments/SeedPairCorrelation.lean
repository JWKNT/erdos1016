import Erdos1016.Probability.Cylinders.SubcubicSeedEvents
import Erdos1016.CycleSpace.Graphical.DisjointRegionCuts

set_option autoImplicit false

/-!
# Exact normalized seed correlations from physical links

Two disjoint connected regions are contracted, leaving every other vertex
as a singleton. The link count is the actual direct-edge/component link
count in that quotient, not a supplied correlation certificate.
-/

noncomputable section
namespace Erdos1016.FiniteMultiGraph.SeedPairCorrelation

open ConnectedContraction ExceptionalPartners LinkCorrelation BoundaryDecay

local instance seedPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (U V : Finset G.Vertex)

def regions : Bool → Finset G.Vertex := fun b => if b then V else U

abbrev PairLabel := DisjointRegionCuts.Label G (regions G U V)
abbrev pairLabel := DisjointRegionCuts.label G (regions G U V)
abbrev pairQuotient := quotient G (pairLabel G U V)

def firstVertex : (pairQuotient G U V).Vertex :=
  vertexEquiv (Sum.inl false : PairLabel G U V)

def secondVertex : DeletedVertex (firstVertex G U V) :=
  ⟨vertexEquiv (Sum.inl true : PairLabel G U V), by
    intro he
    have h := vertexEquiv.injective he
    exact Bool.noConfusion (Sum.inl.inj h)⟩

/-- Actual physical links between the two contracted regions. -/
abbrev Links := MultigraphLink (pairQuotient G U V) (firstVertex G U V) (secondVertex G U V)

private theorem regions_disjoint (hUV : Disjoint U V) :
    Pairwise (fun i j => Disjoint (regions G U V i) (regions G U V j)) := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact hUV
  · exact hUV.symm
  · exact (hij rfl).elim

private theorem regions_connected
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected) :
    ∀ i, (G.toSimpleGraph.induce (↑(regions G U V i) : Set G.Vertex)).Connected := by
  intro i
  cases i
  · exact hU
  · exact hV

/-- The zero-cut ratio for the original regions is exactly the quotient's
link factor, including all parallel inter-region edges. -/
theorem zeroCut_pair_exact (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected) :
    Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V) =
      dyadic ((Nat.card (Links G U V) : ℤ) - 1) *
        Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) *
        Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace V) := by
  have hdisj := regions_disjoint G U V hUV
  have hfib := DisjointRegionCuts.connectedFibers G (regions G U V) hdisj
    (regions_connected G U V hU hV)
  have he (i : Bool) : FiberZeroCut G (pairLabel G U V) (Sum.inl i) =
      fun x : G.CycleSpace => x ∈ G.zeroCutSpace (regions G U V i) := by
    rw [DisjointRegionCuts.fiberZeroCut_eq G (regions G U V) hdisj]
    funext x
    exact propext (G.mem_zeroCutSpace_iff (regions G U V i) x).symm
  have hp := multigraph_zeroCut_pair (pairQuotient G U V)
    (quotient_connected G (pairLabel G U V) hG hfib)
    (firstVertex G U V) (secondVertex G U V)
  change Finite.density (fun x =>
    ZeroCutAt (pairQuotient G U V) (vertexEquiv (Sum.inl false : PairLabel G U V)) x ∧
    ZeroCutAt (pairQuotient G U V) (vertexEquiv (Sum.inl true : PairLabel G U V)) x) = _ at hp
  rw [← fiberZeroCut_pair_density G (pairLabel G U V) hfib (Sum.inl false) (Sum.inl true)] at hp
  change _ = dyadic ((Nat.card (Links G U V) : ℤ) - 1) *
    Finite.density (ZeroCutAt (pairQuotient G U V) (vertexEquiv (Sum.inl false : PairLabel G U V))) *
    Finite.density (ZeroCutAt (pairQuotient G U V) (vertexEquiv (Sum.inl true : PairLabel G U V))) at hp
  rw [← fiberZeroCut_density G (pairLabel G U V) hfib (Sum.inl false),
    ← fiberZeroCut_density G (pairLabel G U V) hfib (Sum.inl true), he false, he true] at hp
  exact hp

/-- Fixed internal affine factors cancel from the pair correlation ratio. -/
theorem incidentSeed_pair_exact (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V) :
    Finite.density (fun x => G.IncidentSeed U seed x ∧ G.IncidentSeed V seed' x) =
      dyadic ((Nat.card (Links G U V) : ℤ) - 1) *
        Finite.density (G.IncidentSeed U seed) * Finite.density (G.IncidentSeed V seed') := by
  rw [G.incidentSeed_pair_density U V hUV seed seed',
    zeroCut_pair_exact G U V hG hUV hU hV,
    G.incidentSeed_density U seed, G.incidentSeed_density V seed']
  ring

/-- Normalization preserves exactly the same actual link factor. -/
theorem normalizedIncidentSeed_pair (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V) (a b : ℝ) :
    average (fun x => normalizedIndicator (G.IncidentSeed U seed) a x *
      normalizedIndicator (G.IncidentSeed V seed') b x) =
        dyadic ((Nat.card (Links G U V) : ℤ) - 1) * a * b :=
  normalizedIndicator_joint_of_ratio _ _ a b _
    (G.incidentSeed_density_pos U seed).ne' (G.incidentSeed_density_pos V seed').ne'
    (incidentSeed_pair_exact G U V hG hUV hU hV seed seed')

/-- The exact selection-event law for two disjoint cycles in a subcubic
ambient multigraph. The cycle seeds are literal supported even words. -/
theorem selectedSeed_pair_exact (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V)
    (hdU : ∀ v ∈ U, G.selectedDegree seed.1.1 v = 2)
    (hdV : ∀ v ∈ V, G.selectedDegree seed'.1.1 v = 2)
    (hdegreeU : ∀ v ∈ U, G.degree v ≤ 3) (hdegreeV : ∀ v ∈ V, G.degree v ≤ 3) :
    Finite.density (fun x => G.SelectedSeed seed.1 x ∧ G.SelectedSeed seed'.1 x) =
      dyadic ((Nat.card (Links G U V) : ℤ) - 1) *
        Finite.density (G.SelectedSeed seed.1) * Finite.density (G.SelectedSeed seed'.1) := by
  have heU : G.SelectedSeed seed.1 = G.IncidentSeed U seed := by
    funext x
    exact propext (G.selectedSeed_iff_incidentSeed U seed hdU hdegreeU x)
  have heV : G.SelectedSeed seed'.1 = G.IncidentSeed V seed' := by
    funext x
    exact propext (G.selectedSeed_iff_incidentSeed V seed' hdV hdegreeV x)
  rw [heU, heV]
  exact incidentSeed_pair_exact G U V hG hUV hU hV seed seed'

/-- The normalized cycle-indicator mixed moment is exactly its two geometric
weights times the actual link factor. -/
theorem normalizedSelectedSeed_pair (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (seed : G.internalCycleSpace U) (seed' : G.internalCycleSpace V)
    (hdU : ∀ v ∈ U, G.selectedDegree seed.1.1 v = 2)
    (hdV : ∀ v ∈ V, G.selectedDegree seed'.1.1 v = 2)
    (hdegreeU : ∀ v ∈ U, G.degree v ≤ 3) (hdegreeV : ∀ v ∈ V, G.degree v ≤ 3) :
    average (fun x => G.normalizedSeedIndicator seed.1 x * G.normalizedSeedIndicator seed'.1 x) =
      dyadic ((Nat.card (Links G U V) : ℤ) - 1) *
        (1 / (2 : ℝ) ^ (G.seedSupport seed.1).card) *
          (1 / (2 : ℝ) ^ (G.seedSupport seed'.1).card) := by
  apply normalizedIndicator_joint_of_ratio
  · exact (lt_of_lt_of_le (by positivity) (G.selectedSeed_probability_ge seed.1)).ne'
  · exact (lt_of_lt_of_le (by positivity) (G.selectedSeed_probability_ge seed'.1)).ne'
  · exact selectedSeed_pair_exact G U V hG hUV hU hV seed seed' hdU hdV hdegreeU hdegreeV

end Erdos1016.FiniteMultiGraph.SeedPairCorrelation

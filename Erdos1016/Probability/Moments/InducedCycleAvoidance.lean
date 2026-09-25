import Erdos1016.Graph.Multigraph.InducedCycleSeeds
import Erdos1016.Cycles.Counting.LengthIndexedFamily
import Erdos1016.Probability.Moments.SeedFamilyAvoidance

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The actual induced-cycle weighted avoidance estimate

All bounded-length physical cycles of the retained graph are lifted to the
ambient uniform multigraph cycle space. Their means are exactly the trace
weights, and the high-girth vertex estimate supplies the exceptional-row load.
Only the geometric link-factor envelope remains as an input.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph.InducedCycleAvoidance
open BoundaryDecay BoundaryTrace Proof Nonbacktracking
open InducedSimpleRealization

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

local notation "H" => graph G R hloop hsimple

abbrev Index := LengthIndexedFamily.Index H

def region (i : Index G R hloop hsimple) : Finset G.Vertex :=
  cycleRegion G R hloop hsimple (LengthIndexedFamily.cycle H i)

def seed (i : Index G R hloop hsimple) : G.internalCycleSpace (region G R hloop hsimple i) :=
  cycleSeed G R hloop hsimple (LengthIndexedFamily.cycle H i)

@[simp] theorem weight_eq (i : Index G R hloop hsimple) :
    SeedFamilyAvoidance.weight G (region G R hloop hsimple) (seed G R hloop hsimple) i =
      1 / (2 : ℝ) ^ BoundaryDecay.Cycle.length (LengthIndexedFamily.cycle H i) := by
  unfold SeedFamilyAvoidance.weight seed
  rw [cycleSeed_support_card]

theorem vertex_load_le (hmax : ∀ v, (H).degree v ≤ 3) (D L s : ℕ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (v : G.Vertex) :
    (∑ i ∈ LengthIndexedFamily.family H L,
      if v ∈ region G R hloop hsimple i then
        SeedFamilyAvoidance.weight G (region G R hloop hsimple) (seed G R hloop hsimple) i
      else 0) ≤ (3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s := by
  classical
  by_cases hv : v ∈ R
  · let u : (H).Vertex := vertexEquiv G R ⟨v, hv⟩
    have hvertex : vertex G R hloop hsimple u = v := by simp [u, vertex]
    have he (i : Index G R hloop hsimple) : v ∈ region G R hloop hsimple i ↔
        u ∈ Cycle.vertices (LengthIndexedFamily.cycle H i) := by
      rw [← hvertex]
      exact mem_cycleRegion_vertex G R hloop hsimple _ u
    simpa only [he, weight_eq] using
      LengthIndexedFamily.vertex_weight_le H hmax D L s hg hs hshort u
  · have hz : ∀ i : Index G R hloop hsimple, v ∉ region G R hloop hsimple i := by
      intro i hi
      exact hv (cycleRegion_subset G R hloop hsimple _ hi)
    simp only [hz, if_false, Finset.sum_const_zero]
    positivity

/-- Avoiding every bounded-length retained cycle, in the actual ambient
cycle space, has the sharp weighted second-moment bound. -/
theorem avoidance_le (hG : G.toSimpleGraph.Connected)
    (hdegree : ∀ v ∈ R, G.degree v ≤ 3)
    (hmax : ∀ v, (H).degree v ≤ 3) (D L s : ℕ) (M : ℝ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (hM : 0 ≤ M)
    (hlinks : ∀ C D' : (H).CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length D' ≤ L → C ≠ D' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple D') →
      dyadic ((Nat.card (SeedPairCorrelation.Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple D')) : ℤ) - 1) ≤ M)
    (hmean : 0 < ∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell) :
    Finite.density (fun x : G.CycleSpace =>
      ∀ i ∈ LengthIndexedFamily.family H L, ¬ G.SelectedSeed (seed G R hloop hsimple i).1 x) ≤
      1 / 2 + (1 + (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) /
        (4 * (∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell) +
          2 * (1 + (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s)) := by
  classical
  have hmass : (∑ i ∈ LengthIndexedFamily.family H L,
      SeedFamilyAvoidance.weight G (region G R hloop hsimple) (seed G R hloop hsimple) i) =
      ∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell := by
    simp only [weight_eq]
    exact LengthIndexedFamily.total_weight H L
  have hn (i : Index G R hloop hsimple) (hi : i ∈ LengthIndexedFamily.family H L) :
      BoundaryDecay.Cycle.length (LengthIndexedFamily.cycle H i) ≤ L := by
    rw [LengthIndexedFamily.cycle_length]
    exact (LengthIndexedFamily.mem_family_iff H L i).mp hi |>.2
  have h := SeedFamilyAvoidance.avoidance_le G (region G R hloop hsimple) (seed G R hloop hsimple)
    (LengthIndexedFamily.family H L) L M ((3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s) hG
    (fun i hi => cycleSeed_connected G R hloop hsimple _)
    (fun i hi => cycleSeed_degree G R hloop hsimple _)
    (fun i hi v hv => hdegree v (cycleRegion_subset G R hloop hsimple _ hv))
    (fun i hi j hj he => LengthIndexedFamily.cycle_injective H
      (cycleSeed_injective G R hloop hsimple he))
    (fun i hi => by
      change (cycleRegion G R hloop hsimple _).card ≤ L
      rw [cycleRegion_card]
      exact hn i hi) hM (by positivity)
    (vertex_load_le G R hloop hsimple hmax D L s hg hs hshort)
    (fun i hi j hj hij he => hlinks _ _ (hn i hi) (hn j hj)
      (fun h => hij (LengthIndexedFamily.cycle_injective H h)) he.1)
    (hmass.symm ▸ hmean)
  rw [hmass] at h
  convert h using 1; ring


/-- The numerical form used in the final forest estimate. -/
theorem avoidance_le_half_add_twenty (hG : G.toSimpleGraph.Connected)
    (hdegree : ∀ v ∈ R, G.degree v ≤ 3)
    (hmax : ∀ v, (H).degree v ≤ 3) (D L s : ℕ) (M z : ℝ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (hM : 0 ≤ M) (hz : 0 < z)
    (hlinks : ∀ C D' : (H).CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length D' ≤ L → C ≠ D' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple D') →
      dyadic ((Nat.card (SeedPairCorrelation.Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple D')) : ℤ) - 1) ≤ M)
    (hmass : z / 64 ≤ ∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell)
    (herror : M * ((3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) ≤ 1 / 4) :
    Finite.density (fun x : G.CycleSpace =>
      ∀ i ∈ LengthIndexedFamily.family H L, ¬ G.SelectedSeed (seed G R hloop hsimple i).1 x) ≤
      1 / 2 + 20 / z := by
  have hmean : 0 < ∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell :=
    (by positivity : 0 < z / 64).trans_le hmass
  have h := avoidance_le G R hloop hsimple hG hdegree hmax D L s M hg hs hshort hM hlinks hmean
  have hη : (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s ≤ 1 / 4 := by
    nlinarith [herror]
  have hη0 : 0 ≤ (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s := by positivity
  have hbound : (1 + (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) /
      (4 * (∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell) +
        2 * (1 + (3 / 2 : ℝ) * M * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s)) ≤ 20 / z := by
    apply (div_le_div_iff₀ (by positivity) hz).2
    have hzη := mul_le_mul_of_nonneg_right hη hz.le
    nlinarith
  linarith

/-- A forest on any edge set containing the retained graph avoids all its
lifted cycles. This comparison is on the ambient uniform cycle space. -/
theorem forest_density_le_avoidance (L : ℕ) (E : Finset G.Edge)
    (hE : G.internalEdges R ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      Finite.density (fun x : G.CycleSpace =>
        ∀ i ∈ LengthIndexedFamily.family H L, ¬ G.SelectedSeed (seed G R hloop hsimple i).1 x) := by
  classical
  rw [← average_indicator, ← average_indicator]
  apply average_mono
  intro x
  by_cases hx : G.IsForestWord (G.restrictEdges E x.1)
  · have havoid : ∀ i ∈ LengthIndexedFamily.family H L,
        ¬ G.SelectedSeed (seed G R hloop hsimple i).1 x := by
      intro i hi hsel
      apply G.not_isForestWord_of_even_support (seed G R hloop hsimple i).1 _
        (G.restrictEdges E x.1) _ hx
      · intro hz
        apply cycleSeed_nonzero G R hloop hsimple (LengthIndexedFamily.cycle H i)
        exact Subtype.ext (Subtype.ext hz)
      · intro e he
        have hr : e ∈ G.internalEdges R := by
          by_contra hn
          exact he (liftWord_zero_outside G R hloop hsimple _ e hn)
        simpa only [restrictEdges, hE hr, ↓reduceIte] using hsel e he
    unfold indicator
    split_ifs <;> norm_num
  · simp only [indicator, hx, ↓reduceIte]
    split_ifs <;> norm_num

/-- The finite retained-graph forest estimate, including the paper's constant. -/
theorem forest_le_half_add_twenty (hG : G.toSimpleGraph.Connected)
    (hdegree : ∀ v ∈ R, G.degree v ≤ 3)
    (hmax : ∀ v, (H).degree v ≤ 3) (D L s : ℕ) (M z : ℝ)
    (hg : ShortWalks.GirthGreater (H).toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) (hM : 0 ≤ M) (hz : 0 < z)
    (hlinks : ∀ C D' : (H).CycleWord,
      BoundaryDecay.Cycle.length C ≤ L → BoundaryDecay.Cycle.length D' ≤ L → C ≠ D' →
      Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple D') →
      dyadic ((Nat.card (SeedPairCorrelation.Links G (cycleRegion G R hloop hsimple C)
        (cycleRegion G R hloop hsimple D')) : ℤ) - 1) ≤ M)
    (hmass : z / 64 ≤ ∑ ell ∈ Finset.Icc 1 L, SimpleRunWeight.cycleWordMassAtLength H ell)
    (herror : M * ((3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s) ≤ 1 / 4)
    (E : Finset G.Edge) (hE : G.internalEdges R ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      1 / 2 + 20 / z :=
  (forest_density_le_avoidance G R hloop hsimple L E hE).trans
    (avoidance_le_half_add_twenty G R hloop hsimple hG hdegree hmax D L s M z
      hg hs hshort hM hz hlinks hmass herror)

end Erdos1016.FiniteMultiGraph.InducedCycleAvoidance

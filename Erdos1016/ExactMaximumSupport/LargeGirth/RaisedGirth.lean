import Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirthTransfer
import Erdos1016.ExactMaximumSupport.LargeGirth.Packing

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Dyadic assembly of actual raised-girth packings

The stage lemmas use the literal selected regions and their labeled induced
graphs. The final packing estimate is supplied by the geometric packing theorem.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
open FiniteMultiGraph RegionPackingSequence GirthRaiseBounds
local instance raisedGirthDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The girth available before the next dyadic packing stage. -/
def incomingScale (D : ℕ) : ℕ→ℕ
  | 0 => D
  | n+1 => scale D n+1

theorem incomingScale_ge (D n : ℕ) : D ≤ incomingScale D n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
      have hp := Nat.one_le_two_pow (n:=n)
      change D ≤ 2^n*D+1
      nlinarith

theorem scale_le_twice_incoming (D n : ℕ) : scale D n ≤ 2*incomingScale D n := by
  cases n with
  | zero => simp only [scale,incomingScale,pow_zero,one_mul]; omega
  | succ n =>
      simp only [scale,incomingScale,pow_succ]
      nlinarith

/-- The initial labeled girth and the previous maximal packing give each
incoming labeled girth, with no simplicity assumption. -/
theorem stage_no_short (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ) (hD : 2 ≤ D) (hmax : ∀v,G.degree v ≤ 3)
    (hg : ¬(PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D) (n : ℕ) :
    ¬(PieceCore.Induced.graph G (P∪vertices G P (scale D) n)ᶜ).HasCycleShorterThan
      (incomingScale D n) := by
  cases n with
  | zero => simpa only [vertices_zero,Finset.union_empty,incomingScale] using hg
  | succ n =>
      apply vertices_no_short G P (scale D) n _ hmax
      have hp := Nat.one_le_two_pow (n:=n)
      dsimp [scale]
      nlinarith

/-- The original probability lower bound holds at every deletion stage. -/
theorem stage_probability_lower (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D n : ℕ) (q : ℝ) (hq : q ≤ G.regionForestProbability Pᶜ) :
    q ≤ G.regionForestProbability (P∪vertices G P (scale D) n)ᶜ :=
  hq.trans (exterior_probability_mono G Finset.subset_union_left)

/-- This interface isolates the actual selected-family cardinality estimate.
The geometric packing theorem will discharge it for a universal cutoff. -/
def SelectedPackingBound (G : FiniteMultiGraph) (P : Finset G.Vertex) (D₀ : ℕ) : Prop :=
  ∀ (S : Finset G.Vertex) (g d : ℕ), S⊆Pᶜ → D₀ ≤ g → 2 ≤ d → d ≤ 2*g →
    ¬(PieceCore.Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
    (2/5:ℝ) ≤ G.regionForestProbability (P∪S)ᶜ →
    (selected G (P∪S) d).card ≤ 1551*d*(S.card+1)*2^d

/-- Discharge every recurrence premise from the actual incoming girth and
probability. No recurrence or labeled girth is assumed. -/
theorem dyadic_size_of_selected_packing (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D₀ D : ℕ) (hD : 7 ≤ D) (hbase : D₀ ≤ D) (hmax : ∀v,G.degree v ≤ 3)
    (hg : ¬(PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D)
    (hq : (2/5:ℝ) ≤ G.regionForestProbability Pᶜ)
    (hpack : SelectedPackingBound G P D₀) (j : ℕ) :
    (vertices G P (scale D) (j+1)).card+1 ≤ 
      2^(2*scale D j+6*(Nat.clog 2 (scale D j))^2) := by
  apply vertices_size_bound G P D hD _ j
  intro n
  apply hpack (vertices G P (scale D) n) (incomingScale D n) (scale D n)
    (vertices_outside G P (scale D) (scale_mono D) n)
    (hbase.trans (incomingScale_ge D n)) _ (scale_le_twice_incoming D n)
    (stage_no_short G P D (by omega) hmax hg n)
    (stage_probability_lower G P D n (2/5) hq)
  have hp := Nat.one_le_two_pow (n:=n)
  dsimp [scale]
  nlinarith


/-- A nested sequence of actual maximal short-region packings. -/
structure HighGirthPackingSequence (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ) where
  family : ℕ→Finset (Finset G.Vertex)
  region : ℕ→Finset G.Vertex
  region_eq : ∀j,region j=(family j).biUnion id
  nested : Monotone region
  outside : ∀j,region j⊆Pᶜ
  spec : ∀j,∀U∈family j,G.ShortCyclicRegion P (scale D j) U
  disjoint : ∀j,∀U∈family j,∀V∈family j,U≠V→Disjoint U V
  hits : ∀j,∀U,G.ShortCyclicRegion P (scale D j) U→((region j)∩U).Nonempty
  no_short : ∀j,¬(PieceCore.Induced.graph G (P∪region j)ᶜ).HasCycleShorterThan (scale D j+1)
  size : ∀j,(region j).card+1 ≤ 2^(2*scale D j+6*(Nat.clog 2 (scale D j))^2)

/-- The geometric packing theorem supplies a universal selected-family cutoff. -/
theorem exists_selected_packing_cutoff :
    ∃D₀:ℕ,256 ≤ D₀ ∧ ∀(G:FiniteMultiGraph)(P:Finset G.Vertex),
      G.toSimpleGraph.Connected→(∀v,G.degree v=3)→
      (P=∅ ∨ (G.toSimpleGraph.induce (↑P:Set G.Vertex)).Connected)→
      SelectedPackingBound G P D₀ := by
  obtain ⟨D₀,hD₀,hbound⟩ := Packing.exists_finset_cutoff
  refine ⟨D₀,hD₀,?_⟩
  intro G P hG hcubic hP S g d _ hg hd hdg hshort hprob
  have hs := selected_spec G (P∪S) d
  exact hbound G P S g d (selected G (P∪S) d) hG hcubic hg hd hdg hP hshort hprob
    hs.2.1 (fun U hU => (hs.1 U hU).connected) (fun U hU => (hs.1 U hU).outside)
    (fun U hU => (hs.1 U hU).cyclic) (fun U hU => (hs.1 U hU).cut)

/-- Actual bounded nested high-girth packings exist with a universal cutoff.
No packing-cardinality, recurrence, or quotient-model premise remains. -/
theorem exists_raising_cutoff :
    ∃D₀:ℕ,256 ≤ D₀ ∧ ∀(G:FiniteMultiGraph)(P:Finset G.Vertex)(D:ℕ),
      G.toSimpleGraph.Connected→(∀v,G.degree v=3)→D₀ ≤ D→
      (P=∅ ∨ (G.toSimpleGraph.induce (↑P:Set G.Vertex)).Connected)→
      ¬(PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D→
      (2/5:ℝ) ≤ G.regionForestProbability Pᶜ→Nonempty (HighGirthPackingSequence G P D) := by
  obtain ⟨D₀,hD₀,hpack⟩ := exists_selected_packing_cutoff
  refine ⟨D₀,hD₀,?_⟩
  intro G P D hG hcubic hD hP hshort hprob
  have hmax (v : G.Vertex) : G.degree v ≤ 3 := (hcubic v).le
  refine ⟨{
    family := fun j => families G P (scale D) (j+1)
    region := fun j => vertices G P (scale D) (j+1)
    region_eq := fun _ => rfl
    nested := fun i j hij => vertices_mono G P (scale D) (by omega)
    outside := fun j => vertices_outside G P (scale D) (scale_mono D) (j+1)
    spec := fun j => families_spec G P (scale D) (scale_mono D) j
    disjoint := fun j => families_disjoint G P (scale D) (j+1)
    hits := fun j => RegionPackingSequence.hits G P (scale D) j
    no_short := ?_
    size := fun j => dyadic_size_of_selected_packing G P D₀ D (by omega) hD hmax
      hshort hprob (hpack G P hG hcubic hP) j }⟩
  intro j
  apply vertices_no_short G P (scale D) j _ hmax
  have hp := Nat.one_le_two_pow (n:=j)
  dsimp [scale]
  nlinarith

end Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth

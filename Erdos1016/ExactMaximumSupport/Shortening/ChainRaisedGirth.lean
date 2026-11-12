import Erdos1016.ExactMaximumSupport.Shortening.ChainPacking
import Erdos1016.ExactMaximumSupport.Shortening.ChainGirthRaiseBounds
import Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The unchanged raised-girth interface from chain packing

The selected regions and their girth properties are unchanged. Only their
cardinality estimate and its recurrence use the new chain proof. A connected
marker supplies the nonempty anchor required by the separator construction.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainRaisedGirth
open FiniteMultiGraph LargeGirth RegionPackingSequence GirthRaiseBounds RaisedGirth
local instance chainRaiseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Actual nested packings, with the same size budget as the original interface. -/
theorem exists_raising_cutoff :
    ∃ D₀ : ℕ, 256 ≤ D₀ ∧ ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ),
      G.toSimpleGraph.Connected → (∀ v,G.degree v=3) → D₀≤D →
      (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected →
      ¬(PieceCore.Induced.graph G Pᶜ).HasCycleShorterThan D →
      (2/5:ℝ)≤G.regionForestProbability Pᶜ → Nonempty (HighGirthPackingSequence G P D) := by
  obtain ⟨D₀,hD₀,hpack⟩ := ChainPacking.exists_finset_cutoff
  refine ⟨D₀,hD₀,?_⟩
  intro G P D hG hcubic hD hP hshort hprob
  have hmax (v : G.Vertex) : G.degree v≤3 := (hcubic v).le
  have hPne : P.Nonempty := by
    obtain ⟨v⟩ := hP.nonempty
    exact ⟨v.1,v.2⟩
  have hsizes (n : ℕ) :
      (selected G (P∪vertices G P (scale D) n) (scale D n)).card ≤
        150*(scale D n)^3*((vertices G P (scale D) n).card+1)*2^scale D n := by
    have hs := selected_spec G (P∪vertices G P (scale D) n) (scale D n)
    have hn : 2≤scale D n := by
      have hp := Nat.one_le_two_pow (n:=n)
      dsimp [scale]
      nlinarith
    exact hpack G P (vertices G P (scale D) n) (incomingScale D n) (scale D n)
      (selected G (P∪vertices G P (scale D) n) (scale D n)) hG hcubic
      (hD.trans (incomingScale_ge D n)) hn (scale_le_twice_incoming D n) hP hPne
      (stage_no_short G P D (by omega) hmax hshort n)
      (stage_probability_lower G P D n (2/5) hprob)
      hs.2.1 (fun U hU => (hs.1 U hU).connected) (fun U hU => (hs.1 U hU).outside)
      (fun U hU => (hs.1 U hU).cyclic) (fun U hU => (hs.1 U hU).cut)
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
    size := fun j => ChainGirthRaiseBounds.vertices_size_bound G P D (by omega) hsizes j }⟩
  intro j
  apply vertices_no_short G P (scale D) j _ hmax
  have hp := Nat.one_le_two_pow (n:=j)
  dsimp [scale]
  nlinarith

end Erdos1016.ExactMaximumSupport.Shortening.ChainRaisedGirth

import Erdos1016.ExactMaximumSupport.Shortening.LargeOrderPieces
import Erdos1016.ExactMaximumSupport.MinimalCyclicInterval

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Size and probability obstructions for separator-chain packing

All regions use the original physical labels. The two-piece estimate is applied
to the full deleted marker `P ∪ S`; only the subsequent separator geometry
needs the connected part `P`. Taking `max d 4` covers boundaries two and three.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.ChainPackingBounds
open FiniteMultiGraph LargeGirth LargeGirth.PieceCore

local instance chainBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- An actual cyclic induced region has at least its inherited girth in vertices. -/
theorem cyclic_region_card (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (g : ℕ) (hg : 3 ≤ g)
    (hshort : ¬ (Induced.graph G X).HasCycleShorterThan g)
    (hcyc : ∃ z : G.internalCycleSpace X, z ≠ 0) : g ≤ X.card := by
  obtain ⟨z, hz⟩ := hcyc
  let K := Induced.graph G X
  change ¬ K.HasCycleShorterThan g at hshort
  let y : K.CycleSpace := (PoleProduct.cycleEquiv G X).symm z
  have hy : y.1 ≠ 0 := by
    intro h
    have he : y = 0 := Subtype.ext h
    apply hz
    have hh := congrArg (PoleProduct.cycleEquiv G X) he
    simpa only [y, LinearEquiv.apply_symm_apply, map_zero] using hh
  have hloop : K.IsLoopless := noLoops_of_no_short_cycle K
    (no_short_three_of_le K g hg hshort)
  have hf : ¬ K.IsForestWord (K.restrictEdges (K.internalEdges Finset.univ) (fun _ => 1)) := by
    intro hf
    apply hy
    apply (K.isForestWord_iff_no_even_support _).1 hf y
    intro e _
    simp [restrictEdges, internalEdges]
  obtain ⟨x, hx, _⟩ := MinimalCyclicInterval.hasCycleIn_of_not_forest K hloop Finset.univ hf
  have hlen : g ≤ K.wordLength x := by
    by_contra hn
    exact hshort ⟨x, hx, by omega⟩
  have hc := Finset.card_le_univ (CycleRegions.region K x)
  rw [CycleRegions.cycle_region_card K x hx] at hc
  have hn : Fintype.card K.Vertex = X.card := by
    simp [FiniteMultiGraph.Vertex, K]
  omega

/-- The chain block size works also for `d = 2, 3`, where the pole theorem's
real scale must be at least four. -/
theorem block_scale (g d : ℕ) (hg : 4 ≤ g) (hd : 2 ≤ d) (hdg : d ≤ 2*g) :
    8*(max d 4)^2 ≤ 16*d*g := by
  by_cases h : 4 ≤ d
  · rw [max_eq_left h]
    nlinarith [Nat.mul_le_mul_left (8*d) hdg]
  · rw [max_eq_right (by omega : d ≤ 4)]
    nlinarith [Nat.mul_le_mul hd hg]

/-- Scalar constant in the chain contradiction, using the parity-sharp
region-event lower bound `2^(-d)`. -/
theorem packing_constant (d s : ℕ) (hd : 2 ≤ d) :
    3*d*((d+s+2)*(16*d+1))+6*d ≤ 150*d^3*(s+1) := by
  have h1 : d+s+2 ≤ 2*d*(s+1) := by nlinarith
  have h2 : 16*d+1 ≤ 17*d := by omega
  have h3 := Nat.mul_le_mul h1 h2
  have h4 := Nat.mul_le_mul_left (3*d) h3
  have h5 : 1 ≤ d^2*(s+1) := by
    have : 0 < d^2*(s+1) := by positivity
    omega
  have h6 := Nat.mul_le_mul_left (6*d) h5
  nlinarith

/-- Two disjoint clean chain blocks contradict forest probability two fifths.
No connectedness assumption on either block is used. -/
theorem exists_block_obstruction_constant :
    ∃ C : ℝ, 0 < C ∧
    ∀ (G : FiniteMultiGraph) (P S : Finset G.Vertex) (g d : ℕ)
      (X : Fin 2 → Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) →
      4 ≤ g → 2 ≤ d → d ≤ 2*g →
      C*Real.logb 2 ((max d 4 : ℕ)+2) ≤ g →
      ¬ (Induced.graph G (P∪S)ᶜ).HasCycleShorterThan g →
      Disjoint (X 0) (X 1) →
      (∀ i, Disjoint (X i) (P∪S)) →
      (∀ i, 16*d*g ≤ (X i).card) →
      (∀ i, (G.cutEdges (X i)).card ≤ 2*d) →
      G.regionForestProbability (P∪S)ᶜ < 2/5 := by
  obtain ⟨C, hC, hbound⟩ := LargeOrderPieces.exists_constant
  refine ⟨C, hC, ?_⟩
  intro G P S g d X hG hcubic hg hd hdg hlog hshort hdisj hclean hsize hcut
  have hsub (i : Fin 2) : X i ⊆ (P∪S)ᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun h => Finset.disjoint_left.mp (hclean i) hv h)
  apply (hbound G (P∪S) X (fun _ => g) hG hcubic hdisj hsub
    (fun i => Induced.no_short_mono G (P∪S)ᶜ (X i) (hsub i) g (by omega) hshort) ?_).2
  intro i
  refine ⟨(max d 4 : ℕ), ?_, ?_, ?_, hlog⟩
  · exact_mod_cast (le_max_right d 4)
  · exact_mod_cast ((block_scale g d hg hd hdg).trans (hsize i))
  · exact_mod_cast ((hcut i).trans (Nat.mul_le_mul_left 2 (le_max_left d 4)))

end Erdos1016.ExactMaximumSupport.Shortening.ChainPackingBounds

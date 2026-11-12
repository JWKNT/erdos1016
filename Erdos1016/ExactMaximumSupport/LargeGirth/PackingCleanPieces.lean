import Erdos1016.ExactMaximumSupport.LargeGirth.SmallBoundaryPieces
import Erdos1016.ExactMaximumSupport.LargeGirth.BlockGeometry

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Two clean pieces in a long packing family

The finite selection uses literal disjoint vertex sets. At most one set meets
the marker, and each remaining discarded set consumes a distinct bad vertex.
The selected induced graphs inherit the exterior girth before the existing
two-piece forest bound is applied.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingCleanPieces
open FiniteMultiGraph PieceCore PieceCore.Induced
local instance packingCleanDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Select two literal clean members; no clean-family hypothesis is assumed. -/
theorem exists_two_clean {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (F : Finset ι) (X : ι → Finset V) (P S : Finset V)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (X i) (X j))
    (hP : (F.filter fun i => ¬ Disjoint (X i) P).card ≤ 1)
    (hcard : S.card + 3 ≤ F.card) :
    ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ Disjoint (X i) (P ∪ S) ∧
      Disjoint (X j) (P ∪ S) := by
  classical
  let A := F.filter fun i => Disjoint (X i) P
  let B := A.filter fun i => Disjoint (X i) S
  have hAP : F.card ≤ A.card + 1 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card (s := F)
      (fun i => Disjoint (X i) P)
    change F.card ≤ (F.filter fun i => Disjoint (X i) P).card + 1
    omega
  have hAB : A.card ≤ B.card + S.card := by
    apply clean_blocks_card_ge A X S
    intro i hi j hj hij
    exact hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
  have hB : 1 < B.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hB
  have hclean (k : ι) (hk : k ∈ B) : k ∈ F ∧ Disjoint (X k) (P ∪ S) := by
    have hka := (Finset.mem_filter.mp hk).1
    have hkp := (Finset.mem_filter.mp hka).2
    exact ⟨(Finset.mem_filter.mp hka).1,
      Finset.disjoint_union_right.mpr ⟨hkp, (Finset.mem_filter.mp hk).2⟩⟩
  exact ⟨i, (hclean i hi).1, j, (hclean j hj).1, hij,
    (hclean i hi).2, (hclean j hj).2⟩

/-- A sufficiently long actual family gives the two-piece probability bound. -/
theorem exists_obstruction_cutoff :
    ∃ D : ℕ, 256 ≤ D ∧
    ∀ {ι : Type*} [DecidableEq ι] (G : FiniteMultiGraph)
      (P S : Finset G.Vertex) (g : ℕ) (F : Finset ι) (X : ι → Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) → D ≤ g →
      ¬ (graph G (P ∪ S)ᶜ).HasCycleShorterThan g →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (X i) (X j)) →
      (∀ i ∈ F, (G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected) →
      (∀ i ∈ F, 256 ≤ (graph G (X i)).cycleRank) →
      (∀ i ∈ F, (G.cutEdges (X i)).card ≤ 4*g) →
      (F.filter fun i => ¬ Disjoint (X i) P).card ≤ 1 →
      S.card + 3 ≤ F.card →
      G.regionForestProbability (P ∪ S)ᶜ ≤ 9/25 ∧
        G.regionForestProbability (P ∪ S)ᶜ < 2/5 := by
  obtain ⟨D, C, hD, _, hbound⟩ := SmallBoundaryPieces.exists_constants
  refine ⟨D, hD, ?_⟩
  intro ι _ G P S g F X hG hcubic hg hshort hdisj hconn hrank hcut hP hcard
  obtain ⟨i, hi, j, hj, hij, hci, hcj⟩ := exists_two_clean F X P S hdisj hP hcard
  let Y : Fin 2 → Finset G.Vertex := fun a => if a = 0 then X i else X j
  have hsub (a : Fin 2) : Y a ⊆ (P ∪ S)ᶜ := by
    have hd : Disjoint (Y a) (P ∪ S) := by
      fin_cases a <;> simp only [Y, ↓reduceIte, Fin.zero_eta, Fin.isValue] <;> assumption
    intro v hv
    exact Finset.mem_compl.mpr (fun hm => Finset.disjoint_left.mp hd hv hm)
  apply hbound G (P ∪ S) Y (fun _ => g) hG hcubic ?_ hsub ?_ ?_
  · simpa [Y] using hdisj i hi j hj hij
  · intro a
    exact Induced.no_short_mono G (P ∪ S)ᶜ (Y a) (hsub a) g (by omega) hshort
  · intro a
    left
    fin_cases a <;> simp only [Y, ↓reduceIte, Fin.zero_eta, Fin.isValue]
    · exact ⟨hconn i hi, hrank i hi, hcut i hi, hg⟩
    · exact ⟨hconn j hj, hrank j hj, hcut j hj, hg⟩

/-- At forest density at least two fifths, at most two pieces survive the bad-set budget. -/
theorem exists_cardinality_cutoff :
    ∃ D : ℕ, 256 ≤ D ∧
    ∀ {ι : Type*} [DecidableEq ι] (G : FiniteMultiGraph)
      (P S : Finset G.Vertex) (g : ℕ) (F : Finset ι) (X : ι → Finset G.Vertex),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) → D ≤ g →
      ¬ (graph G (P ∪ S)ᶜ).HasCycleShorterThan g →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (X i) (X j)) →
      (∀ i ∈ F, (G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected) →
      (∀ i ∈ F, 256 ≤ (graph G (X i)).cycleRank) →
      (∀ i ∈ F, (G.cutEdges (X i)).card ≤ 4*g) →
      (F.filter fun i => ¬ Disjoint (X i) P).card ≤ 1 →
      (2/5 : ℝ) ≤ G.regionForestProbability (P ∪ S)ᶜ → F.card ≤ S.card + 2 := by
  obtain ⟨D, hD, hbound⟩ := exists_obstruction_cutoff
  refine ⟨D, hD, ?_⟩
  intro ι _ G P S g F X hG hcubic hg hshort hdisj hconn hrank hcut hP hprob
  by_contra hn
  have hh := hbound G P S g F X hG hcubic hg hshort hdisj hconn hrank hcut hP (by omega)
  exact not_lt_of_ge hprob hh.2

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingCleanPieces

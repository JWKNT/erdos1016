import Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringIntervals
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotientLift
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingRegionRank
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingCleanPieces

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Actual ambient pieces supplied by a long quotient string

The quotient has the original packing regions as marked fibers. Each
selected interval contains 256 distinct marked fibers. Their internal even
words supply actual induced rank after lifting. The endpoint cut bound and
the marker count use the physical quotient-lifting theorems.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringLift
open FiniteMultiGraph TerminalStrings PackingStringIntervals
local instance stringLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι → Finset G.Vertex)
variable {R : Finset (PackingQuotient.graph G X).Vertex}
variable (s : OrderedString (PackingQuotient.graph G X).toSimpleGraph ∅ R)
variable (m : ℕ) (hlen : 258*m ≤ s.length)

/-- The full inverse image of the deterministic quotient interval. -/
def region (b : Fin m) : Finset G.Vertex :=
  PackingQuotient.lift G X (interval s m hlen b)

theorem region_connected
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected)
    (b : Fin m) : (G.toSimpleGraph.induce (↑(region G X s m hlen b) : Set G.Vertex)).Connected :=
  PackingQuotient.lift_connected G X hdisj hconn _ (interval_connected s m hlen b)

theorem regions_disjoint : Pairwise (fun b c =>
    Disjoint (region G X s m hlen b) (region G X s m hlen c)) := by
  intro b c hbc
  exact PackingQuotient.lift_disjoint G X (intervals_disjoint s m hlen hbc)

/-- Interior marks recover distinct cyclic packing fibers in the lifted region. -/
theorem region_rank_ge
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hcyc : ∀ i, ∃ z : G.internalCycleSpace (X i), z ≠ 0)
    (hR : ∀ v ∈ R, ∃ i, PackingQuotient.mark G X i = v)
    (b : Fin m) : 256 ≤ (PieceCore.Induced.graph G (region G X s m hlen b)).cycleRank := by
  have hex (t : Fin 256) : ∃ i, PackingQuotient.mark G X i = interiorVertex s m hlen b t :=
    hR _ (interior_relevant s m hlen b t)
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro t u he
    apply interior_injective s m hlen b
    rw [← hf t, ← hf u, he]
  have hsub (t : Fin 256) : X (f t) ⊆ region G X s m hlen b := by
    apply PackingQuotient.selected_subset_lift G X hdisj
    rw [hf t]
    exact interior_mem s m hlen b t
  have hpair : Pairwise (fun t u : Fin 256 => Disjoint (X (f t)) (X (f u))) := by
    intro t u htu
    exact hdisj (fun he => htu (hfinj he))
  simpa only [Fintype.card_fin] using PackingRegionRank.card_le_induced_cycleRank G
    (region G X s m hlen b) (fun t => X (f t)) hsub hpair (fun t => hcyc (f t))

/-- Only the two endpoint fibers contribute to the physical cut. -/
theorem region_cut_le
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hR : ∀ v ∈ R, ∃ i, PackingQuotient.mark G X i = v)
    (d : ℕ) (hcut : ∀ i, (G.cutEdges (X i)).card ≤ d) (b : Fin m) :
    (G.cutEdges (region G X s m hlen b)).card ≤ 2*d := by
  obtain ⟨i, hi⟩ := hR _ (s.relevant (leftIndex s m hlen b))
  obtain ⟨j, hj⟩ := hR _ (s.relevant (rightIndex s m hlen b))
  apply PackingQuotient.lift_cut_card_le G X hdisj (interval s m hlen b) i j
  · rw [hi]
    exact (interval_avoids s m hlen b).1
  · rw [hj]
    exact (interval_avoids s m hlen b).2
  · intro u hu w huw hw
    simpa only [hi, hj] using interval_boundary s m hlen b hu huw hw
  · exact hcut i
  · exact hcut j

/-- An empty or connected clean marker meets at most one lifted interval. -/
theorem marker_bad_card_le_one
    (P : Finset G.Vertex)
    (hP : P = ∅ ∨ (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected)
    (hPX : ∀ i, Disjoint P (X i)) :
    (Finset.univ.filter fun b : Fin m => ¬ Disjoint (region G X s m hlen b) P).card ≤ 1 := by
  rcases hP with rfl | hP
  · simp
  · exact PackingQuotient.marker_bad_card_le_one G X Finset.univ (interval s m hlen)
      (fun b _ c _ hbc => intervals_disjoint s m hlen hbc) P hP hPX

/-- The actual long-string contradiction, with a cutoff uniform in all inputs. -/
theorem exists_length_cutoff :
    ∃ D : ℕ, 256 ≤ D ∧
    ∀ (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι → Finset G.Vertex)
      (P S : Finset G.Vertex) (g d : ℕ),
      G.toSimpleGraph.Connected → (∀ v, G.degree v = 3) → D ≤ g → d ≤ 2*g →
      (P = ∅ ∨ (G.toSimpleGraph.induce (↑P : Set G.Vertex)).Connected) →
      ¬ (PieceCore.Induced.graph G (P ∪ S)ᶜ).HasCycleShorterThan g →
      (2/5 : ℝ) ≤ G.regionForestProbability (P ∪ S)ᶜ →
      Pairwise (fun i j => Disjoint (X i) (X j)) →
      (∀ i, (G.toSimpleGraph.induce (↑(X i) : Set G.Vertex)).Connected) →
      (∀ i, X i ⊆ (P ∪ S)ᶜ) →
      (∀ i, ∃ z : G.internalCycleSpace (X i), z ≠ 0) →
      (∀ i, (G.cutEdges (X i)).card ≤ d) →
      ∀ (R : Finset (PackingQuotient.graph G X).Vertex),
      (∀ v ∈ R, ∃ i, PackingQuotient.mark G X i = v) →
      ∀ s : OrderedString (PackingQuotient.graph G X).toSimpleGraph ∅ R,
        s.length < 258*(S.card+3) := by
  obtain ⟨D, hD, hbound⟩ := PackingCleanPieces.exists_cardinality_cutoff
  refine ⟨D, hD, ?_⟩
  intro G ι _ X P S g d hG hcubic hg hd hP hshort hprob hdisj hconn hXP hcyc hcut R hR s
  by_contra hn
  have hlen : 258*(S.card+3) ≤ s.length := by omega
  have hPX (i : ι) : Disjoint P (X i) := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvX
    exact (Finset.mem_compl.mp (hXP i hvX)) (Finset.mem_union_left S hvP)
  have hh := hbound G P S g (Finset.univ : Finset (Fin (S.card+3)))
    (region G X s (S.card+3) hlen) hG hcubic hg hshort
    (fun b _ c _ hbc => regions_disjoint G X s (S.card+3) hlen hbc)
    (fun b _ => region_connected G X s (S.card+3) hlen hdisj hconn b)
    (fun b _ => region_rank_ge G X s (S.card+3) hlen hdisj hcyc hR b)
    (fun b _ => (region_cut_le G X s (S.card+3) hlen hdisj hR d hcut b).trans (by omega))
    (marker_bad_card_le_one G X s (S.card+3) hlen P hP hPX) hprob
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  omega

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringLift

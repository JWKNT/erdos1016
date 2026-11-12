import Erdos1016.PolynomialBound.ParallelLinks
import Erdos1016.PolynomialBound.TwoLinkMoment
import Erdos1016.ExactMaximumSupport.Averaging

set_option autoImplicit false

/-!
# Orienting actual two-link pairs towards an anchor

If a connected set lies outside the anchor component after another connected
set is deleted, the reverse relation cannot hold. Applied to the symmetric
two-link kernel, this leaves at least half its weight in the near direction.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.LargeGirth

open PolynomialBound.Separation PolynomialBound.ParallelLinks
open FiniteMultiGraph FiniteMultiGraph.SeedPairCorrelation
open PolynomialBound.TwoLinkMoment BoundaryDecay BoundaryTrace

local instance orientationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A far set forces the first connected set into the anchor component of
its complement. The first-hit path supplies the connection to the anchor. -/
theorem far_forces_near {V : Type*} (H : SimpleGraph V) (p : V) (A B : Set V)
    (hH : H.Connected) (hA : IsConnectedSet H A) (hne : A.Nonempty)
    (hp : p ∉ A) (hd : Disjoint A B) (hfar : Disjoint B (side H A p)) :
    A ⊆ side H B p := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨w⟩ := hH.preconnected p a
  obtain ⟨z, x, hz, hzx, hx⟩ := exists_first_hit w hp ⟨a, w.end_mem_support, ha⟩
  have hzB : AvoidReach H B p z := avoidReach_of_side_disjoint hz hfar
  have hxB : x ∉ B := fun hb => Set.disjoint_left.mp hd hx hb
  have hpx : AvoidReach H B p x := hzB.step hzx hxB
  intro y hy
  exact hpx.trans (hA.avoidReach hd hx hy)

/-- Both orientations cannot be far from the same anchor. -/
theorem not_both_far {V : Type*} (H : SimpleGraph V) (p : V) (A B : Set V)
    (hH : H.Connected) (hA : IsConnectedSet H A) (hne : A.Nonempty)
    (hp : p ∉ A) (hd : Disjoint A B) :
    ¬ (Disjoint B (side H A p) ∧ Disjoint A (side H B p)) := by
  rintro ⟨hAB, hBA⟩
  obtain ⟨a, ha⟩ := hne
  exact Set.disjoint_left.mp hBA ha (far_forces_near H p A B hH hA ⟨a, ha⟩ hp hd hAB ha)

/-- The exact correlation law proves symmetry of the actual quotient-link
cardinality. No identification of quotient vertex labels is needed. -/
theorem links_card_symm (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hd : Disjoint A B)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected) :
    Nat.card (Links G A B) = Nat.card (Links G B A) := by
  have hAB := normalizedIncidentSeed_pair G A B hG hd hA hB 0 0 1 1
  have hBA := normalizedIncidentSeed_pair G B A hG hd.symm hB hA 0 0 1 1
  simp only [mul_one] at hAB hBA
  have heq : dyadic ((Nat.card (Links G A B) : ℤ) - 1) =
      dyadic ((Nat.card (Links G B A) : ℤ) - 1) := by
    rw [← hAB, ← hBA]
    congr 1
    funext x
    exact mul_comm _ _
  have hexp := (zpow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective heq
  omega

variable {ι : Type*} (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)

/-- Symmetry of the literal zero-one two-link kernel. -/
theorem twoLink_symm (i j : ι) (hG : G.toSimpleGraph.Connected)
    (hi : (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hj : (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected) :
    twoLink G U i j = twoLink G U j i := by
  by_cases hd : Disjoint (U i) (U j)
  · have hc := links_card_symm G (U i) (U j) hG hd hi hj
    simp only [twoLink, hd, hd.symm, true_and, and_true, hc, ne_comm]
  · have hd' : ¬ Disjoint (U j) (U i) := fun h => hd h.symm
    simp [twoLink, hd, hd']

/-- The far orientation restricted to the actual two-link pairs. -/
def farTwoLink (p : G.Vertex) (i j : ι) : ℝ :=
  if Disjoint (↑(U j) : Set G.Vertex) (side G.toSimpleGraph (↑(U i)) p)
  then twoLink G U i j else 0

/-- Opposite far orientations together use at most one copy of the
two-link kernel, with its actual component interpretation. -/
theorem farTwoLink_add_reverse_le (p : G.Vertex) (i j : ι)
    (hG : G.toSimpleGraph.Connected)
    (hi : (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hj : (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected)
    (hp : p ∉ U i) :
    farTwoLink G U p i j + farTwoLink G U p j i ≤ twoLink G U i j := by
  have hsymm := twoLink_symm G U i j hG hi hj
  rcases twoLink_eq_zero_or_one G U i j with hz | hone
  · simp only [farTwoLink, ← hsymm, hz]
    split_ifs <;> norm_num
  · have hd := ((twoLink_eq_one_iff G U i j).mp hone).2.1
    have hnot := not_both_far G.toSimpleGraph p (↑(U i)) (↑(U j)) hG
      (isConnectedSet_of_induce hi)
      (by obtain ⟨v⟩ := hi.nonempty; exact ⟨v.1, v.2⟩) hp
      (by exact_mod_cast hd)
    simp only [farTwoLink, ← hsymm, hone]
    split_ifs with h1 h2
    · exact (hnot ⟨h1, h2⟩).elim
    · norm_num
    · norm_num
    · norm_num

/-- Far two-link pairs carry at most half the complete two-link weight. -/
theorem farTwoLink_weight_le_half (p : G.Vertex) (s : Finset ι) (a : ι → ℝ)
    (hG : G.toSimpleGraph.Connected)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hp : ∀ i ∈ s, p ∉ U i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    2 * (∑ i ∈ s, ∑ j ∈ s, farTwoLink G U p i j * (a i * a j)) ≤
      ∑ i ∈ s, ∑ j ∈ s, twoLink G U i j * (a i * a j) := by
  exact Averaging.oriented_weight_le_half_kernel s a (farTwoLink G U p)
    (twoLink G U) ha (fun i hi j hj =>
      farTwoLink_add_reverse_le G U p i j hG (hconn i hi) (hconn j hj) (hp i hi))

end Erdos1016.ExactMaximumSupport.LargeGirth

import Erdos1016.ExactMaximum.PoleMatchings
import Erdos1016.ExactMaximumSupport.InterfaceMatchings
import Erdos1016.ExactMaximumSupport.NetworkMultiplicity
import Erdos1016.ExactMaximumSupport.LayerMatchingCount

set_option autoImplicit false

/-!
# Actual matching bounds between ordinary layers

Physical multiplicity bounds supply the two-by-two inequalities. Exact
labelled matching enumeration then gives the original network statement.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport
namespace LayerMatchingInput

open BoundaryTrace BoundaryTrace.Network
local instance matchingInputDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E) (s t : V)

omit [Fintype V] in
private theorem degree_le_three (hN : N.IsBridgelessTwoPole s t) (v : V) :
    N.deg (fun _ => 1) v ≤ 3 := by
  by_cases hs : v = s
  · subst v; have := hN.deg_s; omega
  by_cases ht : v = t
  · subst v; have := hN.deg_t; omega
  exact (hN.deg_other v hs ht).le

omit [Fintype E] in
/-- Enumerate the two actual vertices in a thin distance layer. -/
theorem two_vertices_of_layer_card (j : ℕ)
    (hj : Nat.card {v : V // N.graph.dist s v = j} = 2) :
    ∃ a b : V, a ≠ b ∧ N.graph.dist s a = j ∧ N.graph.dist s b = j ∧
      ∀ v : V, N.graph.dist s v = j ↔ v = a ∨ v = b := by
  have hc : (Finset.univ.filter fun v : V => N.graph.dist s v = j).card = 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hj
  obtain ⟨a,b,hab,heq⟩ := Finset.card_eq_two.mp hc
  have hiff (v : V) : N.graph.dist s v = j ↔ v = a ∨ v = b := by
    have hmem : N.graph.dist s v = j ↔ v ∈
        (Finset.univ.filter fun w : V => N.graph.dist s w = j) := by simp
    rw [heq] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  exact ⟨a,b,hab,(hiff a).mpr (Or.inl rfl),(hiff b).mpr (Or.inr rfl),hiff⟩

omit [Fintype V] in
/-- The actual interface permanent is at most two. -/
theorem permanent_le_two (hN : N.IsBridgelessTwoPole s t) (l : ℕ)
    (hord : N.IsOrdinaryLayer s t l) (a b c d : V) (hab : a ≠ b) (hcd : c ≠ d)
    (ha : N.graph.dist s a = l) (hb : N.graph.dist s b = l)
    (hc : N.graph.dist s c = l+1) (hd : N.graph.dist s d = l+1) :
    (Nat.card {e : E // N.Joins e a c}) * (Nat.card {e : E // N.Joins e b d}) +
      (Nat.card {e : E // N.Joins e a d}) * (Nat.card {e : E // N.Joins e b c}) ≤ 2 := by
  apply InterfaceMatchings.matching_count_le_two
  · exact NetworkMultiplicity.next_layer_pair_count_le_two N s a c d l
      hN.connected ha hord.1.1 hc hd hcd (degree_le_three N s t hN a)
  · exact NetworkMultiplicity.next_layer_pair_count_le_two N s b c d l
      hN.connected hb hord.1.1 hc hd hcd (degree_le_three N s t hN b)
  · rintro ⟨hA,hB⟩
    have hpA : N.OnParallel a := hA.elim
      (fun h => (NetworkMultiplicity.onParallel_of_two_le_joins_card N a c h).1)
      (fun h => (NetworkMultiplicity.onParallel_of_two_le_joins_card N a d h).1)
    have hpB : N.OnParallel b := hB.elim
      (fun h => (NetworkMultiplicity.onParallel_of_two_le_joins_card N b c h).1)
      (fun h => (NetworkMultiplicity.onParallel_of_two_le_joins_card N b d h).1)
    exact hab (hord.2 a b ha hb hpA hpB)

omit [Fintype V] in
/-- Two adjacent actual interface permanents have sum at most three. -/
theorem adjacent_permanent_sum_le_three (hN : N.IsBridgelessTwoPole s t) (l : ℕ)
    (hord : N.IsOrdinaryLayer s t (l+1)) (a b c d u v : V)
    (hab : a ≠ b) (hcd : c ≠ d) (huv : u ≠ v)
    (ha : N.graph.dist s a = l) (hb : N.graph.dist s b = l)
    (hc : N.graph.dist s c = l+1) (hd : N.graph.dist s d = l+1)
    (hu : N.graph.dist s u = l+2) (hv : N.graph.dist s v = l+2) :
    ((Nat.card {e : E // N.Joins e a c}) * (Nat.card {e : E // N.Joins e b d}) +
      (Nat.card {e : E // N.Joins e a d}) * (Nat.card {e : E // N.Joins e b c})) +
    ((Nat.card {e : E // N.Joins e c u}) * (Nat.card {e : E // N.Joins e d v}) +
      (Nat.card {e : E // N.Joins e c v}) * (Nat.card {e : E // N.Joins e d u})) ≤ 3 := by
  have hau : a ≠ u := by intro h; subst u; omega
  have hav : a ≠ v := by intro h; subst v; omega
  have hbu : b ≠ u := by intro h; subst u; omega
  have hbv : b ≠ v := by intro h; subst v; omega
  have hsum (w : V) :
      (Nat.card {e : E // N.Joins e a w}) + (Nat.card {e : E // N.Joins e b w}) +
      (Nat.card {e : E // N.Joins e w u}) + (Nat.card {e : E // N.Joins e w v}) ≤ 3 := by
    have hs := NetworkMultiplicity.sum_joins_card_le_degree N w ({a,b,u,v} : Finset V)
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
      hab,hau,hav,hbu,hbv,huv,false_or,not_false_eq_true] at hs
    rw [NetworkMultiplicity.joins_card_symm N w a,
      NetworkMultiplicity.joins_card_symm N w b] at hs
    have hdeg := degree_le_three N s t hN w
    omega
  apply InterfaceMatchings.adjacent_matching_sum_le_three
  · exact hsum c
  · exact hsum d
  · rintro ⟨hC,hD⟩
    have hpC : N.OnParallel c := by
      rcases hC with h | h | h | h
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N a c h).2
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N b c h).2
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N c u h).1
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N c v h).1
    have hpD : N.OnParallel d := by
      rcases hD with h | h | h | h
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N a d h).2
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N b d h).2
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N d u h).1
      · exact (NetworkMultiplicity.onParallel_of_two_le_joins_card N d v h).1
    exact hcd (hord.2 c d hc hd hpC hpD)

end LayerMatchingInput

/-- The paper's matching paragraph, with actual labelled matching words. -/
theorem layerMatchingStatement : ExactMaximum.LayerMatchingStatement := by
  classical
  intro V E _ _ N s t hN l hl hl1
  obtain ⟨a,b,hab,ha,hb,hleft⟩ :=
    LayerMatchingInput.two_vertices_of_layer_card N s l hl.1.2.2
  obtain ⟨c,d,hcd,hc,hd,hright⟩ :=
    LayerMatchingInput.two_vertices_of_layer_card N s (l+1) hl1.1.2.2
  have hac : a ≠ c := by intro h; subst c; omega
  have had : a ≠ d := by intro h; subst d; omega
  have hbc : b ≠ c := by intro h; subst c; omega
  have hbd : b ≠ d := by intro h; subst d; omega
  have hcount := LayerMatchingCount.card_layerMatching N s l a b c d
    hab hac had hbc hbd hcd hleft hright
  constructor
  · rw [hcount]
    exact LayerMatchingInput.permanent_le_two N s t hN l hl a b c d hab hcd ha hb hc hd
  · intro hl2
    obtain ⟨u,v,huv,hu,hv,hlast⟩ :=
      LayerMatchingInput.two_vertices_of_layer_card N s (l+2) hl2.1.2.2
    have hcu : c ≠ u := by intro h; subst u; omega
    have hcv : c ≠ v := by intro h; subst v; omega
    have hdu : d ≠ u := by intro h; subst u; omega
    have hdv : d ≠ v := by intro h; subst v; omega
    have hcount2 := LayerMatchingCount.card_layerMatching N s (l+1) c d u v
      hcd hcu hcv hdu hdv huv hright (by simpa only [Nat.add_assoc] using hlast)
    rw [hcount,hcount2]
    exact LayerMatchingInput.adjacent_permanent_sum_le_three N s t hN l hl1
      a b c d u v hab hcd huv ha hb hc hd hu hv

end Erdos1016.ExactMaximumSupport

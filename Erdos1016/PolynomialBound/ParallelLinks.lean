import Erdos1016.Probability.Avoidance.ExteriorCyclicCount
import Erdos1016.Probability.Moments.PairLinkCount
import Erdos1016.PolynomialBound.Separation

set_option autoImplicit false

/-!
# Link components between two connected sets are independent

Let `A` and `B` be connected vertex sets of a connected multigraph, and let
`c₀` be a component of the graph without `A ∪ B` that has an edge to `A` and
an edge to `B`. Then the deletion of any two other components `c`, `d` leaves
a connected graph. Thus `c` and `d` have exactly one link in the sense of the
pair correlation law, and their zero-cut events are independent.

A second-moment bound for pairwise independent events then gives a count
that does not depend on the forest excess: if the forest probability outside
a marked set exceeds one half, at most `2 ^ (t + 1)` components that join `A`
and `B` are cyclic, avoid the marked set, and have at most `t` cut edges.

The earlier count `(t + 1) 2 ^ t / (2 ε)` needed a forest excess `ε`. The new
count is what the polynomial error bound needs, because there `ε` is a
negative power of the rank.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PolynomialBound.ParallelLinks

open FiniteMultiGraph BoundaryDecay SimpleGraph
open FiniteMultiGraph.ExteriorComponents
open Erdos1016.PolynomialBound.Separation

local instance parallelLinksDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### Pairwise independent events -/

section Probability

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]

/-- If no two of the events are positively correlated, then the probability
that none of them occurs is at most `1 / (1 + μ)`, where `μ` is the sum of
their probabilities. -/
theorem none_density_le (s : Finset ι) (P : ι → Ω → Prop)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Finite.density (fun x => P i x ∧ P j x) ≤
        Finite.density (P i) * Finite.density (P j)) :
    Finite.density (fun x => ∀ i ∈ s, ¬ P i x) ≤
      1 / (1 + ∑ i ∈ s, Finite.density (P i)) := by
  classical
  set μ : ℝ := ∑ i ∈ s, Finite.density (P i) with hμ
  have hdens (i : ι) : 0 ≤ Finite.density (P i) := Finite.density_nonneg _
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun i _ => hdens i
  rcases hμ0.eq_or_lt with h0 | hpos
  · rw [← h0, add_zero, div_one]
    exact Finite.density_le_one _
  let Z : Ω → ℝ := fun x => ∑ i ∈ s, indicator (P i) x
  have hmean : average Z = μ := by
    change average (fun x => ∑ i ∈ s, indicator (P i) x) = μ
    rw [average_sum]
    simp only [average_indicator, hμ]
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      average (fun x => indicator (P i) x * indicator (P j) x) ≤
        Finite.density (P i) * Finite.density (P j) +
          (if i = j then Finite.density (P i) else 0) := by
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have h1 : average (fun x => indicator (P i) x * indicator (P i) x) ≤
          Finite.density (P i) := by
        rw [← average_indicator]
        apply average_mono
        intro x
        by_cases hx : P i x <;> simp [indicator, hx]
      nlinarith [hdens i]
    · rw [if_neg hij, add_zero]
      simpa only [indicator_mul, average_indicator] using hpair i hi j hj hij
  have hdiag : (∑ i ∈ s, ∑ j ∈ s, if i = j then Finite.density (P i) else 0) = μ := by
    rw [hμ]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hprod : (∑ i ∈ s, ∑ j ∈ s, Finite.density (P i) * Finite.density (P j)) = μ ^ 2 := by
    rw [hμ, sq, Finset.sum_mul_sum]
  have hsecond : average (fun x => Z x ^ 2) ≤ μ ^ 2 + μ := by
    change average (fun x => (∑ i ∈ s, indicator (P i) x) ^ 2) ≤ μ ^ 2 + μ
    rw [second_average_sum]
    calc
      ∑ i ∈ s, ∑ j ∈ s, average (fun x => indicator (P i) x * indicator (P j) x) ≤
          ∑ i ∈ s, ∑ j ∈ s, (Finite.density (P i) * Finite.density (P j) +
            (if i = j then Finite.density (P i) else 0)) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
      _ = μ ^ 2 + μ := by
        simp only [Finset.sum_add_distrib]
        rw [hprod, hdiag]
  have hmeanpos : 0 < average Z := hmean ▸ hpos
  have hE2pos := second_moment_pos_of_mean_pos Z hmeanpos
  have hzero := zero_density_le_one_sub_mean_sq_div_second Z hmeanpos
  rw [hmean] at hzero
  have hsub : Finite.density (fun x => ∀ i ∈ s, ¬ P i x) ≤
      Finite.density (fun x => Z x = 0) := by
    rw [← average_indicator, ← average_indicator]
    apply average_mono
    intro x
    by_cases hx : ∀ i ∈ s, ¬ P i x
    · have hz : Z x = 0 :=
        Finset.sum_eq_zero fun i hi => by simp [indicator, hx i hi]
      simp only [indicator]
      rw [if_pos hx, if_pos hz]
    · simp only [indicator]
      rw [if_neg hx]
      split_ifs <;> norm_num
  have hquot : μ / (1 + μ) ≤ μ ^ 2 / average (fun x => Z x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hE2pos]
    nlinarith [mul_le_mul_of_nonneg_left hsecond hpos.le]
  have hid : 1 - μ / (1 + μ) = 1 / (1 + μ) := by
    field_simp
  linarith

end Probability

/-! ### Connected sets in the graph of a multigraph -/

/-- A connected induced subgraph gives a connected set. -/
theorem isConnectedSet_of_induce {V : Type*} {H : SimpleGraph V} {C : Set V}
    (h : (H.induce C).Connected) : IsConnectedSet H C := by
  intro a ha b hb
  obtain ⟨p⟩ := h.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨p.map (Embedding.induce C).toHom, ?_⟩
  intro v hv
  rw [Walk.support_map, List.mem_map] at hv
  obtain ⟨w, _, rfl⟩ := hv
  exact w.2

variable (G : FiniteMultiGraph)

/-- A walk that stays inside the region `W` stays inside one component of the
graph induced on `W`. -/
theorem walk_stays (W : Finset G.Vertex) (e : Component G W) {a b : G.Vertex}
    (p : G.toSimpleGraph.Walk a b) (ha : a ∈ vertices G W e)
    (hp : ∀ v ∈ p.support, v ∈ W) : ∀ v ∈ p.support, v ∈ vertices G W e := by
  induction p with
  | nil =>
    intro v hv
    rw [Walk.support_nil, List.mem_singleton] at hv
    exact hv ▸ ha
  | @cons a c b hadj q ih =>
    intro v hv
    rw [Walk.support_cons, List.mem_cons] at hv
    have hcW : c ∈ W := hp c (by
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ q.start_mem_support)
    have hc : c ∈ vertices G W e := adjacent_stays G W e ha hcW hadj
    rcases hv with rfl | hv
    · exact ha
    · exact ih hc (fun w hw => hp w (by
        rw [Walk.support_cons]
        exact List.mem_cons_of_mem _ hw)) v hv

variable (A B : Finset G.Vertex)

/-- Let `c₀` join `A` and `B`. After the deletion of two other components
`c` and `d` of the graph without `A ∪ B`, every remaining vertex can be
reached from every vertex of `A`. -/
theorem avoidReach_of_third_link (hG : G.toSimpleGraph.Connected)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (c₀ c d : Component G (A ∪ B)ᶜ)
    (h₀ : SeedPairCorrelation.BothAttached G A B c₀) (hc : c₀ ≠ c) (hd : c₀ ≠ d)
    {a w : G.Vertex} (ha : a ∈ A)
    (hw : w ∉ vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d) :
    AvoidReach G.toSimpleGraph
      (↑(vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d) : Set G.Vertex) a w := by
  classical
  set X : Set G.Vertex := ↑(vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d) with hX
  -- a vertex of `A ∪ B` is not in `X`
  have houter (v : G.Vertex) (hv : v ∈ A ∪ B) : v ∉ X := by
    intro hvX
    rw [hX, Finset.mem_coe, Finset.mem_union] at hvX
    rcases hvX with h | h
    · exact Finset.mem_compl.mp (vertices_subset G _ c h) hv
    · exact Finset.mem_compl.mp (vertices_subset G _ d h) hv
  -- a vertex of a component other than `c` and `d` is not in `X`
  have hother (e : Component G (A ∪ B)ᶜ) (hec : e ≠ c) (hed : e ≠ d) (v : G.Vertex)
      (hv : v ∈ vertices G (A ∪ B)ᶜ e) : v ∉ X := by
    intro hvX
    rw [hX, Finset.mem_coe, Finset.mem_union] at hvX
    rcases hvX with h | h
    · exact Finset.disjoint_left.mp (vertices_disjoint G _ hec) hv h
    · exact Finset.disjoint_left.mp (vertices_disjoint G _ hed) hv h
  have hAX : Disjoint (↑A : Set G.Vertex) X :=
    Set.disjoint_left.mpr fun v hv => houter v (Finset.mem_union_left _ hv)
  have hBX : Disjoint (↑B : Set G.Vertex) X :=
    Set.disjoint_left.mpr fun v hv => houter v (Finset.mem_union_right _ hv)
  have h₀X : Disjoint (↑(vertices G (A ∪ B)ᶜ c₀) : Set G.Vertex) X :=
    Set.disjoint_left.mpr fun v hv => hother c₀ hc hd v hv
  have hAset := isConnectedSet_of_induce hA
  have hBset := isConnectedSet_of_induce hB
  have h₀set := isConnectedSet_of_induce (vertices_connected G (A ∪ B)ᶜ c₀)
  have reachA (v : G.Vertex) (hv : v ∈ A) : AvoidReach G.toSimpleGraph X a v :=
    hAset.avoidReach hAX (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hv)
  obtain ⟨⟨u, hu, x, hx, hux⟩, ⟨v, hv, y, hy, hvy⟩⟩ := h₀
  have reachx : AvoidReach G.toSimpleGraph X a x :=
    (reachA u hu).step hux (hother c₀ hc hd x hx)
  have reachy : AvoidReach G.toSimpleGraph X a y :=
    reachx.trans (h₀set.avoidReach h₀X (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy))
  have reachv : AvoidReach G.toSimpleGraph X a v :=
    reachy.step hvy.symm (houter v (Finset.mem_union_right _ hv))
  have reachB (b : G.Vertex) (hb : b ∈ B) : AvoidReach G.toSimpleGraph X a b :=
    reachv.trans (hBset.avoidReach hBX (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hb))
  have reachAB (b : G.Vertex) (hb : b ∈ A ∪ B) : AvoidReach G.toSimpleGraph X a b := by
    rcases Finset.mem_union.mp hb with h | h
    · exact reachA b h
    · exact reachB b h
  by_cases hwAB : w ∈ A ∪ B
  · exact reachAB w hwAB
  -- `w` lies in a component `e` other than `c` and `d`
  have hwW : w ∈ (A ∪ B)ᶜ := Finset.mem_compl.mpr hwAB
  let e : Component G (A ∪ B)ᶜ := (graph G (A ∪ B)ᶜ).connectedComponentMk ⟨w, hwW⟩
  have hwe : w ∈ vertices G (A ∪ B)ᶜ e := (mem_vertices G _ e w).mpr ⟨hwW, rfl⟩
  have hec : e ≠ c := fun h => hw (Finset.mem_union_left _ (h ▸ hwe))
  have hed : e ≠ d := fun h => hw (Finset.mem_union_right _ (h ▸ hwe))
  obtain ⟨q⟩ := hG.preconnected w a
  have hwY : w ∉ (↑(A ∪ B) : Set G.Vertex) := fun h => hwAB (Finset.mem_coe.mp h)
  obtain ⟨z, y', hz, hzy, hy'⟩ := exists_first_hit q hwY
    ⟨a, q.end_mem_support, Finset.mem_coe.mpr (Finset.mem_union_left _ ha)⟩
  obtain ⟨p, hp⟩ := hz
  have hpW : ∀ v ∈ p.support, v ∈ (A ∪ B)ᶜ := fun v hv =>
    Finset.mem_compl.mpr fun h => hp v hv (Finset.mem_coe.mpr h)
  have hpe := walk_stays G (A ∪ B)ᶜ e p hwe hpW
  have hwz : AvoidReach G.toSimpleGraph X w z :=
    ⟨p, fun v hv => hother e hec hed v (hpe v hv)⟩
  have hy'AB : y' ∈ A ∪ B := Finset.mem_coe.mp hy'
  have hwy : AvoidReach G.toSimpleGraph X w y' := hwz.step hzy (houter y' hy'AB)
  exact (reachAB y' hy'AB).trans hwy.symm

/-- The graph that remains after the deletion of `c` and `d` is connected. -/
theorem complement_connected (hG : G.toSimpleGraph.Connected)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (c₀ c d : Component G (A ∪ B)ᶜ)
    (h₀ : SeedPairCorrelation.BothAttached G A B c₀) (hc : c₀ ≠ c) (hd : c₀ ≠ d) :
    (G.toSimpleGraph.induce
      (↑((vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d)ᶜ : Finset G.Vertex) :
        Set G.Vertex)).Connected := by
  classical
  obtain ⟨⟨a, ha⟩⟩ := hA.nonempty
  have ha' : a ∈ A := Finset.mem_coe.mp ha
  have haN : a ∉ vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_compl.mp (vertices_subset G _ c h) (Finset.mem_union_left _ ha')
    · exact Finset.mem_compl.mp (vertices_subset G _ d h) (Finset.mem_union_left _ ha')
  apply G.toSimpleGraph.induce_connected_of_patches a
    (Finset.mem_coe.mpr (Finset.mem_compl.mpr haN))
  intro v hv
  have hv' : v ∉ vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d :=
    Finset.mem_compl.mp (Finset.mem_coe.mp hv)
  obtain ⟨p, hp⟩ := avoidReach_of_third_link G A B hG hA hB c₀ c d h₀ hc hd ha' hv'
  refine ⟨{x | x ∈ p.support}, ?_, p.start_mem_support, p.end_mem_support, ?_⟩
  · intro x hx
    exact Finset.mem_coe.mpr (Finset.mem_compl.mpr fun h => hp x hx (Finset.mem_coe.mpr h))
  · exact p.connected_induce_support.preconnected _ _

/-- Two components other than `c₀` have at most one link. -/
theorem links_card_le_one (hG : G.toSimpleGraph.Connected)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (c₀ c d : Component G (A ∪ B)ᶜ)
    (h₀ : SeedPairCorrelation.BothAttached G A B c₀) (hc : c₀ ≠ c) (hd : c₀ ≠ d)
    (hcd : c ≠ d) :
    Nat.card (SeedPairCorrelation.Links G (vertices G (A ∪ B)ᶜ c)
      (vertices G (A ∪ B)ᶜ d)) ≤ 1 := by
  classical
  have hdisj := vertices_disjoint G (A ∪ B)ᶜ hcd
  have h := SeedPairCorrelation.links_card_le_direct_add_exterior G _ _ hdisj
  have hdirect : G.directLabels (vertices G (A ∪ B)ᶜ c) (vertices G (A ∪ B)ᶜ d) = ∅ := by
    apply Finset.eq_empty_of_forall_not_mem
    intro e he
    rcases (G.mem_directLabels _ _ e).mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hne : G.src e ≠ G.dst e := fun heq =>
        Finset.disjoint_left.mp hdisj hs (heq ▸ ht)
      have hadj : G.toSimpleGraph.Adj (G.src e) (G.dst e) := ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
      exact Finset.disjoint_left.mp hdisj
        (adjacent_stays G _ c hs (vertices_subset G _ d ht) hadj) ht
    · have hne : G.dst e ≠ G.src e := fun heq =>
        Finset.disjoint_left.mp hdisj ht (heq ▸ hs)
      have hadj : G.toSimpleGraph.Adj (G.dst e) (G.src e) := ⟨hne, e, Or.inr ⟨rfl, rfl⟩⟩
      exact Finset.disjoint_left.mp hdisj
        (adjacent_stays G _ c ht (vertices_subset G _ d hs) hadj) hs
  have hconn := complement_connected G A B hG hA hB c₀ c d h₀ hc hd
  have hext : (SeedPairCorrelation.exteriorLinks G (vertices G (A ∪ B)ᶜ c)
      (vertices G (A ∪ B)ᶜ d)).card ≤ 1 := by
    haveI : Subsingleton (Component G
        (vertices G (A ∪ B)ᶜ c ∪ vertices G (A ∪ B)ᶜ d)ᶜ) :=
      hconn.preconnected.subsingleton_connectedComponent
    exact Finset.card_le_one_of_subsingleton _
  rw [hdirect, Finset.card_empty, zero_add] at h
  exact h.trans hext

/-! ### Independence and the forest bound -/

/-- Two disjoint connected regions with at most one link have region cycle
events that are not positively correlated. -/
theorem regionCycleEvent_pair_le_of_links (U V : Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hUV : Disjoint U V)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (hlinks : Nat.card (SeedPairCorrelation.Links G U V) ≤ 1) :
    Finite.density (fun x => G.RegionCycleEvent U x ∧ G.RegionCycleEvent V x) ≤
      Finite.density (G.RegionCycleEvent U) * Finite.density (G.RegionCycleEvent V) := by
  have hpair := SeedPairCorrelation.zeroCut_pair_exact G U V hG hUV hU hV
  have hd : dyadic ((Nat.card (SeedPairCorrelation.Links G U V) : ℤ) - 1) ≤ 1 := by
    unfold dyadic
    apply zpow_le_one_of_nonpos₀ (by norm_num)
    have hcast : (Nat.card (SeedPairCorrelation.Links G U V) : ℤ) ≤ 1 := by
      exact_mod_cast hlinks
    omega
  have h := G.regionCycleEvent_pair_le U V hUV 1 (by
    rw [hpair, one_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (Finite.density_nonneg _) hd) (Finite.density_nonneg _))
  simpa only [one_mul] using h

/-- A family of disjoint connected cyclic regions with at most `t` cut edges,
any two of which have at most one link, bounds the forest probability on
every edge set that contains their internal edges. -/
theorem independent_regions_forest_le {ι : Type*} (U : ι → Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected) (s : Finset ι)
    (hconn : ∀ i ∈ s, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (hlinks : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Nat.card (SeedPairCorrelation.Links G (U i) (U j)) ≤ 1)
    (t : ℕ) (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ t)
    (hcyclic : ∀ i ∈ s, ∃ z : G.internalCycleSpace (U i), z ≠ 0)
    (E : Finset G.Edge) (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      1 / (1 + (s.card : ℝ) / 2 ^ (t + 1)) := by
  classical
  have hnone := none_density_le s (fun i => G.RegionCycleEvent (U i))
    (fun i hi j hj hij => regionCycleEvent_pair_le_of_links G (U i) (U j) hG
      (hdisj i hi j hj hij) (hconn i hi) (hconn j hj) (hlinks i hi j hj hij))
  have hforest :
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      Finite.density (fun x : G.CycleSpace => ∀ i ∈ s, ¬ G.RegionCycleEvent (U i) x) := by
    rw [← average_indicator, ← average_indicator]
    apply average_mono
    intro x
    by_cases hx : G.IsForestWord (G.restrictEdges E x.1)
    · have hno : ∀ i ∈ s, ¬ G.RegionCycleEvent (U i) x := by
        intro i hi hcycle
        apply G.regionCycleEvent_not_forest (U i) x hcycle
        apply hx.mono
        intro e he
        by_cases hmem : e ∈ G.internalEdges (U i)
        · have hlarge := hE i hi hmem
          simpa only [restrictEdges, hmem, hlarge, ↓reduceIte] using he
        · simp [restrictEdges, hmem] at he
      simp only [indicator]
      rw [if_pos hx, if_pos hno]
    · simp only [indicator]
      rw [if_neg hx]
      split_ifs <;> norm_num
  have hmass : (s.card : ℝ) / 2 ^ (t + 1) ≤
      ∑ i ∈ s, Finite.density (G.RegionCycleEvent (U i)) := by
    have h := Finset.sum_le_sum fun i hi =>
      G.regionCycleEvent_probability_ge (U i) (hcyclic i hi) t (hcut i hi)
    simpa [div_eq_mul_inv] using h
  have hpos : (0 : ℝ) < 1 + (s.card : ℝ) / 2 ^ (t + 1) := by positivity
  calc
    _ ≤ _ := hforest
    _ ≤ 1 / (1 + ∑ i ∈ s, Finite.density (G.RegionCycleEvent (U i))) := hnone
    _ ≤ 1 / (1 + (s.card : ℝ) / 2 ^ (t + 1)) :=
      one_div_le_one_div_of_le hpos (by linarith)

/-- **Small cyclic links, without a forest excess.** If the forest probability
outside `P` exceeds one half, then at most `2 ^ (t + 1)` of the components
that join `A` and `B` are cyclic, avoid `P`, and have at most `t` cut edges. -/
theorem smallCyclicPart_card_le (hG : G.toSimpleGraph.Connected)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (P : Finset G.Vertex) (t : ℕ) (S : Finset (Component G (A ∪ B)ᶜ))
    (hS : ∀ c ∈ S, SeedPairCorrelation.BothAttached G A B c)
    (hforest : (1 / 2 : ℝ) < G.regionForestProbability Pᶜ) :
    (smallCyclicPart G (A ∪ B)ᶜ P t S).card ≤ 2 ^ (t + 1) := by
  classical
  by_cases hne : (smallCyclicPart G (A ∪ B)ᶜ P t S).Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hc₀S : c₀ ∈ S := (Finset.mem_filter.mp hc₀).1
    have hmem (c : Component G (A ∪ B)ᶜ)
        (hc : c ∈ (smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀) :=
      Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    have hbound := independent_regions_forest_le G (vertices G (A ∪ B)ᶜ) hG
      ((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀)
      (fun c _ => vertices_connected G _ c)
      (fun c _ d _ hcd => vertices_disjoint G _ hcd)
      (fun c hc d hd hcd => links_card_le_one G A B hG hA hB c₀ c d (hS c₀ hc₀S)
        (Finset.ne_of_mem_erase hc).symm (Finset.ne_of_mem_erase hd).symm hcd)
      t (fun c hc => (hmem c hc).2.2.1)
      (fun c hc => G.internalCycleSpace_nontrivial_of_not_forest _ (hmem c hc).2.2.2)
      (G.internalEdges Pᶜ) (by
        intro c hc e he
        have hP := (hmem c hc).2.1
        have hends := (Finset.mem_filter.mp he).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
        · exact fun hs => hP ⟨G.src e, hs, hends.1⟩
        · exact fun ht => hP ⟨G.dst e, ht, hends.2⟩)
    rw [G.regionForestProbability_eq_density] at hforest
    have hlt : (((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card : ℝ) / 2 ^ (t + 1) < 1 := by
      by_contra hge
      push_neg at hge
      have hhalf : 1 / (1 + (((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card : ℝ) /
          2 ^ (t + 1)) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hlt' : ((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card < 2 ^ (t + 1) := by
      have h2 : (0 : ℝ) < 2 ^ (t + 1) := by positivity
      have h := (div_lt_one h2).mp hlt
      exact_mod_cast h
    have hcard := Finset.card_erase_add_one hc₀
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Erdos1016.PolynomialBound.ParallelLinks

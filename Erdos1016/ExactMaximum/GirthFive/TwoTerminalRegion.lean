import Erdos1016.ExactMaximum.GirthFive.RegionWords

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Two terminals at girth five, for the words of a multigraph

`N` is a multigraph without cycles of length less than five and with all degrees at most three.
Let `B` be a connected set of vertices and `x ≠ y` two vertices of `B`, and suppose that every
word on the internal edges of `B` with boundary `x + y` is a forest. Then
`|B| ≤ 400 (|D| + 2)`, where `D` contains every vertex of `B` that has degree less than three or
a neighbour outside `B` (`two_terminal_region`).

The proof takes a shortest walk `A` from `x` to `y` inside `B`. The word of `A` has boundary
`x + y`. So no nonzero even word lives on the vertices of `B` outside `A`, and the graph on these
vertices is a forest with at most as many edges as vertices. The count is
`two_terminal_card_le`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph FiniteMultiGraph Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.ExactMaximumSupport.LargeGirth Erdos1016.PolynomialBound.Separation

local instance twoTerminalRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (N : FiniteMultiGraph)

/-- The underlying simple graph inside a set of vertices. -/
def insideGraph (B : Finset N.Vertex) : SimpleGraph N.Vertex where
  Adj u v := N.toSimpleGraph.Adj u v ∧ u ∈ B ∧ v ∈ B
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun u h => N.toSimpleGraph.loopless u h.1

theorem insideGraph_le (B : Finset N.Vertex) : insideGraph N B ≤ N.toSimpleGraph :=
  fun _ _ h => h.1

/-- A walk whose vertices lie in `B` is a walk of the graph inside `B`. -/
theorem exists_inside_walk (B : Finset N.Vertex) {u v : N.Vertex}
    (p : N.toSimpleGraph.Walk u v) (hp : ∀ z ∈ p.support, z ∈ B) :
    ∃ q : (insideGraph N B).Walk u v, q.length = p.length := by
  have hpe : ∀ e ∈ p.edges, e ∈ (insideGraph N B).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨p.adj_of_mem_edges he, hp a (p.fst_mem_support_of_mem_edges he),
        hp b (p.snd_mem_support_of_mem_edges he)⟩
  exact ⟨p.transfer _ hpe, p.length_transfer hpe⟩

/-- The word of the internal edges of a set. -/
def regionWord (F : Finset N.Vertex) : N.EdgeWord :=
  fun e => if e ∈ N.internalEdges F then 1 else 0

/-- If a region has no nonzero even word, the word of its internal edges is a forest. -/
theorem regionWord_isForest (F : Finset N.Vertex) (hF : ∀ z : N.internalCycleSpace F, z = 0) :
    N.IsForestWord (regionWord N F) := by
  rw [isForestWord_iff_no_even_support]
  intro seed hsub
  have hmem : seed ∈ N.internalCycleSpace F := by
    intro e he
    by_contra hne
    have := hsub e hne
    simp only [regionWord, if_neg he, ne_eq, not_true_eq_false] at this
  have h0 := hF ⟨seed, hmem⟩
  have h1 : seed = 0 := congrArg Subtype.val h0
  rw [h1]
  rfl

/-- **Two terminals at girth five.** -/
theorem two_terminal_region (h5 : ¬ N.HasCycleShorterThan 5) (hmax : ∀ v, N.degree v ≤ 3)
    (B : Finset N.Vertex) (hB : IsConnectedSet N.toSimpleGraph (↑B : Set N.Vertex))
    {x y : N.Vertex} (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hrigid : ∀ j : N.EdgeWord, (∀ e, j e ≠ 0 → e ∈ N.internalEdges B) →
      N.boundary j = N.vertexUnit x + N.vertexUnit y → N.IsForestWord j)
    (D : Finset N.Vertex)
    (hD : ∀ v ∈ B, v ∉ D → N.degree v = 3 ∧ ∀ u, N.toSimpleGraph.Adj v u → u ∈ B) :
    B.card ≤ 400 * (D.card + 2) := by
  have h3 := no_short_three_of_le N 5 (by norm_num) h5
  have hg := girthGreater_toSimpleGraph N h5
  have hdeg : ∀ v, (nbrs N.toSimpleGraph v).card ≤ 3 := by
    intro v
    rw [card_nbrs_eq_degree N h3]
    exact hmax v
  -- a shortest walk inside `B`
  obtain ⟨p, hp⟩ := hB x (by exact_mod_cast hx) y (by exact_mod_cast hy)
  obtain ⟨q, _⟩ := exists_inside_walk N B p (fun z hz => by exact_mod_cast hp z hz)
  obtain ⟨A, hA⟩ := (Walk.reachable q).exists_walk_length_eq_dist
  have hshort : ∀ q' : (insideGraph N B).Walk x y, A.length ≤ q'.length := by
    intro q'
    rw [hA]
    exact (insideGraph N B).dist_le q'
  -- the vertices of `A` are in `B`
  have hAB : ∀ z ∈ A.support, z ∈ B := by
    have hend : ∀ a b, (insideGraph N B).Adj a b → b ∈ B := fun _ _ h => h.2.2
    exact walk_support_of_adj (H := insideGraph N B) (fun v => v ∈ B) hend A hx
  let F : Finset N.Vertex := B.filter (fun v => v ∉ A.support)
  -- the word of `A`
  let jA : N.EdgeWord := N.walkWord (A.mapLe (insideGraph_le N B))
  have hjA : N.boundary jA = N.vertexUnit x + N.vertexUnit y := N.boundary_walkWord _
  have hjAsupp : ∀ e, jA e ≠ 0 → N.src e ∈ A.support ∧ N.dst e ∈ A.support := by
    intro e he
    have := walkWord_support N (A.mapLe (insideGraph_le N B)) e he
    simpa using this
  -- no nonzero even word outside `A`
  have hFzero : ∀ z : N.internalCycleSpace F, z = 0 := by
    intro z
    have hzF : ∀ e, z.1.1 e ≠ 0 → e ∈ N.internalEdges F := by
      intro e he
      by_contra hne
      exact he (z.2 e hne)
    have hdisj : ∀ e, z.1.1 e ≠ 0 → jA e = 0 := by
      intro e he
      by_contra hj
      have h1 := (hjAsupp e hj).1
      have h2 := (Finset.mem_filter.mp (hzF e he)).2.1
      exact (Finset.mem_filter.mp h2).2 h1
    have hf := hrigid (jA + z.1.1) ?_ ?_
    · have hz := (isForestWord_iff_no_even_support N _).mp hf z.1 ?_
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
      · intro e he
        show jA e + z.1.1 e ≠ 0
        rw [hdisj e he, zero_add]
        exact he
    · intro e he
      by_cases h1 : jA e ≠ 0
      · obtain ⟨hs, hd⟩ := hjAsupp e h1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB _ hs, hAB _ hd⟩
      · push_neg at h1
        have h2 : z.1.1 e ≠ 0 := by
          intro h0
          apply he
          show jA e + z.1.1 e = 0
          rw [h1, h0, add_zero]
        have h3' := Finset.mem_filter.mp (hzF e h2)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp h3'.2.1).1, (Finset.mem_filter.mp h3'.2.2).1⟩
    · rw [map_add, hjA]
      have hz0 : N.boundary z.1.1 = 0 := LinearMap.mem_ker.mp z.1.2
      rw [hz0, add_zero]
  have hforestWord := regionWord_isForest N F hFzero
  refine two_terminal_card_le N.toSimpleGraph hg hdeg B hxy (insideGraph N B)
    (fun _ _ => Iff.rfl) A hshort ?_ ?_ D ?_
  · -- every cycle inside `B` meets `A`
    intro u c hc
    by_contra hcon
    push_neg at hcon
    have hce : ∀ e ∈ c.edges, e ∈ (N.selectedGraph (regionWord N F)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet]
        have hadj := c.adj_of_mem_edges he
        have ha : a ∈ F := Finset.mem_filter.mpr
          ⟨hadj.2.1, hcon a (c.fst_mem_support_of_mem_edges he)⟩
        have hb : b ∈ F := Finset.mem_filter.mpr
          ⟨hadj.2.2, hcon b (c.snd_mem_support_of_mem_edges he)⟩
        refine ⟨hadj.1.1, N.edgeForAdj hadj.1, ?_, ?_⟩
        · have hmem : N.edgeForAdj hadj.1 ∈ N.internalEdges F := by
            rcases N.edgeForAdj_endpoints hadj.1 with hh | hh
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hh.1]; exact ha,
                by rw [hh.2]; exact hb⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hh.1]; exact hb,
                by rw [hh.2]; exact ha⟩
          simp only [regionWord, if_pos hmem, ne_eq, one_ne_zero, not_false_eq_true]
        · exact N.edgeForAdj_endpoints hadj.1
    exact hforestWord.2.2 (c.transfer _ hce) (hc.transfer hce)
  · -- the edges outside `A`
    have h1 := sum_card_nbrs_le N F
    have h2 := card_internalEdges_le N F hFzero
    have hsum : (∑ v ∈ F,
          ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ B ∧ u ∉ A.support)).card) =
        ∑ v ∈ F, ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ F)).card := by
      apply Finset.sum_congr rfl
      intro v _
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro u _
      simp only [F, Finset.mem_filter]
    have hfinal : (∑ v ∈ F,
        ((nbrs N.toSimpleGraph v).filter (fun u => u ∈ B ∧ u ∉ A.support)).card) ≤
        2 * F.card := by omega
    convert hfinal using 3
    · ext u
      simp only [Finset.mem_filter]
    · ext u
      simp only [F, Finset.mem_filter]
  · intro v hv hvD
    obtain ⟨h3', hin⟩ := hD v hv hvD
    exact ⟨by rw [card_nbrs_eq_degree N h3, h3'], hin⟩

end Erdos1016.ExactMaximum.GirthFive

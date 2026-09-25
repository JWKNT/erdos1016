import Erdos1016.Nonbacktracking.Walks.WeightedPrefixes
import Erdos1016.Cycles.Counting.FixedLengthVertexMass
import Erdos1016.Probability.Moments.CompatibleTupleMoments
import Erdos1016.Expansion.GraphBalls

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace Erdos1016.Proof.WeightedCycleLoad

open scoped BigOperators
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WeightedWalkPrefix
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.FixedLengthVertexMass
open Erdos1016.Proof.RootedCyclePrefixes
open Erdos1016.Proof.CycleRootChoice

variable (G : PhysicalGraph)

/-- A selected family's cycles at a specified length and vertex. -/
def selectedAtVertex (F : Finset G.CycleWord) (ell : ℕ) (v : G.Vertex) :
    Finset (CycleWordsAtLength G ell) := by
  classical
  exact Finset.univ.filter fun C => C.1 ∈ F ∧ v ∈ BoundaryDecay.Cycle.vertices C.1

theorem selectedAtVertex_subset (F : Finset G.CycleWord) (ell : ℕ) (v : G.Vertex) :
    selectedAtVertex G F ell v ⊆ cyclesAtVertex G ell v := by
  classical
  intro C hC
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hC).2.2⟩

/-- The product around a physical cycle is bounded by the internal weight of
either rooted orientation. The omitted root weight is at most one. -/
theorem cycle_product_le_encoded_run (w : G.Vertex → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hwone : ∀ v, w v ≤ 1)
    (ell : ℕ) (v : G.Vertex)
    (C : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v})
    (orientation : Bool) :
    (∏ u ∈ BoundaryDecay.Cycle.vertices C.1.1, w u) ≤
      runWeight G w (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2 := by
  classical
  let c := chosenRootedSimpleCycle C.1
  let x := selectRootAtVertex G ell v C
  let q := rootedOrientedWalk c.1.2 x orientation
  have hq : q.IsCycle := rootedOrientedWalk_cycle c.1.2 c.2.1 x orientation
  have hword : walkWord G q = C.1.1.1 := by
    exact (rootedOrientedWalk_word_eq c.1.2 x orientation).trans
      (congrArg Subtype.val (chosenRootedSimpleCycle_word C.1))
  have hvertices : BoundaryDecay.Cycle.vertices C.1.1 = q.support.tail.toFinset := by
    ext u
    change u ∈ G.usedVertices C.1.1.1 ↔ _
    rw [← hword, used_walkWord_iff G q hq]
    simp only [List.mem_toFinset]
    exact ⟨supportTail_of_cycle G q hq u, List.mem_of_mem_tail⟩
  have hdarts : runDarts G (ell - 1)
      (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2 = walkDarts G q := by
    exact rootedCycleEndpointPrefix_darts G c x
      (selectRootAtVertex_spec G ell v C) orientation
  have hheads := congrArg (List.map (head G)) hdarts
  rw [walkDarts_map_head] at hheads
  rw [hvertices, List.prod_toFinset w hq.support_nodup, runWeight_eq_prod]
  change (q.support.tail.map w).prod ≤
    (((runDarts G (ell - 1)
      (encodeCyclePrefixAtVertex G ell v C orientation).1.2.2).dropLast.map
        (w ∘ head G)).prod)
  rw [← List.map_map, List.map_dropLast, hheads]
  exact prod_map_le_dropLast G w hw hwone _

/-- The two orientations through a fixed vertex give the factor one half in
the conditional cycle-load estimate. The suffix estimate is required only
on the selected physical family. -/
theorem cycle_vertex_weight_le_suffix
    (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) (hwone : ∀ v, w v ≤ 1)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (D ell s : ℕ) (v : G.Vertex)
    (hmax : G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsell : s < ell) (hshort : 2 * s ≤ D)
    (F : Finset (CycleWordsAtLength G ell)) (hF : F ⊆ cyclesAtVertex G ell v)
    (mass : CycleWordsAtLength G ell → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hmass : ∀ C ∈ F, mass C ≤ ∏ u ∈ BoundaryDecay.Cycle.vertices C.1, w u)
    (hsuffix : ∀ C : {C : CycleWordsAtLength G ell // C ∈ F}, ∀ orientation : Bool,
      runWeight G w (splitRun G (show ell - s - 1 ≤ ell - 1 by omega)
        (encodeCyclePrefixAtVertex G ell v ⟨C.1, hF C.2⟩ orientation).1.2.2).2.2 ≤ ε) :
    (∑ C ∈ F, mass C) ≤ (3 / 2 : ℝ) * ε := by
  classical
  let encode := fun z : {C : CycleWordsAtLength G ell // C ∈ F} × Bool =>
    encodeCyclePrefixAtVertex G ell v ⟨z.1.1, hF z.1.2⟩ z.2
  have hinj : Function.Injective encode := by
    intro z t h
    have heq :
        ((⟨z.1.1, hF z.1.2⟩ : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v}), z.2) =
        ((⟨t.1.1, hF t.1.2⟩ : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v}), t.2) :=
      encodeCyclePrefixAtVertex_injective G ell v h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z => z.1.1) heq)
    · have ho := congrArg (fun p => p.2) heq
      exact ho
  have hsum := encoded_endpoint_weight_sum_le G w hw hrow D ell s v v hg hs hsell hshort
    encode hinj (fun z => mass z.1.1) ε hε
    (fun z => (hmass z.1.1 z.1.2).trans
      (cycle_product_le_encoded_run G w hw hwone ell v ⟨z.1.1, hF z.1.2⟩ z.2))
    (fun z => hsuffix z.1 z.2)
  have hleft : (∑ z : {C : CycleWordsAtLength G ell // C ∈ F} × Bool, mass z.1.1) =
      2 * ∑ C ∈ F, mass C := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    exact (Finset.sum_subtype F (by intro C; rfl) mass).symm
  rw [hleft] at hsum
  have hdeg : (G.degree v : ℝ) ≤ 3 := by exact_mod_cast hmax
  have hbound := mul_le_mul_of_nonneg_left hdeg hε
  nlinarith

/-- Reindex the actual selected physical family by length, then sum the
weighted suffix bound. This is the conditional per-vertex load in Lemma 5.3. -/
theorem vertexLoad_le_suffix
    (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) (hwone : ∀ v, w v ≤ 1)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (hmax : ∀ v, G.degree v ≤ 3)
    (D s L : ℕ) (F : Finset G.CycleWord) (mass : G.CycleWord → ℝ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D)
    (hlen : ∀ C ∈ F, s < BoundaryDecay.Cycle.length C ∧ BoundaryDecay.Cycle.length C ≤ L)
    (hmassnonneg : ∀ C ∈ F, 0 ≤ mass C)
    (hmass : ∀ C ∈ F, mass C ≤ ∏ u ∈ BoundaryDecay.Cycle.vertices C, w u)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsuffix : ∀ ell ∈ Finset.Ioc s L, ∀ v,
      ∀ C : {C : CycleWordsAtLength G ell // C ∈ selectedAtVertex G F ell v},
      ∀ orientation : Bool,
      runWeight G w (splitRun G (show ell - s - 1 ≤ ell - 1 by omega)
        (encodeCyclePrefixAtVertex G ell v
          ⟨C.1, selectedAtVertex_subset G F ell v C.2⟩ orientation).1.2.2).2.2 ≤ ε)
    (v : G.Vertex) :
    BoundaryDecay.vertexLoad F BoundaryDecay.Cycle.vertices mass v ≤
      (3 / 2 : ℝ) * (L : ℝ) * ε := by
  classical
  let S := F.filter fun C => v ∈ BoundaryDecay.Cycle.vertices C
  let T := Finset.sigma (Finset.Ioc s L) (fun ell => selectedAtVertex G F ell v)
  let f : G.CycleWord → Σ ell, CycleWordsAtLength G ell :=
    fun C => ⟨BoundaryDecay.Cycle.length C, ⟨C, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro C E h
    exact congrArg (fun z => z.2.1) h
  have himage : S.image f ⊆ T := by
    intro z hz
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hz
    have hCF : C ∈ F := (Finset.mem_filter.mp hC).1
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr (hlen C hCF),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCF, (Finset.mem_filter.mp hC).2⟩⟩
  have hload : BoundaryDecay.vertexLoad F BoundaryDecay.Cycle.vertices mass v =
      ∑ C ∈ S, mass C := by simp [BoundaryDecay.vertexLoad, S, Finset.sum_filter]
  have hfixed (ell : ℕ) (hell : ell ∈ Finset.Ioc s L) :
      (∑ C ∈ selectedAtVertex G F ell v, mass C.1) ≤ (3 / 2 : ℝ) * ε := by
    apply cycle_vertex_weight_le_suffix G w hw hwone hrow D ell s v (hmax v)
      hg hs (Finset.mem_Ioc.mp hell).1 hshort
      (selectedAtVertex G F ell v) (selectedAtVertex_subset G F ell v) (fun C => mass C.1) ε hε
    · intro C hC
      exact hmass C.1 (Finset.mem_filter.mp hC).2.1
    · exact hsuffix ell hell v
  calc
    _ = ∑ C ∈ S, mass C := hload
    _ = ∑ z ∈ S.image f, mass z.2.1 := by rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ ∑ z ∈ T, mass z.2.1 := Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun z hz _ => hmassnonneg z.2.1 (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).2.1)
    _ = ∑ ell ∈ Finset.Ioc s L, ∑ C ∈ selectedAtVertex G F ell v, mass C.1 := by
      rw [Finset.sum_sigma']
    _ ≤ ∑ _ell ∈ Finset.Ioc s L, (3 / 2 : ℝ) * ε :=
      Finset.sum_le_sum fun ell hell => hfixed ell hell
    _ ≤ (3 / 2 : ℝ) * (L : ℝ) * ε := by
      have hcard : ((Finset.Ioc s L).card : ℝ) ≤ L := by
        simp only [Nat.card_Ioc]
        exact_mod_cast Nat.sub_le L s
      have h := mul_le_mul_of_nonneg_right hcard (show 0 ≤ (3 / 2 : ℝ) * ε by positivity)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- A marked-position bound for each actual short suffix gives the conditional
vertex estimate. The two additional positions allow the exceptional pruned
tree and the endpoint omitted from the `s - 1` spacing segment. -/
theorem vertexLoad_le_marked_suffix
    (w : G.Vertex → ℝ) (marked : G.Vertex → Prop) [DecidablePred marked]
    (hw : ∀ v, 0 ≤ w v) (hwone : ∀ v, w v ≤ 1)
    (hhalf : ∀ v, ¬ marked v → w v ≤ 1 / 2)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (hmax : ∀ v, G.degree v ≤ 3)
    (D s L b : ℕ) (F : Finset G.CycleWord) (mass : G.CycleWord → ℝ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D)
    (hlen : ∀ C ∈ F, s < BoundaryDecay.Cycle.length C ∧ BoundaryDecay.Cycle.length C ≤ L)
    (hmassnonneg : ∀ C ∈ F, 0 ≤ mass C)
    (hmass : ∀ C ∈ F, mass C ≤ ∏ u ∈ BoundaryDecay.Cycle.vertices C, w u)
    (hcount : ∀ ell ∈ Finset.Ioc s L, ∀ v,
      ∀ C : {C : CycleWordsAtLength G ell // C ∈ selectedAtVertex G F ell v},
      ∀ orientation : Bool,
      (((runDarts G ((ell - 1) - (ell - s - 1))
        (splitRun G (show ell - s - 1 ≤ ell - 1 by omega)
          (encodeCyclePrefixAtVertex G ell v
            ⟨C.1, selectedAtVertex_subset G F ell v C.2⟩ orientation).1.2.2).2.2).dropLast.map
          (head G)).countP (fun v => decide (marked v))) ≤ 2 + b)
    (v : G.Vertex) :
    BoundaryDecay.vertexLoad F BoundaryDecay.Cycle.vertices mass v ≤
      6 * L * ((2 : ℝ) ^ b / 2 ^ s) := by
  have h := vertexLoad_le_suffix G w hw hwone hrow hmax D s L F mass hg hs hshort
    hlen hmassnonneg hmass ((2 : ℝ) ^ (2 + b) / 2 ^ s) (by positivity) (by
      intro ell hell u C orientation
      have hsell : s < ell := (Finset.mem_Ioc.mp hell).1
      have hlenSuffix : (ell - 1) - (ell - s - 1) = s := by omega
      have hbound := runWeight_le_marked_budget G w marked hw (fun u _ => hwone u)
        hhalf (splitRun G (show ell - s - 1 ≤ ell - 1 by omega)
          (encodeCyclePrefixAtVertex G ell u
            ⟨C.1, selectedAtVertex_subset G F ell u C.2⟩ orientation).1.2.2).2.2
        (2 + b) (hcount ell hell u C orientation)
      simpa only [hlenSuffix] using hbound) v
  convert h using 1 <;> simp only [pow_add, pow_two] <;> ring

end Erdos1016.Proof.WeightedCycleLoad

import Erdos1016.Nonbacktracking.Girth.ThreeContactCounting
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false

namespace Erdos1016.Proof.BreadthFirstLayers

open Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.Proof.ThreeContactCounting

/-- The kth BFS sphere, represented as a finite set. -/
noncomputable def bfsLayer {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (root : V) (k : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => J.dist root v = k

/-- The real-valued size of one BFS sphere. -/
noncomputable def bfsLayerLevel {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (root : V) (k : ℕ) : ℝ :=
  (bfsLayer J root k).card

/-- Boundary tokens in a layer are the cubic degree deficits of its
vertices. In an induced region of a cubic graph these are exactly the
incidences leaving the target set. -/
noncomputable def bfsLayerTokens {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (root : V) (k : ℕ) : ℝ := by
  exact ∑ v ∈ bfsLayer J root k, ((3 : ℝ) - (J.degree v : ℝ))

theorem bfsLayerLevel_zero {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (hconn : J.Connected) (root : V) :
    bfsLayerLevel J root 0 = 1 := by
  classical
  have hlayer : bfsLayer J root 0 = {root} := by
    ext v
    simp [bfsLayer, hconn.dist_eq_zero_iff, eq_comm]
  simp [bfsLayerLevel, hlayer]

theorem bfsLayerLevel_one_eq_three_sub_tokens
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (root : V) :
    bfsLayerLevel J root 1 = 3 - bfsLayerTokens J root 0 := by
  have hzero : bfsLayer J root 0 = {root} := by
    ext v
    simp [bfsLayer, hconn.dist_eq_zero_iff, eq_comm]
  have hone : bfsLayer J root 1 = J.neighborFinset root := by
    ext v
    simp [bfsLayer, SimpleGraph.dist_eq_one_iff_adj]
  have htoken : bfsLayerTokens J root 0 = 3 - (J.degree root : ℝ) := by
    simp [bfsLayerTokens, hzero]
  rw [bfsLayerLevel, hone, J.card_neighborFinset_eq_degree, htoken]
  ring

theorem bfsLayerTokens_nonneg
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V)
    [DecidableRel J.Adj] (root : V) (hmax : ∀ v, J.degree v ≤ 3) (k : ℕ) :
    0 ≤ bfsLayerTokens J root k := by
  unfold bfsLayerTokens
  apply Finset.sum_nonneg
  intro v hv
  have hdegree : (J.degree v : ℝ) ≤ 3 := by exact_mod_cast hmax v
  exact sub_nonneg.mpr hdegree

private theorem take_length_eq_of_le
    {V : Type*} {J : SimpleGraph V} {u v : V} (p : J.Walk u v) :
    ∀ i, i ≤ p.length → (p.take i).length = i := by
  induction p with
  | nil =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      rfl
  | @cons u v w huv p ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.take, SimpleGraph.Walk.length_cons]
          exact congrArg Nat.succ (ih i (by omega))

/-- Every vertex in the next breadth-first sphere has exactly one adjacent
predecessor in the previous sphere. Only connectedness and girth are needed;
degree bounds enter later when counting the available forward incidences. -/
theorem existsUnique_preceding_layer_neighbor
    {V : Type*} [DecidableEq V] (J : SimpleGraph V)
    (hconn : J.Connected) (D k : ℕ)
    (hg : GirthGreater J D) (h2 : 2 * (k + 1) ≤ D)
    (root v : V) (hv : J.dist root v = k + 1) :
    ∃! w, J.Adj w v ∧ J.dist root w = k := by
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist root v
  have hlen : q.length = k + 1 := hq.trans hv
  let w := q.getVert k
  have hadj : J.Adj w v := by
    have hend : q.getVert (k + 1) = v := by
      rw [← hlen]
      exact q.getVert_length
    rw [← hend]
    exact q.adj_getVert_succ (by omega)
  have hupper : J.dist root w ≤ k := by
    calc
      J.dist root w ≤ (q.take k).length := J.dist_le (q.take k)
      _ = k := take_length_eq_of_le q k (by omega)
  have hdistwv : J.dist w v = 1 := by simp [hadj]
  have hlower : k + 1 ≤ J.dist root w + 1 := by
    calc
      k + 1 = J.dist root v := hv.symm
      _ ≤ J.dist root w + J.dist w v := hconn.dist_triangle
      _ = J.dist root w + 1 := by rw [hdistwv]
  have hdist : J.dist root w = k := by omega
  refine ⟨w, ⟨hadj, hdist⟩, ?_⟩
  intro w' hw'
  have huniq := preceding_sphere_neighbor_unique_of_girth J hconn D (k + 1) hg h2
    root v (by rw [hv]) w w' hadj hw'.1
      (by rw [hdist, hv]) (by rw [hw'.2, hv])
  exact huniq.symm

/-- Under the girth bound used for the layer recurrence, every neighbor of a
vertex in sphere `k` lies in one of the two adjacent spheres.  The same-sphere
case is excluded by `no_same_sphere_edge_of_girth`. -/
theorem bfsLayer_neighborFinset_eq_prev_union_next
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (D r k : ℕ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (hk : 1 ≤ k) (hkr : k < r) (root v : V)
    (hv : J.dist root v = k) :
    J.neighborFinset v =
      (J.neighborFinset v).filter (fun w => J.dist root w = k - 1) ∪
      (J.neighborFinset v).filter (fun w => J.dist root w = k + 1) := by
  ext w
  constructor
  · intro hw
    have hadj : J.Adj v w := (SimpleGraph.mem_neighborFinset J v w).1 hw
    have hnear := adjacent_distances_within_one J hconn root v w hadj
    have hnot : J.dist root w ≠ k := by
      intro heq
      exact no_same_sphere_edge_of_girth J hconn D r hg hD root v w hadj
        (hv.trans heq.symm) (by rw [hv]; exact hkr)
    rcases hnear with ⟨hle, hge⟩
    have hlow : k - 1 ≤ J.dist root w := by omega
    have hhigh : J.dist root w ≤ k + 1 := by omega
    rcases eq_or_ne (J.dist root w) (k - 1) with heq | hneq
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, heq⟩)
    · have heq' : J.dist root w = k + 1 := by omega
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, heq'⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_filter.mp hw).1

/-- The sum of ambient degrees over sphere `k` is its one-parent
contribution plus the number of vertices in sphere `k+1`. This is the
incidence-counting identity behind the cubic layer recurrence. -/
theorem bfsLayer_degree_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (D r k : ℕ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (hk : 1 ≤ k) (hkr : k < r) (root : V) :
    (∑ v ∈ bfsLayer J root k, J.degree v) =
      (bfsLayer J root k).card + (bfsLayer J root (k + 1)).card := by
  let C := bfsLayer J root k
  let N := bfsLayer J root (k + 1)
  have hsplit (v : V) (hv : v ∈ C) :
      J.neighborFinset v =
        (J.neighborFinset v).filter (fun w => J.dist root w = k - 1) ∪
        (J.neighborFinset v).filter (fun w => J.dist root w = k + 1) := by
    exact bfsLayer_neighborFinset_eq_prev_union_next J hconn D r k hg hD hk hkr root v
      (Finset.mem_filter.mp hv).2
  have hdisjoint (v : V) : Disjoint
      ((J.neighborFinset v).filter (fun w => J.dist root w = k - 1))
      ((J.neighborFinset v).filter (fun w => J.dist root w = k + 1)) := by
    apply Finset.disjoint_left.mpr
    intro w hw₁ hw₂
    have heq := ((Finset.mem_filter.mp hw₁).2).symm.trans
      (Finset.mem_filter.mp hw₂).2
    omega
  have hprev (v : V) (hv : v ∈ C) :
      ((J.neighborFinset v).filter (fun w => J.dist root w = k - 1)).card = 1 := by
    have hv' : J.dist root v = k := (Finset.mem_filter.mp hv).2
    obtain ⟨w, hw, huniq⟩ := existsUnique_preceding_layer_neighbor J hconn D (k - 1)
      hg (by omega) root v (by rw [hv']; omega)
    have hfilter : (J.neighborFinset v).filter
        (fun x => J.dist root x = k - 1) = {w} := by
      ext x
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, hdist⟩
        have h := huniq x ⟨hadj.symm, hdist⟩
        exact h
      · intro h
        subst x
        exact ⟨hw.1.symm, hw.2⟩
    rw [hfilter]
    simp
  have hnext (w : V) (hw : w ∈ N) :
      ((C).filter (fun v => J.Adj v w)).card = 1 := by
    have hw' : J.dist root w = k + 1 := (Finset.mem_filter.mp hw).2
    obtain ⟨v, hv, huniq⟩ := existsUnique_preceding_layer_neighbor J hconn D k
      hg (by omega) root w hw'
    have hfilter : C.filter (fun x => J.Adj x w) = {v} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hadj⟩
        have h := huniq x ⟨hadj, (Finset.mem_filter.mp hx).2⟩
        exact h
      · intro h
        subst x
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩, hv.1⟩
    rw [hfilter]
    simp
  have hnextBip (w : V) (hw : w ∈ N) :
      (C.bipartiteBelow J.Adj w).card = 1 := by
    simpa only [Finset.bipartiteBelow] using hnext w hw
  have hnextSum :
      (∑ v ∈ C, ((J.neighborFinset v).filter
        (fun w => J.dist root w = k + 1)).card) = N.card := by
    calc
      (∑ v ∈ C, ((J.neighborFinset v).filter
        (fun w => J.dist root w = k + 1)).card) =
          ∑ v ∈ C, (N.bipartiteAbove J.Adj v).card := by
            apply Finset.sum_congr rfl
            intro v hv
            congr 1
            ext w
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
              Finset.mem_bipartiteAbove]
            constructor
            · rintro ⟨hadj, hdist⟩
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, hadj⟩
            · rintro ⟨hw, hadj⟩
              exact ⟨hadj, (Finset.mem_filter.mp hw).2⟩
      _ = ∑ w ∈ N, (C.bipartiteBelow J.Adj w).card := by
            exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow J.Adj
      _ = N.card := by
            calc
              _ = ∑ w ∈ N, 1 := by
                    apply Finset.sum_congr rfl
                    intro w hw
                    exact hnextBip w hw
              _ = N.card := by simp
  calc
    (∑ v ∈ C, J.degree v) =
        ∑ v ∈ C,
          (((J.neighborFinset v).filter (fun w => J.dist root w = k - 1)).card +
            ((J.neighborFinset v).filter (fun w => J.dist root w = k + 1)).card) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hcardDegree : J.degree v =
              ((J.neighborFinset v).filter (fun w => J.dist root w = k - 1)).card +
                ((J.neighborFinset v).filter (fun w => J.dist root w = k + 1)).card := by
            rw [← J.card_neighborFinset_eq_degree]
            calc
              (J.neighborFinset v).card =
                  (((J.neighborFinset v).filter (fun w => J.dist root w = k - 1)) ∪
                    ((J.neighborFinset v).filter (fun w => J.dist root w = k + 1))).card :=
                  congrArg Finset.card (hsplit v hv)
              _ = _ := Finset.card_union_of_disjoint (hdisjoint v)
          exact hcardDegree
    _ = C.card + N.card := by
          rw [Finset.sum_add_distrib]
          have hprevSum :
              (∑ v ∈ C, ((J.neighborFinset v).filter
                (fun w => J.dist root w = k - 1)).card) = C.card := by
            calc
              _ = ∑ v ∈ C, 1 := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    exact hprev v hv
              _ = C.card := by simp
          rw [hprevSum, hnextSum]
    _ = (bfsLayer J root k).card + (bfsLayer J root (k + 1)).card := by rfl

/-- The local BFS recurrence follows from the incidence count: the forward
neighbors are the degree-three budget after subtracting the boundary tokens. -/
theorem bfsLayerLevel_succ_eq
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (D r k : ℕ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (hk : 1 ≤ k) (hkr : k < r) (root : V) :
    bfsLayerLevel J root (k + 1) =
      2 * bfsLayerLevel J root k - bfsLayerTokens J root k := by
  let C := bfsLayer J root k
  let N := bfsLayer J root (k + 1)
  have hdeg := bfsLayer_degree_sum_eq J hconn D r k hg hD hk hkr root
  have hdegR : (∑ v ∈ C, (J.degree v : ℝ)) =
      (C.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast hdeg
  have hdegR' : (∑ v ∈ bfsLayer J root k, (J.degree v : ℝ)) =
      ((bfsLayer J root k).card : ℝ) + ((bfsLayer J root (k + 1)).card : ℝ) := by
    simpa [C, N] using hdegR
  have hconst : (∑ _v ∈ C, (3 : ℝ)) = (C.card : ℝ) * 3 := by
    simp [Finset.sum_const]
  have hconst' :
      (∑ _v ∈ bfsLayer J root k, (3 : ℝ)) =
        ((bfsLayer J root k).card : ℝ) * 3 := by
    simpa [C] using hconst
  have htoken : bfsLayerTokens J root k =
      (C.card : ℝ) * 3 - ((C.card : ℝ) + (N.card : ℝ)) := by
    unfold bfsLayerTokens
    rw [Finset.sum_sub_distrib, hconst', hdegR']
  rw [bfsLayerLevel, bfsLayerLevel, htoken]
  dsimp [C, N]
  ring

/-- In an ambient cubic graph, a vertex's unused degree slots in the induced
target region are exactly its ambient neighbor contacts outside the target.
This is the graph-level interpretation of the layer tokens above. -/
theorem induced_degree_deficit_eq_external_contacts
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] [Fintype S] [DecidableEq S]
    (hreg : ∀ v : S, G.degree v = 3) (v : S)
    [Fintype ((G.induce S).neighborSet v)] :
    (3 : ℝ) - ((G.induce S).degree v : ℝ) =
      (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) := by
  let inside := (G.neighborFinset v.1).filter (fun w => w ∈ S.toFinset)
  let outside := (G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)
  have hinside : (G.induce S).degree v = inside.card := by
    rw [← (G.induce S).card_neighborFinset_eq_degree]
    have hcard : ((G.induce S).neighborFinset v).card = inside.card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx
        have hadj : (G.induce S).Adj v x :=
          (SimpleGraph.mem_neighborFinset (G.induce S) v x).1 hx
        have hadj' : G.Adj v.1 x.1 := by
          simpa only [SimpleGraph.Subgraph.induce_adj] using hadj
        simp only [inside, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨hadj', Set.mem_toFinset.mpr x.2⟩
      · intro x hx y hy hxy
        exact Subtype.ext hxy
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        have hadj : G.Adj v.1 y :=
          (SimpleGraph.mem_neighborFinset G v.1 y).1 hy'.1
        have hyS : y ∈ S := Set.mem_toFinset.mp hy'.2
        refine ⟨⟨y, hyS⟩, ?_, rfl⟩
        exact (SimpleGraph.mem_neighborFinset (G.induce S) v ⟨y, hyS⟩).2
          (by simpa only [SimpleGraph.Subgraph.induce_adj] using hadj)
    exact hcard
  have hpartition : G.neighborFinset v.1 = inside ∪ outside := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, inside, outside]
    constructor
    · intro hw
      by_cases h : w ∈ S.toFinset
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
    · rintro (⟨hw, _⟩ | ⟨hw, _⟩)
      · exact hw
      · exact hw
  have hdisjoint : Disjoint inside outside := by
    exact Finset.disjoint_filter_filter_neg (G.neighborFinset v.1)
      (G.neighborFinset v.1) (fun w => w ∈ S.toFinset)
  have hsum : (G.neighborFinset v.1).card = inside.card + outside.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hambient : (G.neighborFinset v.1).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have hthree : 3 = inside.card + outside.card := by
    calc
      3 = (G.neighborFinset v.1).card := hambient.symm
      _ = inside.card + outside.card := hsum
  have hinsideR : ((G.induce S).degree v : ℝ) = (inside.card : ℝ) := by
    exact_mod_cast hinside
  have hthreeR : (3 : ℝ) = (inside.card : ℝ) + (outside.card : ℝ) := by
    exact_mod_cast hthree
  rw [hinsideR]
  have : (outside.card : ℝ) =
      (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) := by rfl
  linarith

/-- For the induced target region, the layer token count is literally the
number of ambient outgoing neighbor contacts based in that BFS layer. -/
theorem bfsLayerTokens_eq_external_contacts
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] [Fintype S] [DecidableEq S]
    (hreg : ∀ v : S, G.degree v = 3) (root : S) (k : ℕ) :
    bfsLayerTokens (G.induce S) root k =
      ∑ v ∈ bfsLayer (G.induce S) root k,
        (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) := by
  unfold bfsLayerTokens
  apply Finset.sum_congr rfl
  intro v hv
  exact induced_degree_deficit_eq_external_contacts G S hreg v

/-- A cubic ambient graph induces a subcubic graph on every finite target
set. -/
theorem induced_degree_le_three_of_cubic
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] [Fintype S] [DecidableEq S]
    (hreg : ∀ v : S, G.degree v = 3) (v : S) :
    (G.induce S).degree v ≤ 3 := by
  have hcontact := induced_degree_deficit_eq_external_contacts G S hreg v
  have hnonneg : (0 : ℝ) ≤
      (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) :=
    Nat.cast_nonneg _
  have hbound : ((G.induce S).degree v : ℝ) ≤ 3 := by linarith
  exact_mod_cast hbound

/-- The total size of the first `r+1` BFS layers never exceeds the order of
the finite graph. This is the volume interface required by the abstract
three-token lemma. -/
theorem bfsLayer_volume_le_order
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V)
    (root : V) (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1), bfsLayerLevel J root k) ≤ Fintype.card V := by
  classical
  let B := Finset.univ.filter (fun v => J.dist root v ≤ r)
  have hmaps : B.toSet.MapsTo (fun v => J.dist root v) (Finset.range (r + 1)) := by
    intro v hv
    have hdist := (Finset.mem_filter.mp hv).2
    apply Finset.mem_range.mpr
    change J.dist root v < r + 1
    omega
  have hsumNat : B.card =
      ∑ k ∈ Finset.range (r + 1),
        (B.filter (fun v => J.dist root v = k)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber (k : ℕ) (hk : k ∈ Finset.range (r + 1)) :
      (B.filter (fun v => J.dist root v = k)).card =
        (bfsLayer J root k).card := by
    congr 1
    ext v
    simp only [B, bfsLayer, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hdist⟩
      exact hdist
    · intro hdist
      exact ⟨by have := Finset.mem_range.mp hk; omega, hdist⟩
  have hsumLayer : B.card =
      ∑ k ∈ Finset.range (r + 1), (bfsLayer J root k).card := by
    rw [hsumNat]
    apply Finset.sum_congr rfl
    intro k hk
    exact hfiber k hk
  have hreal :
      (∑ k ∈ Finset.range (r + 1), bfsLayerLevel J root k) = (B.card : ℝ) := by
    unfold bfsLayerLevel
    exact_mod_cast hsumLayer.symm
  have hB : B.card ≤ Fintype.card V := Finset.card_le_univ B
  have hBreal : (B.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hB
  rw [hreal]
  exact hBreal

/-- Applying the paper's abstract three-token lemma to the actual BFS layers
of a finite high-girth subcubic graph. The only non-geometric input is the
volume bound for the first `r+1` layers. -/
theorem actual_bfs_three_contacts_of_small_order
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (D r : ℕ) (n : ℝ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (root : V) (hmax : ∀ v, J.degree v ≤ 3)
    (hvolume :
      (∑ k ∈ Finset.range (r + 1), bfsLayerLevel J root k) ≤ n)
    (hsmall : n < 2 ^ r) :
    2 < ∑ k ∈ Finset.range r, bfsLayerTokens J root k := by
  have hroot : bfsLayerLevel J root 0 = 1 := bfsLayerLevel_zero J hconn root
  have hfirst : bfsLayerLevel J root 1 = 3 - bfsLayerTokens J root 0 :=
    bfsLayerLevel_one_eq_three_sub_tokens J hconn root
  have hstep : ∀ k, 1 ≤ k → k < r →
      bfsLayerLevel J root (k + 1) = 2 * bfsLayerLevel J root k - bfsLayerTokens J root k := by
    intro k hk hkr
    exact bfsLayerLevel_succ_eq J hconn D r k hg hD hk hkr root
  have htoken : ∀ k, 0 ≤ bfsLayerTokens J root k := by
    intro k
    exact bfsLayerTokens_nonneg J root hmax k
  exact three_tokens_before_radius_of_small_order
    (fun k => bfsLayerLevel J root k) (fun k => bfsLayerTokens J root k) r n
    hroot hfirst hstep htoken hvolume hsmall

/-- The finite-order form, with the BFS volume bound discharged internally. -/
theorem actual_bfs_three_contacts_of_graph_order
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hconn : J.Connected) (D r : ℕ)
    (hg : GirthGreater J D) (hD : 2 * r + 1 ≤ D)
    (root : V) (hmax : ∀ v, J.degree v ≤ 3)
    (hsmall : (Fintype.card V : ℝ) < 2 ^ r) :
    2 < ∑ k ∈ Finset.range r, bfsLayerTokens J root k := by
  apply actual_bfs_three_contacts_of_small_order J hconn D r (Fintype.card V)
    hg hD root hmax ?_ hsmall
  exact_mod_cast bfsLayer_volume_le_order J root r

/-- The abstract three-contact conclusion expressed directly as outgoing
ambient edge contacts from a finite induced target set. -/
theorem induced_target_three_contacts_of_small_order
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] [Fintype S] [DecidableEq S]
    (hreg : ∀ v : S, G.degree v = 3)
    (hconn : (G.induce S).Connected) (D r : ℕ)
    (hg : GirthGreater (G.induce S) D) (hD : 2 * r + 1 ≤ D)
    (root : S) (hsmall : (Fintype.card S : ℝ) < 2 ^ r) :
    2 < ∑ k ∈ Finset.range r,
      ∑ v ∈ bfsLayer (G.induce S) root k,
        (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) := by
  have htokens := actual_bfs_three_contacts_of_graph_order
    (G.induce S) hconn D r hg hD root
    (fun v => induced_degree_le_three_of_cubic G S hreg v) hsmall
  have hcontacts :
      (∑ k ∈ Finset.range r, bfsLayerTokens (G.induce S) root k) =
        ∑ k ∈ Finset.range r,
          ∑ v ∈ bfsLayer (G.induce S) root k,
            (((G.neighborFinset v.1).filter (fun w => w ∉ S.toFinset)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact bfsLayerTokens_eq_external_contacts G S hreg root k
  rw [hcontacts] at htokens
  exact htokens

end Erdos1016.Proof.BreadthFirstLayers

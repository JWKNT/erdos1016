import Erdos1016.ExactMaximum.GirthFive.RegionRigidity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Regions between two distance levels

`K` is a connected graph, `o` a vertex, and the *level* of a vertex is its distance from `o`.
For an interval `[a, c]` of levels and a vertex `u`, the *level region* is the set of the
vertices that a walk through the levels `a, ..., c` joins to `u` (`levelRegion`).

* A level region is connected, and an edge at a vertex of an inner level stays in the region
  (`levelRegion_connected`, `levelRegion_inner`).
* If every level has at most `W` vertices, the region has at most `(c + 1 - a) W` vertices
  (`levelRegion_card_le`).
* The vertices of a shortest walk `A` from `o` have the levels `0, 1, 2, ...` (`dist_spine`).
  They are the *spine* of the regions at `A.getVert a`.

The main statement is `window_not_rigid`. Let `N` be a multigraph without cycles of length less
than five and with all degrees at most three. Suppose that every level has at most `W` vertices
and that the vertices of the levels `a, ..., c` are cubic, where `c = a + n τ + 1` with
`n > 2 W` and `τ > 400 (2 W + 2)`. Let `R` be the level region of `[a, c]` at the spine, and let
`w` be a word on the internal edges of `R` whose boundary vanishes at the inner levels. Then
some word `w + z`, with `z` an even word on the internal edges of `R`, is not a forest. The
proof applies `region_not_rigid` to `n` slabs of `τ` levels.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open SimpleGraph FiniteMultiGraph Erdos1016.Nonbacktracking.ShortWalks
open Erdos1016.ExactMaximumSupport.LargeGirth Erdos1016.PolynomialBound.Separation

local instance levelRegionsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Levels

variable {V : Type*} [Fintype V] (K : SimpleGraph V) (o : V)

/-- The vertices with level outside the interval `[a, c]`. -/
def offBand (a c : ℕ) : Set V := {v | K.dist o v < a ∨ c < K.dist o v}

omit [Fintype V] in
theorem not_mem_offBand {a c : ℕ} {v : V} :
    v ∉ offBand K o a c ↔ a ≤ K.dist o v ∧ K.dist o v ≤ c := by
  show ¬ (K.dist o v < a ∨ c < K.dist o v) ↔ a ≤ K.dist o v ∧ K.dist o v ≤ c
  constructor
  · intro h
    exact ⟨not_lt.mp (fun h1 => h (Or.inl h1)), not_lt.mp (fun h2 => h (Or.inr h2))⟩
  · rintro ⟨h1, h2⟩ (h | h) <;> omega

/-- The level region of the interval `[a, c]` at the vertex `u`. -/
def levelRegion (a c : ℕ) (u : V) : Finset V :=
  Finset.univ.filter (fun v => AvoidReach K (offBand K o a c) u v)

theorem mem_levelRegion {a c : ℕ} {u v : V} :
    v ∈ levelRegion K o a c u ↔ AvoidReach K (offBand K o a c) u v := by
  simp only [levelRegion, Finset.mem_filter, Finset.mem_univ, true_and]

theorem levelRegion_level {a c : ℕ} {u v : V} (h : v ∈ levelRegion K o a c u) :
    a ≤ K.dist o v ∧ K.dist o v ≤ c :=
  (not_mem_offBand K o).mp ((mem_levelRegion K o).mp h).right_not_mem

theorem levelRegion_connected (a c : ℕ) (u : V) :
    IsConnectedSet K (↑(levelRegion K o a c u) : Set V) := by
  intro x hx y hy
  have hx' := (mem_levelRegion K o).mp (Finset.mem_coe.mp hx)
  have hy' := (mem_levelRegion K o).mp (Finset.mem_coe.mp hy)
  obtain ⟨p, hp⟩ := hx'.symm.trans hy'
  refine ⟨p, fun v hv => ?_⟩
  have hv' : AvoidReach K (offBand K o a c) u v :=
    hx'.trans (avoidReach_of_mem_support p hp hv)
  exact Finset.mem_coe.mpr ((mem_levelRegion K o).mpr hv')

theorem levelRegion_adj {a c : ℕ} {u v x : V} (hv : v ∈ levelRegion K o a c u)
    (hadj : K.Adj v x) (hx : a ≤ K.dist o x ∧ K.dist o x ≤ c) :
    x ∈ levelRegion K o a c u :=
  (mem_levelRegion K o).mpr
    (((mem_levelRegion K o).mp hv).step hadj ((not_mem_offBand K o).mpr hx))

omit [Fintype V] in
theorem dist_adj_le (hK : K.Connected) {v x : V} (hadj : K.Adj v x) :
    K.dist o x ≤ K.dist o v + 1 := by
  have h := hK.dist_triangle (u := o) (v := v) (w := x)
  rw [dist_eq_one_iff_adj.mpr hadj] at h
  exact h

/-- An edge at a vertex of an inner level stays in the region. -/
theorem levelRegion_inner (hK : K.Connected) {a c : ℕ} {u v x : V}
    (hv : v ∈ levelRegion K o a c u) (hlo : a < K.dist o v) (hhi : K.dist o v < c)
    (hadj : K.Adj v x) : x ∈ levelRegion K o a c u := by
  apply levelRegion_adj K o hv hadj
  have h1 := dist_adj_le K o hK hadj
  have h2 := dist_adj_le K o hK hadj.symm
  omega

theorem levelRegion_mono {a c a' c' : ℕ} {u u' : V} (ha : a ≤ a') (hc : c' ≤ c)
    (hu : AvoidReach K (offBand K o a c) u u') :
    levelRegion K o a' c' u' ⊆ levelRegion K o a c u := by
  intro v hv
  rw [mem_levelRegion] at hv ⊢
  refine hu.trans (hv.mono ?_)
  intro x hx
  rcases hx with h | h
  · exact Or.inl (lt_of_lt_of_le h ha)
  · exact Or.inr (lt_of_le_of_lt hc h)

/-- A level region is small if every level is small. -/
theorem levelRegion_card_le (W : ℕ)
    (hW : ∀ l, (Finset.univ.filter (fun v => K.dist o v = l)).card ≤ W) (a c : ℕ) (u : V) :
    (levelRegion K o a c u).card ≤ (c + 1 - a) * W := by
  have hsub : levelRegion K o a c u ⊆
      (Finset.Icc a c).biUnion (fun l => Finset.univ.filter (fun v => K.dist o v = l)) := by
    intro v hv
    have h := levelRegion_level K o hv
    exact Finset.mem_biUnion.mpr ⟨K.dist o v, Finset.mem_Icc.mpr h,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc
    (levelRegion K o a c u).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc a c).card * W :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun l _ => hW l)
    _ = (c + 1 - a) * W := by rw [Nat.card_Icc]

/-- A set in two levels has at most `2 W` vertices. -/
theorem two_levels_card_le (W : ℕ)
    (hW : ∀ l, (Finset.univ.filter (fun v => K.dist o v = l)).card ≤ W) (S : Finset V)
    (l₁ l₂ : ℕ) (h : ∀ v ∈ S, K.dist o v = l₁ ∨ K.dist o v = l₂) : S.card ≤ 2 * W := by
  have hsub : S ⊆ Finset.univ.filter (fun v => K.dist o v = l₁) ∪
      Finset.univ.filter (fun v => K.dist o v = l₂) := by
    intro v hv
    rcases h v hv with h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter (fun v => K.dist o v = l₁))
    (Finset.univ.filter (fun v => K.dist o v = l₂))
  have h3 := hW l₁
  have h4 := hW l₂
  omega

section Spine

variable {t : V} (A : K.Walk o t) (hshort : ∀ q : K.Walk o t, A.length ≤ q.length)

omit [Fintype V] in
include hshort in
/-- The vertex at position `i` of a shortest walk from `o` has level `i`. -/
theorem dist_spine {i : ℕ} (hi : i ≤ A.length) : K.dist o (A.getVert i) = i := by
  obtain ⟨Wp, hWp⟩ := exists_prefix A hi
  apply le_antisymm
  · have h := K.dist_le Wp
    omega
  · obtain ⟨p, hp⟩ := Wp.reachable.exists_walk_length_eq_dist
    rw [← hp]
    exact geodesic_prefix A hshort hi p

omit [Fintype V] in
/-- A part of the walk avoids a set if its vertices are outside the set. -/
theorem spine_reach (X : Set V) : ∀ (n i : ℕ), i + n ≤ A.length →
    (∀ l, i ≤ l → l ≤ i + n → A.getVert l ∉ X) →
    AvoidReach K X (A.getVert i) (A.getVert (i + n)) := by
  intro n
  induction n with
  | zero =>
    intro i _ h
    exact AvoidReach.refl (h i le_rfl le_rfl)
  | succ n ih =>
    intro i hi h
    have h1 := ih i (by omega) (fun l hl1 hl2 => h l hl1 (by omega))
    exact h1.step (A.adj_getVert_succ (by omega)) (h (i + n + 1) (by omega) (by omega))

omit [Fintype V] in
theorem spine_reach' (X : Set V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ A.length)
    (h : ∀ l, i ≤ l → l ≤ j → A.getVert l ∉ X) :
    AvoidReach K X (A.getVert i) (A.getVert j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact spine_reach K o A X n i hj h

include hshort in
/-- The spine vertices of the levels `a, ..., c` are in the level region. -/
theorem spine_mem_levelRegion {a c i : ℕ} (hai : a ≤ i) (hic : i ≤ c) (hc : c ≤ A.length) :
    A.getVert i ∈ levelRegion K o a c (A.getVert a) := by
  rw [mem_levelRegion]
  apply spine_reach' K o A _ hai (by omega)
  intro l hl1 hl2
  rw [not_mem_offBand, dist_spine K o A hshort (by omega)]
  omega

end Spine

end Levels

/-- **A window of cubic levels is not rigid.** -/
theorem window_not_rigid (N : FiniteMultiGraph) (hconn : N.toSimpleGraph.Connected)
    (h5 : ¬ N.HasCycleShorterThan 5) (hmax : ∀ v, N.degree v ≤ 3)
    {o t : N.Vertex} (A : N.toSimpleGraph.Walk o t)
    (hshort : ∀ q : N.toSimpleGraph.Walk o t, A.length ≤ q.length)
    (W τ n a : ℕ)
    (hW : ∀ l, (Finset.univ.filter (fun v => N.toSimpleGraph.dist o v = l)).card ≤ W)
    (hτ : 400 * (2 * W + 2) < τ) (hn : 2 * W < n)
    (hc : a + n * τ + 1 ≤ A.length)
    (hcubic : ∀ v, a ≤ N.toSimpleGraph.dist o v →
      N.toSimpleGraph.dist o v ≤ a + n * τ + 1 → N.degree v = 3)
    (w : N.EdgeWord)
    (hw : ∀ e, w e ≠ 0 → e ∈ N.internalEdges
      (levelRegion N.toSimpleGraph o a (a + n * τ + 1) (A.getVert a)))
    (hb : ∀ v, a < N.toSimpleGraph.dist o v → N.toSimpleGraph.dist o v < a + n * τ + 1 →
      N.boundary w v = 0) :
    ∃ z : N.internalCycleSpace
        (levelRegion N.toSimpleGraph o a (a + n * τ + 1) (A.getVert a)),
      ¬ N.IsForestWord (w + z.1.1) := by
  let c := a + n * τ + 1
  let R := levelRegion N.toSimpleGraph o a c (A.getVert a)
  -- the slab `i` has the levels `lo i, ..., hi i`
  let lo : ℕ → ℕ := fun i => a + i * τ + 1
  let hi : ℕ → ℕ := fun i => a + (i + 1) * τ
  have hsucc : ∀ i : ℕ, (i + 1) * τ = i * τ + τ := fun i => by ring
  have hlohi : ∀ i, lo i < hi i := by
    intro i
    have := hsucc i
    show a + i * τ + 1 < a + (i + 1) * τ
    omega
  have hhilo : ∀ i j : ℕ, i < j → hi i < lo j := by
    intro i j hij
    have := Nat.mul_le_mul_right τ (show i + 1 ≤ j from hij)
    show a + (i + 1) * τ < a + j * τ + 1
    omega
  have hhic : ∀ i : ℕ, i < n → hi i < c := by
    intro i hin
    have := Nat.mul_le_mul_right τ (show i + 1 ≤ n from hin)
    show a + (i + 1) * τ < a + n * τ + 1
    omega
  have hloa : ∀ i : ℕ, a < lo i := by
    intro i
    show a < a + i * τ + 1
    omega
  have hlev : ∀ l, l ≤ A.length → N.toSimpleGraph.dist o (A.getVert l) = l :=
    fun l hl => dist_spine N.toSimpleGraph o A hshort hl
  have hspR : ∀ l, a ≤ l → l ≤ c → A.getVert l ∈ R :=
    fun l h1 h2 => spine_mem_levelRegion N.toSimpleGraph o A hshort h1 h2 hc
  let B : Fin n → Finset N.Vertex :=
    fun i => levelRegion N.toSimpleGraph o (lo i) (hi i) (A.getVert (lo i))
  let D : Fin n → Finset N.Vertex :=
    fun i => (B i).filter (fun v => N.toSimpleGraph.dist o v = lo i ∨ N.toSimpleGraph.dist o v = hi i)
  have hBlev : ∀ (i : Fin n) v, v ∈ B i → lo i ≤ N.toSimpleGraph.dist o v ∧ N.toSimpleGraph.dist o v ≤ hi i :=
    fun i v hv => levelRegion_level N.toSimpleGraph o hv
  have hspB : ∀ (i : Fin n) l, lo i ≤ l → l ≤ hi i → A.getVert l ∈ B i := by
    intro i l h1 h2
    have := hhic i i.2
    exact spine_mem_levelRegion N.toSimpleGraph o A hshort h1 h2 (by omega)
  have hBR : ∀ i, B i ⊆ R := by
    intro i
    have h1 := hloa i
    have h2 := hhic i i.2
    have h3 := hlohi i
    exact levelRegion_mono N.toSimpleGraph o (by omega) (by omega)
      ((mem_levelRegion N.toSimpleGraph o).mp (hspR (lo i) (by omega) (by omega)))
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have h1 := hBlev i v hvi
    have h2 := hBlev j v hvj
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hhilo i j h
      omega
    · have := hhilo j i h
      omega
  have hD : ∀ i, ∀ v ∈ B i, v ∉ D i →
      N.degree v = 3 ∧ ∀ u, N.toSimpleGraph.Adj v u → u ∈ B i := by
    intro i v hv hvD
    have h1 := hBlev i v hv
    have h2 : N.toSimpleGraph.dist o v ≠ lo i := fun h =>
      hvD (Finset.mem_filter.mpr ⟨hv, Or.inl h⟩)
    have h3 : N.toSimpleGraph.dist o v ≠ hi i := fun h =>
      hvD (Finset.mem_filter.mpr ⟨hv, Or.inr h⟩)
    have h4 := hloa i
    have h5' := hhic i i.2
    refine ⟨hcubic v (by omega) (by omega), ?_⟩
    intro u hadj
    exact levelRegion_inner N.toSimpleGraph o hconn hv (by omega) (by omega) hadj
  have hsize : ∀ i, 400 * ((D i).card + 2) < (B i).card := by
    intro i
    have hDcard : (D i).card ≤ 2 * W :=
      two_levels_card_le N.toSimpleGraph o W hW (D i) (lo i) (hi i)
        (fun v hv => (Finset.mem_filter.mp hv).2)
    have h2 := hhic i i.2
    have hinj : Set.InjOn (fun l => A.getVert l) (↑(Finset.Icc (lo i) (hi i)) : Set ℕ) := by
      intro l hl l' hl' h
      have hl1 := Finset.mem_Icc.mp (Finset.mem_coe.mp hl)
      have hl2 := Finset.mem_Icc.mp (Finset.mem_coe.mp hl')
      exact geodesic_getVert_injective A hshort (by omega) (by omega) h
    have himg : (Finset.Icc (lo i) (hi i)).image (fun l => A.getVert l) ⊆ B i := by
      intro v hv
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
      have hl1 := Finset.mem_Icc.mp hl
      exact hspB i l hl1.1 hl1.2
    have hcard : τ ≤ (B i).card := by
      calc
        τ = (Finset.Icc (lo i) (hi i)).card := by
          rw [Nat.card_Icc]
          have := hsucc i
          show τ = a + (i + 1) * τ + 1 - (a + i * τ + 1)
          omega
        _ = ((Finset.Icc (lo i) (hi i)).image (fun l => A.getVert l)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (B i).card := Finset.card_le_card himg
    omega
  let sm : Fin n → N.Vertex := fun i => A.getVert (a + i * τ)
  let sp : Fin n → N.Vertex := fun i => A.getVert (hi i + 1)
  let xm : Fin n → N.Vertex := fun i => A.getVert (lo i)
  let xp : Fin n → N.Vertex := fun i => A.getVert (hi i)
  have hsm : ∀ i, sm i ∈ R ∧ sm i ∉ B i := by
    intro i
    have h1 := hhic i i.2
    have h2 := hlohi i
    have h3 : a + i * τ + 1 = lo i := rfl
    refine ⟨hspR _ (by omega) (by omega), ?_⟩
    intro hmem
    have h4 := (hBlev i _ hmem).1
    rw [hlev _ (by omega)] at h4
    omega
  have hsp : ∀ i, sp i ∈ R ∧ sp i ∉ B i := by
    intro i
    have h1 := hhic i i.2
    have h2 := hlohi i
    have h3 := hloa i
    refine ⟨hspR _ (by omega) (by omega), ?_⟩
    intro hmem
    have h4 := (hBlev i _ hmem).2
    rw [hlev _ (by omega)] at h4
    omega
  have hxm : ∀ i, xm i ∈ B i ∧ N.toSimpleGraph.Adj (sm i) (xm i) := by
    intro i
    have h1 := hhic i i.2
    have h2 := hlohi i
    have h3 : a + i * τ + 1 = lo i := rfl
    exact ⟨hspB i _ le_rfl h2.le, A.adj_getVert_succ (by omega)⟩
  have hxp : ∀ i, xp i ∈ B i ∧ N.toSimpleGraph.Adj (sp i) (xp i) := by
    intro i
    have h1 := hhic i i.2
    have h2 := hlohi i
    exact ⟨hspB i _ h2.le le_rfl, (A.adj_getVert_succ (by omega)).symm⟩
  have hxne : ∀ i, xm i ≠ xp i := by
    intro i h
    have h1 := hhic i i.2
    have h2 := hlohi i
    have := geodesic_getVert_injective A hshort (by omega) (by omega) h
    omega
  have hspine : ∀ i j : Fin n, i ≠ j → ∀ v ∈ B j,
      AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sm i) v ∨
      AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sp i) v := by
    intro i j hij v hv
    have hd : Disjoint (↑(B j) : Set N.Vertex) (slabCut N R (B i)) := by
      apply Set.disjoint_left.mpr
      intro x hx hxc
      have hxj : x ∈ B j := Finset.mem_coe.mp hx
      rcases hxc with h | h
      · exact h (hBR j hxj)
      · exact Finset.disjoint_left.mp (hdisj i j hij) h hxj
    have hxv : AvoidReach N.toSimpleGraph (slabCut N R (B i)) (xm j) v :=
      (levelRegion_connected N.toSimpleGraph o (lo j) (hi j) (A.getVert (lo j))).avoidReach hd
        (Finset.mem_coe.mpr (hxm j).1) (Finset.mem_coe.mpr hv)
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have h1 := hhic i i.2
    have h2 := hlohi i
    have h3 := hhic j j.2
    have h4 := hlohi j
    have h5' := hloa j
    have h6 := hloa i
    have h7 : a + i * τ + 1 = lo i := rfl
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · -- the slab `j` is above the slab `i`
      have h8 := hhilo i j h
      have hreach : AvoidReach N.toSimpleGraph (slabCut N R (B i)) (sp i) (xm j) := by
        apply spine_reach' N.toSimpleGraph o A _ (by omega) (by omega)
        intro l hl1 hl2
        refine (not_mem_slabCut N).mpr ⟨hspR l (by omega) (by omega), ?_⟩
        intro hmem
        have h9 := (hBlev i _ hmem).2
        rw [hlev l (by omega)] at h9
        omega
      exact Or.inr (hreach.trans hxv)
    · -- the slab `j` is below the slab `i`
      have h8 := hhilo j i h
      have hreach : AvoidReach N.toSimpleGraph (slabCut N R (B i)) (xm j) (sm i) := by
        apply spine_reach' N.toSimpleGraph o A _ (by omega) (by omega)
        intro l hl1 hl2
        refine (not_mem_slabCut N).mpr ⟨hspR l (by omega) (by omega), ?_⟩
        intro hmem
        have h9 := (hBlev i _ hmem).1
        rw [hlev l (by omega)] at h9
        omega
      exact Or.inl (hreach.symm.trans hxv)
  have hbB : ∀ i, ∀ v ∈ B i, N.boundary w v = 0 := by
    intro i v hv
    have h1 := hBlev i v hv
    have h2 := hloa i
    have h3 := hhic i i.2
    exact hb v (by omega) (by omega)
  have hcount : (Finset.univ.filter (fun v => N.boundary w v ≠ 0)).card <
      Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    have hle : (Finset.univ.filter (fun v => N.boundary w v ≠ 0)).card ≤ 2 * W := by
      apply two_levels_card_le N.toSimpleGraph o W hW _ a c
      intro v hv
      have hne := (Finset.mem_filter.mp hv).2
      have hvR : v ∈ R := Classical.byContradiction
        (fun hnotR => hne (boundary_eq_zero_of_not_mem N R w hw hnotR))
      have h1 := levelRegion_level N.toSimpleGraph o hvR
      rcases Nat.lt_or_ge a (N.toSimpleGraph.dist o v) with h2 | h2
      · rcases Nat.lt_or_ge (N.toSimpleGraph.dist o v) c with h3 | h3
        · exact absurd (hb v h2 h3) hne
        · exact Or.inr (le_antisymm h1.2 h3)
      · exact Or.inl (le_antisymm h2 h1.1)
    omega
  exact region_not_rigid N h5 hmax R (levelRegion_connected N.toSimpleGraph o a c (A.getVert a))
    B D sm sp xm xp hBR (fun i => levelRegion_connected N.toSimpleGraph o (lo i) (hi i) (A.getVert (lo i)))
    hdisj hD hsize hsm hsp hxm hxp hxne hspine w hw hbB hcount

end Erdos1016.ExactMaximum.GirthFive

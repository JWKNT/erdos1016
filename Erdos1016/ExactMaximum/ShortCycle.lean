import Erdos1016.ExactMaximum.ShortCycleCount
import Erdos1016.ExactMaximum.CycleBoundMargin
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.ExactMaximum.Cases
import Erdos1016.ExactMaximumSupport.NetworkShortCycleCut

set_option autoImplicit false

/-!
# A short cycle

This file proves Theorem 7.1 of the paper "The maximum number of cycles in a graph of large
rank" (Case 4 of the proof of Theorem 1.1) from the statement of `CyclicShore.lean`, which is
Corollary 5.6 for the pole alone:

`shortCycleStatement_of_shore : CyclicShoreStatement → ShortCycleStatement`.

The steps:

1. `rank_sub_add_one_le`, `networkRank_sub_ne`: the network without an edge `e` of a cycle has
   rank `r - 1`.
2. `ShortSetting.initial`: the first state of the recursion of `ShortCycleCount.lean` is the
   cycle `C` without the edge `e`.
3. `numCycles_lt_of_short_cycle`: `c(N) ≤ c(N - e) + P`; the first term is at most
   `(1/2 + 2^(-m-1)) 2^(r-1)` (`numCycles_le_of_large_rank_margin`), and the second term is
   bounded by `ShortState.count`. With `m ≥ |C| + 2` the sum is less than `2^(r-1)` for large
   `r`.
4. The multigraph: a cycle with fewer than `D` edges gives a shortest cycle `C` of the network
   with fewer than `D` edges; it has at least five edges because there is no cyclic cut with at
   most four edges (`four_lt_size_of_cyclic_cut_lower_bound`, by Astra).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance shortCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-! ### The rank without an edge of a cycle -/

section Rank

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **A part that misses an edge of a word with even degrees has smaller rank.** -/
theorem rank_sub_add_one_le (N : Network V E) (p : E → Prop) {Z : N.Word}
    (hZ : N.boundary Z = 0) {g : E} (hg : Z g ≠ 0) (hp : ¬ p g) :
    networkRank (N.sub p) + 1 ≤ networkRank N := by
  have h1 := (N.sub p).natCard_even
  have h2 := N.natCard_even
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : N.Word → Prop, ∀ x, P₀ x ↔ (N.boundary x = 0 ∧ x g = 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : N.Word → Prop, ∀ x, P₁ x ↔ (N.boundary x = 0 ∧ x g ≠ 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  have k1 : Nat.card {y : (N.sub p).Word // (N.sub p).boundary y = 0} ≤
      Nat.card {x : N.Word // P₀ x} := by
    obtain ⟨φ, hφ⟩ : ∃ φ : {y : (N.sub p).Word // (N.sub p).boundary y = 0} →
        {x : N.Word // P₀ x}, ∀ y, (φ y).1 = extend p y.1 := by
      refine ⟨fun y => ⟨extend p y.1, (hP₀ _).2 ⟨?_, extend_apply_of_neg p _ hp⟩⟩, fun _ => rfl⟩
      rw [N.boundary_extend p y.1]
      exact y.2
    apply Nat.card_le_card_of_injective φ
    intro y y' hyy
    have h : extend p y.1 = extend p y'.1 := by rw [← hφ y, ← hφ y', hyy]
    exact Subtype.ext (extend_injective p h)
  have k2 : Nat.card {x : N.Word // P₀ x} ≤ Nat.card {x : N.Word // P₁ x} := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : {x : N.Word // P₀ x} → {x : N.Word // P₁ x},
        ∀ x, (ψ x).1 = x.1 + Z := by
      refine ⟨fun x => ⟨x.1 + Z, (hP₁ _).2 ⟨?_, ?_⟩⟩, fun _ => rfl⟩
      · rw [map_add, ((hP₀ _).1 x.2).1, hZ, add_zero]
      · show x.1 g + Z g ≠ 0
        rw [((hP₀ _).1 x.2).2, zero_add]
        exact hg
    apply Nat.card_le_card_of_injective ψ
    intro x x' hxx
    have h : x.1 + Z = x'.1 + Z := by rw [← hψ x, ← hψ x', hxx]
    exact Subtype.ext (add_right_cancel h)
  have k3 : Nat.card {x : N.Word // P₀ x} + Nat.card {x : N.Word // P₁ x} ≤
      Nat.card {x : N.Word // N.boundary x = 0} :=
    natCard_add_le_of_imp P₀ P₁ (fun x => N.boundary x = 0) (fun x h => ((hP₀ x).1 h).1)
      (fun x h => ((hP₁ x).1 h).1) (fun x h h' => ((hP₁ x).1 h').2 ((hP₀ x).1 h).2)
  have k4 : 2 ^ (networkRank (N.sub p) + 1) ≤ 2 ^ networkRank N := by
    rw [pow_succ]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 k4

/-- **The network without an edge of a cycle has rank `r - 1`**, if the network is connected.
The statement is for every set `p` of edges that is the set of all edges other than `e`. -/
theorem networkRank_sub_of_iff_ne (N : Network V E) (hN : N.graph.Connected) {Z : N.Word}
    (hZ : N.boundary Z = 0) {e : E} (he : Z e ≠ 0) (p : E → Prop) (hp : ∀ g, p g ↔ g ≠ e) :
    networkRank (N.sub p) + 1 = networkRank N := by
  have h1 := N.rank_sub_add_one_le p hZ he (fun h => (hp e).1 h rfl)
  have e0 := network_rank_euler N
  rw [connected_component_card N hN] at e0
  simp only [← Nat.card_eq_fintype_card] at e0
  obtain ⟨T, hT⟩ : ∃ T : V → Prop, ∀ v, T v := ⟨fun _ => True, fun _ => trivial⟩
  have h2 := N.rank_sub_ge p T (s₀ := N.src e) (hT _) (fun _ _ => ⟨hT _, hT _⟩)
  have h3 : Nat.card {v : V // T v} = Nat.card V :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hT)
  have h4 : Nat.card {g : E // p g} + Nat.card {g : E // g = e} = Nat.card E := by
    rw [← natCard_or_of_disjoint p (fun g => g = e) (fun g h1 h2 => (hp g).1 h1 h2)]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun g => (Classical.em (g = e)).elim Or.inr (fun h => Or.inl ((hp g).2 h))))
  have h5 : Nat.card {g : E // g = e} = 1 := Nat.card_unique
  omega

/-- **The network without an edge of a cycle has rank `r - 1`**, if the network is connected. -/
theorem networkRank_sub_ne (N : Network V E) (hN : N.graph.Connected) {Z : N.Word}
    (hZ : N.boundary Z = 0) {e : E} (he : Z e ≠ 0) [inst : Fintype {g : E // g ≠ e}] :
    networkRank (N.sub fun g => g ≠ e) + 1 = networkRank N := by
  have h := N.networkRank_sub_of_iff_ne hN hZ he (fun g => g ≠ e) (fun _ => Iff.rfl)
  convert h

/-- **A cycle without an edge is a path** between the ends of the edge. -/
theorem IsCycleWord.erase_edge {N : Network V E} {x : N.Word} (hx : N.IsCycleWord x) {e : E}
    {a b : V} (he : N.Joins e a b) (hxe : x e ≠ 0) : N.IsPathWord a b (x + unitWord e) := by
  have hsub : N.IsSubword (x + unitWord e) x := (N.isSubword_unitWord hxe).add_self
  apply N.isPathWord_of_minimal he.ne
  · rw [map_add, hx.boundary_eq_zero, zero_add, N.boundary_unitWord_of_joins he]
    rfl
  · intro y hy hy0
    refine Classical.not_not.1 fun hne => ?_
    have hyx := hx.eq_of_even_subword (fun g hg => hsub g (hy g hg)) hy0 hne
    have h1 := ((add_unitWord_ne_zero_iff hxe e).1 (hy e (by rw [hyx]; exact hxe))).2
    exact h1 rfl

end Rank

/-! ### The first state -/

variable {V E : Type} [Fintype V] [Fintype E]

/-- **The first state**: nothing is deleted, and the path is the cycle without the edge `e`. -/
theorem ShortSetting.initial {N : Network V E} {C : N.Word} {e : E} (H : N.ShortSetting C e)
    {v₀ t : V} (he : N.Joins e v₀ t) :
    N.ShortState C e t (fun _ => False) (C + unitWord e) v₀ := by
  refine ⟨H.cyc.erase_edge he H.mem, (N.isSubword_unitWord H.mem).add_self, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨((add_unitWord_ne_zero_iff H.mem g).1 hg).2, fun h => h, fun h => h⟩
  · intro g hg
    by_cases hge : g = e
    · exact Or.inr (fun hk => hk.1 hge)
    · exact Or.inl ((add_unitWord_ne_zero_iff H.mem g).2 ⟨hg, hge⟩)
  · intro v hv
    exact absurd hv (fun h => h)
  · intro v hv _
    have h2 : N.deg C v = 2 := by
      rcases H.cyc.2.1 v with h | h
      · omega
      · exact h
    have h2' : 1 < (Finset.univ.filter fun g : E =>
        C g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card := by
      have h3 : N.deg C v = (Finset.univ.filter fun g : E =>
          C g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card := rfl
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2'
    have ha := (Finset.mem_filter.1 ha).2
    have hb := (Finset.mem_filter.1 hb).2
    by_cases hae : a = e
    · have hbe : b ≠ e := fun h => hab (hae.trans h.symm)
      exact N.deg_pos_of_edge ((add_unitWord_ne_zero_iff H.mem b).2 ⟨hb.1, hbe⟩) hb.2
    · exact N.deg_pos_of_edge ((add_unitWord_ne_zero_iff H.mem a).2 ⟨ha.1, hae⟩) ha.2
  · have h1 := size_add_of_subword (N.isSubword_unitWord H.mem)
    rw [size_unitWord] at h1
    omega

/-! ### Theorem 7.1 for networks -/

/-- The arithmetic at the end of the proof of Theorem 7.1. -/
theorem short_cycle_arith {a A m c c₀ P X Z T : ℕ} (ha : a = 2 * 2 ^ m) (hA : A = 2 ^ m + 2)
    (h1 : c ≤ c₀ + P) (h2 : a * c₀ ≤ (2 ^ m + 1) * X) (h3 : a * P + A * Z ≤ T + A * X)
    (h4 : 8 * X ≤ A * Z) (h5 : T ≤ X) (hX : 0 < X) : c < X := by
  have k1 : a * c ≤ a * c₀ + a * P := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ h1
  have k2 : (2 ^ m + 1) * X + A * X = a * X + 3 * X := by
    rw [ha, hA]
    ring
  have k3 : a * c < a * X := by omega
  exact Nat.lt_of_mul_lt_mul_left k3

/-- **Theorem 7.1 of the paper for networks.** Let `N` be a connected cubic network without a
cyclic cut with at most four crossing edges, and let `C` be a shortest cycle, with at least five
edges. Let the statement of `CyclicShore.lean` hold for the numbers `m ≥ |C| + 2`,
`G ≥ 12 |C|` and `B₁`, and let every network of rank at least `B₂` have at most
`(1/2 + 2^(-m-1)) 2^b` cycles. If the rank `r` of `N` is large, then `N` has fewer than `2^(r-1)`
cycles. -/
theorem numCycles_lt_of_short_cycle {m G B₁ B₂ : ℕ}
    (hshore : ∀ (V E : Type) [Fintype V] [Fintype E] (K : Network V E), K.IsWeakPole →
      Nat.card {v : V // K.IsPort v} ≤ G + 2 → B₁ ≤ networkRank K →
      ∀ s t : V, K.IsPort s → K.IsPort t → s ≠ t →
        (2 ^ m + 2) * 2 ^ networkRank K ≤ 2 ^ (m + 1) * K.numPaths s t →
        ∃ S : V → Prop, K.IsCyclicCut S ∧ K.cutSize S ≤ 4 ∧
          ∀ v, S v → K.deg (fun _ => 1) v = 3)
    (hbound : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B₂ ≤ networkRank N →
      2 ^ (m + 1) * N.numCycles ≤ (2 ^ m + 1) * 2 ^ networkRank N)
    (N : Network V E) (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hcut : ∀ S : V → Prop, N.IsCyclicCut S → 5 ≤ N.cutSize S) (C : N.Word)
    (hC : N.IsCycleWord C) (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z)
    (h5 : 5 ≤ size C) (hG : 12 * size C ≤ G) (hm : size C + 2 ≤ m)
    (hr : size C + m + B₁ + B₂ + 3 ≤ networkRank N) :
    N.numCycles < 2 ^ (networkRank N - 1) := by
  obtain ⟨e, he⟩ := hC.exists_edge
  have hj : N.Joins e (N.src e) (N.dst e) := Or.inl ⟨rfl, rfl⟩
  have H : N.ShortSetting C e := ⟨hN, hcubic, hC, hmin, h5, he⟩
  have St := H.initial hj
  have hsz : size (C + unitWord e) = size C - 1 := by
    have h1 := size_add_of_subword (N.isSubword_unitWord he)
    rw [size_unitWord] at h1
    omega
  have hcount := ShortState.count hshore H hcut hG (by omega) (Or.inr rfl) (size C - 1) _ _ _
    St hsz
  rw [N.numPathsIn_congr (q' := fun g => g ≠ e)
    (fun g => ⟨fun h => h.1, fun h => ⟨h, fun k => k, fun k => k⟩⟩)] at hcount
  have e1 : networkRank N - size C + (size C - 1) = networkRank N - 1 := by omega
  rw [e1] at hcount
  -- the cycles through `e` and the other cycles
  have hE := N.numCycles_le_add_numPathsIn hj
  have hrank := N.networkRank_sub_ne hN hC.boundary_eq_zero he
  have hb := hbound V _ (N.sub fun g => g ≠ e) (by omega)
  have e2 : networkRank (N.sub fun g => g ≠ e) = networkRank N - 1 := by omega
  rw [e2] at hb
  -- the arithmetic
  have hX : 0 < 2 ^ (networkRank N - 1) := Nat.two_pow_pos _
  have h4 : 8 * 2 ^ (networkRank N - 1) ≤ (2 ^ m + 2) * 2 ^ (networkRank N - size C) := by
    have k1 : 8 * 2 ^ (networkRank N - 1) = 2 ^ (networkRank N - 1 + 3) := by
      rw [pow_add]
      norm_num
      ring
    have k2 : 2 ^ (networkRank N - 1 + 3) ≤ 2 ^ (m + (networkRank N - size C)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have k3 : 2 ^ (m + (networkRank N - size C)) = 2 ^ m * 2 ^ (networkRank N - size C) :=
      pow_add 2 m _
    have k4 : 2 ^ m * 2 ^ (networkRank N - size C) ≤
        (2 ^ m + 2) * 2 ^ (networkRank N - size C) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    omega
  have h5' : 2 ^ (m + 1) + (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) ≤ 2 ^ (networkRank N - 1) := by
    have k1 : size C ≤ 2 ^ size C := Nat.lt_two_pow_self.le
    have k2 : 1 ≤ 2 ^ B₁ := Nat.one_le_two_pow
    have k3 : 2 ^ (m + 1) + (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) ≤
        size C * (2 ^ (m + 1) * 2 ^ B₁) := by
      have k4 : 2 ^ (m + 1) ≤ 2 ^ (m + 1) * 2 ^ B₁ := Nat.le_mul_of_pos_right _ (by omega)
      have k5 : size C * (2 ^ (m + 1) * 2 ^ B₁) =
          (size C - 1) * (2 ^ (m + 1) * 2 ^ B₁) + 2 ^ (m + 1) * 2 ^ B₁ := by
        have k6 : size C = (size C - 1) + 1 := by omega
        rw [k6, Nat.add_mul, one_mul, Nat.add_sub_cancel]
      omega
    have k7 : size C * (2 ^ (m + 1) * 2 ^ B₁) ≤ 2 ^ size C * (2 ^ (m + 1) * 2 ^ B₁) :=
      Nat.mul_le_mul_right _ k1
    have k8 : 2 ^ size C * (2 ^ (m + 1) * 2 ^ B₁) = 2 ^ (size C + (m + 1 + B₁)) := by
      rw [pow_add 2 (size C), pow_add 2 (m + 1) B₁]
    have k9 : 2 ^ (size C + (m + 1 + B₁)) ≤ 2 ^ (networkRank N - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact short_cycle_arith (pow_succ' 2 m) rfl hE hb hcount h4 h5' hX

end Erdos1016.BoundaryTrace.Network

/-! ### Theorem 7.1 for multigraphs -/

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance shortCycleBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- **Theorem 7.1 of the paper (Case 4 of the proof of Theorem 1.1)**, from Corollary 5.6 for the
pole alone. For every `D`, a connected cubic multigraph of large rank `r`, without a loop,
without a cyclic cut of size at most four and with a cycle of length less than `D`, has fewer
than `2^(r-1)` cycles. -/
theorem shortCycleStatement_of_shore (hshore : CyclicShoreStatement) : ShortCycleStatement := by
  intro D₀
  obtain ⟨B₁, hB₁⟩ := hshore (D₀ + 2) (12 * D₀)
  obtain ⟨B₂, hB₂⟩ := numCycles_le_of_large_rank_margin (D₀ + 2)
  refine ⟨D₀ + (D₀ + 2) + B₁ + B₂ + 12, ?_⟩
  rintro M hconn hcubic hloop hR hno4 ⟨x, hx, hlen⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  have hrank : D₀ + (D₀ + 2) + B₁ + B₂ + 12 ≤ networkRank M.looplessNetwork := by
    rw [← M.cycleRank_eq_networkRank hl]
    exact hR
  -- the cut edges of a vertex set are the crossing edges
  have hcutcard : ∀ W : Finset M.Vertex,
      (M.cutEdges W).card = M.looplessNetwork.cutSize (fun v => v ∈ W) := by
    intro W
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges W} = (M.cutEdges W).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ W) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} := rfl
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} →
        {e : M.Edge // e ∈ M.cutEdges W}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses W e.1).2 e.2⟩, fun _ => rfl⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
        exact Subtype.ext (Subtype.ext h1)
      · intro b
        refine ⟨⟨⟨b.1, hl b.1⟩, (M.mem_cutEdges_iff_crosses W ⟨b.1, hl b.1⟩).1 b.2⟩, ?_⟩
        apply Subtype.ext
        rw [hf]
    have h1 := Nat.card_eq_of_bijective f hbij
    omega
  -- every cyclic cut of the network has at least five crossing edges
  have hcut : ∀ S : M.Vertex → Prop, M.looplessNetwork.IsCyclicCut S →
      5 ≤ M.looplessNetwork.cutSize S := by
    intro S hS
    obtain ⟨W, hW⟩ : ∃ W : Finset M.Vertex, (fun v => v ∈ W) = S :=
      ⟨Finset.univ.filter S, funext fun v => propext (by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩)⟩
    subst hW
    refine Nat.le_of_not_lt fun hlt => ?_
    apply hno4
    refine ⟨W, ⟨?_, ?_⟩, ?_⟩
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl W).2 ⟨z, hz, hw⟩
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl Wᶜ).2 ⟨z, hz, fun g hg =>
        ⟨Finset.mem_compl.2 (hw g hg).1, Finset.mem_compl.2 (hw g hg).2⟩⟩
    · rw [hcutcard W]
      omega
  -- the short cycle of the multigraph is a short cycle of the network
  have hy : M.looplessNetwork.IsCycleWord (M.nonloopWord x) :=
    (M.isCycleWord_iff_looplessNetwork x (hl.word x)).1 hx
  have hysize : size (M.nonloopWord x) ≤ M.wordLength x := by
    unfold size FiniteMultiGraph.wordLength
    apply Finset.card_le_card_of_injOn (fun g : M.NonloopEdge => g.1)
    · intro g hg
      exact Finset.mem_filter.2 ⟨Finset.mem_univ g.1, (Finset.mem_filter.1 hg).2⟩
    · intro g _ g' _ hgg
      exact Subtype.ext hgg
  -- a shortest cycle of the network
  have hex : ∃ n, ∃ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z ∧ size z = n :=
    ⟨_, M.nonloopWord x, hy, rfl⟩
  obtain ⟨C, hC, hCsize⟩ := Nat.find_spec hex
  have hmin : ∀ z : M.looplessNetwork.Word, M.looplessNetwork.IsCycleWord z →
      size C ≤ size z := by
    intro z hz
    rw [hCsize]
    exact Nat.find_min' hex ⟨z, hz, rfl⟩
  have hCD : size C < D₀ := lt_of_le_of_lt (hmin _ hy) (lt_of_le_of_lt hysize hlen)
  have h5 : 5 ≤ size C :=
    ExactMaximumSupport.NetworkShortCycleCut.four_lt_size_of_cyclic_cut_lower_bound
      M.looplessNetwork (fun v => le_of_eq (hcub v)) (by omega) hcut C hC
  have h := numCycles_lt_of_short_cycle hB₁ hB₂ M.looplessNetwork hN hcub hcut C hC hmin h5
    (by omega) (by omega) (by omega)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h

end Erdos1016.ExactMaximum

import Erdos1016.ExactMaximum.SmallCutCase
import Erdos1016.ExactMaximum.NetCutRank
import Erdos1016.ExactMaximum.NetJoin

set_option autoImplicit false

/-!
# The structure of a smallest cyclic cut of size four

Let `N` be a connected cubic network in which every cyclic cut has at least four crossing edges,
and let `S` be a cyclic cut with exactly four crossing edges. This file proves the first
paragraph of the proof of Theorem 6.8 of the paper "The maximum number of cycles in a graph of
large rank":

* the two sides are connected (`reachable_inside_of_four`);
* no vertex is on two crossing edges (`false_of_two_crossing_at_four`);
* so the two sides are poles, the ends of the four crossing edges are four different ports on
  each side, and `r + 1 = h + k + 4` for the ranks (`exists_isFourCut`);
* a side of rank one has no other vertices than its four ports (`exists_eq_of_rank_one`).

The lemmas of `NetSmallCut.lean` and `Poles.lean` are for cuts of size at most three. There every
cut with at most two crossing edges is cyclic, and this is all that the proofs use. For size four
the two facts need one more step. A side that is not connected has a part with at most two
crossing edges. A vertex on two crossing edges can leave its side: the cut that remains has at
most three crossing edges, and a cycle on each side.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance fourCutStructureDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### The sides are connected -/

omit [Fintype V] in
/-- **Two parts of a side.** Let `u ∈ S` be not joined to `s₀ ∈ S` by edges inside `S`. Then `S`
has a part `C` with `s₀` and a part `D` with `u` and without `s₀`, and the cuts `C` and `D` have
together at most as many crossing edges as the cut `S`. -/
theorem exists_parts_of_not_reachable (N : Network V E) (S : V → Prop) {s₀ u : V} (hs₀ : S s₀)
    (hu : S u) (hnot : ¬ (N.sub (N.inside S)).graph.Reachable s₀ u) :
    ∃ C D : V → Prop, C s₀ ∧ (∀ v, C v → S v) ∧ D u ∧ ¬ D s₀ ∧
      N.cutSize C + N.cutSize D ≤ N.cutSize S := by
  obtain ⟨C, hC⟩ : ∃ C : V → Prop,
      ∀ v, C v ↔ (S v ∧ (N.sub (N.inside S)).graph.Reachable s₀ v) := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : V → Prop,
      ∀ v, D v ↔ (S v ∧ ¬ (N.sub (N.inside S)).graph.Reachable s₀ v) := ⟨_, fun _ => Iff.rfl⟩
  have hCs : C s₀ := (hC s₀).2 ⟨hs₀, SimpleGraph.Reachable.refl _⟩
  have hDu : D u := (hD u).2 ⟨hu, hnot⟩
  have hDs : ¬ D s₀ := fun h => ((hD s₀).1 h).2 (SimpleGraph.Reachable.refl _)
  -- an edge inside `S` joins two vertices of the same part
  have hin : ∀ e, N.inside S e → ((N.sub (N.inside S)).graph.Reachable s₀ (N.src e) ↔
      (N.sub (N.inside S)).graph.Reachable s₀ (N.dst e)) := by
    intro e he
    have hadj : (N.sub (N.inside S)).graph.Adj (N.src e) (N.dst e) :=
      ⟨⟨e, he⟩, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  -- a crossing edge of a part is a crossing edge of `S`
  have hCS : ∀ e, N.crosses C e → N.crosses S e := by
    intro e he
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · exfalso
      apply he
      rw [hC, hC]
      exact ⟨fun k => ⟨h.2, (hin e h).1 k.2⟩, fun k => ⟨h.1, (hin e h).2 k.2⟩⟩
    · exfalso
      apply he
      rw [hC, hC]
      exact ⟨fun k => absurd k.1 h.1, fun k => absurd k.1 h.2⟩
    · exact h
  have hDS : ∀ e, N.crosses D e → N.crosses S e := by
    intro e he
    rcases N.inside_or_outside_or_crosses S e with h | h | h
    · exfalso
      apply he
      rw [hD, hD]
      exact ⟨fun k => ⟨h.2, fun k' => k.2 ((hin e h).2 k')⟩,
        fun k => ⟨h.1, fun k' => k.2 ((hin e h).1 k')⟩⟩
    · exfalso
      apply he
      rw [hD, hD]
      exact ⟨fun k => absurd k.1 h.1, fun k => absurd k.1 h.2⟩
    · exact h
  -- no edge crosses both parts
  have hCD : ∀ e, N.crosses C e → N.crosses D e → False := by
    intro e heC heD
    have hS' := hCS e heC
    by_cases k1 : S (N.src e)
    · have k2 : ¬ S (N.dst e) := fun k2 => hS' ⟨fun _ => k2, fun _ => k1⟩
      have c2 : ¬ C (N.dst e) := fun h => k2 ((hC _).1 h).1
      have d2 : ¬ D (N.dst e) := fun h => k2 ((hD _).1 h).1
      have c1 : C (N.src e) := Classical.not_not.1 fun h =>
        heC ⟨fun k => absurd k h, fun k => absurd k c2⟩
      have d1 : D (N.src e) := Classical.not_not.1 fun h =>
        heD ⟨fun k => absurd k h, fun k => absurd k d2⟩
      exact ((hD _).1 d1).2 ((hC _).1 c1).2
    · have c1 : ¬ C (N.src e) := fun h => k1 ((hC _).1 h).1
      have d1 : ¬ D (N.src e) := fun h => k1 ((hD _).1 h).1
      have c2 : C (N.dst e) := Classical.not_not.1 fun h =>
        heC ⟨fun k => absurd k c1, fun k => absurd k h⟩
      have d2 : D (N.dst e) := Classical.not_not.1 fun h =>
        heD ⟨fun k => absurd k d1, fun k => absurd k h⟩
      exact ((hD _).1 d2).2 ((hC _).1 c2).2
  have h3 := natCard_add_le_of_imp (fun e : E => N.crosses C e) (fun e => N.crosses D e)
    (fun e => N.crosses S e) hCS hDS hCD
  exact ⟨C, D, hCs, fun v hv => ((hC v).1 hv).1, hDu, hDs, h3⟩

/-- **A side of a smallest cyclic cut of size four is connected.** In a cubic network, let every
cyclic cut have at least four crossing edges, and let the cut `S` have exactly four. Then every
vertex of `S` is joined to `s₀ ∈ S` by edges inside `S`. -/
theorem reachable_inside_of_four (N : Network V E) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 4) {s₀ t₀ : V} (hs₀ : S s₀) (ht₀ : ¬ S t₀) :
    ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u := by
  intro u hu
  refine Classical.not_not.1 fun hnot => ?_
  obtain ⟨C, D, hCs, hCS, hDu, hDs, hle⟩ := N.exists_parts_of_not_reachable S hs₀ hu hnot
  have hCt : ¬ C t₀ := fun h => ht₀ (hCS t₀ h)
  by_cases hC2 : N.cutSize C ≤ 2
  · have := hmin C (N.isCyclicCut_of_cutSize_le_two hcubic C hCs hCt hC2)
    omega
  · have hD2 : N.cutSize D ≤ 2 := by omega
    have := hmin D (N.isCyclicCut_of_cutSize_le_two hcubic D hDu hDs hD2)
    omega

/-! ### No vertex is on two crossing edges -/

omit [Fintype V] in
/-- A vertex of a cubic network is not on four different edges. -/
theorem false_of_four_edges_at (N : Network V E) (hcubic : N.IsCubic) {v : V} {e f g g' : E}
    (hef : e ≠ f) (heg : e ≠ g) (heg' : e ≠ g') (hfg : f ≠ g) (hfg' : f ≠ g') (hgg' : g ≠ g')
    (he : N.src e = v ∨ N.dst e = v) (hf : N.src f = v ∨ N.dst f = v)
    (hg : N.src g = v ∨ N.dst g = v) (hg' : N.src g' = v ∨ N.dst g' = v) : False := by
  have hsub : ({e, f, g, g'} : Finset E) ⊆ Finset.univ.filter
      (fun k : E => (fun _ => (1 : Bit)) k ≠ 0 ∧ (N.src k = v ∨ N.dst k = v)) := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hk
    refine Finset.mem_filter.2 ⟨Finset.mem_univ k, one_ne_zero, ?_⟩
    rcases hk with hk | hk | hk | hk
    · rw [hk]
      exact he
    · rw [hk]
      exact hf
    · rw [hk]
      exact hg
    · rw [hk]
      exact hg'
  have hcard : ({e, f, g, g'} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
      Finset.card_insert_of_not_mem, Finset.card_singleton]
    · rw [Finset.mem_singleton]
      exact hgg'
    · rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hfg h
      · exact hfg' h
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact hef h
      · exact heg h
      · exact heg' h
  have hle := Finset.card_le_card hsub
  have hdeg : (Finset.univ.filter
      (fun k : E => (fun _ => (1 : Bit)) k ≠ 0 ∧ (N.src k = v ∨ N.dst k = v))).card = 3 :=
    hcubic v
  omega

omit [Fintype V] in
/-- **Removing a vertex with two crossing edges.** In a cubic network, let two different
crossing edges of the cut `S` have the end `v` in `S`, and let `S'` be `S` without `v`. Then the
cut `S'` has fewer crossing edges than the cut `S`. -/
theorem cutSize_remove_lt (N : Network V E) (hcubic : N.IsCubic) (S S' : V → Prop) {v : V}
    (hS' : ∀ u, S' u ↔ (S u ∧ u ≠ v)) {e f : E} {w₁ w₂ : V} (hef : e ≠ f)
    (he : N.Joins e v w₁) (hf : N.Joins f v w₂) (hv : S v) (hw₁ : ¬ S w₁) (hw₂ : ¬ S w₂) :
    N.cutSize S' + 1 ≤ N.cutSize S := by
  have hce : N.crosses S e := N.crosses_of_joins he hv hw₁
  have hcf : N.crosses S f := N.crosses_of_joins hf hv hw₂
  -- an edge that is not at `v` crosses both cuts or none
  have hnot_at : ∀ g, ¬ (N.src g = v ∨ N.dst g = v) → (N.crosses S' g ↔ N.crosses S g) := by
    intro g hg
    have k1 : N.src g ≠ v := fun h => hg (Or.inl h)
    have k2 : N.dst g ≠ v := fun h => hg (Or.inr h)
    have e1 : S' (N.src g) ↔ S (N.src g) := by
      rw [hS']
      exact ⟨fun h => h.1, fun h => ⟨h, k1⟩⟩
    have e2 : S' (N.dst g) ↔ S (N.dst g) := by
      rw [hS']
      exact ⟨fun h => h.1, fun h => ⟨h, k2⟩⟩
    unfold crosses
    rw [e1, e2]
  -- an edge at `v` that crosses the new cut is inside `S`
  have hat : ∀ g, (N.src g = v ∨ N.dst g = v) → N.crosses S' g → N.inside S g := by
    intro g hg hc
    have hv' : ¬ S' v := fun h => ((hS' v).1 h).2 rfl
    rcases hg with hg | hg
    · have k : S' (N.dst g) := Classical.not_not.1 fun k =>
        hc ⟨fun h => absurd (hg ▸ h) hv', fun h => absurd h k⟩
      exact ⟨hg ▸ hv, ((hS' _).1 k).1⟩
    · have k : S' (N.src g) := Classical.not_not.1 fun k =>
        hc ⟨fun h => absurd h k, fun h => absurd (hg ▸ h) hv'⟩
      exact ⟨((hS' _).1 k).1, hg ▸ hv⟩
  -- the injective map
  obtain ⟨φ, hφ⟩ : ∃ φ : {g : E // N.crosses S' g} → {g : E // N.crosses S g ∧ g ≠ f},
      ∀ g, (φ g).1 = if (N.src g.1 = v ∨ N.dst g.1 = v) then e else g.1 := by
    refine ⟨fun g => ⟨if (N.src g.1 = v ∨ N.dst g.1 = v) then e else g.1, ?_⟩, fun _ => rfl⟩
    by_cases hg : N.src g.1 = v ∨ N.dst g.1 = v
    · rw [if_pos hg]
      exact ⟨hce, hef⟩
    · rw [if_neg hg]
      exact ⟨(hnot_at g.1 hg).1 g.2, fun h => hg (h ▸ hf.at_left)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg Subtype.val hab
    rw [hφ, hφ] at h
    by_cases ha : N.src a.1 = v ∨ N.dst a.1 = v <;> by_cases hb : N.src b.1 = v ∨ N.dst b.1 = v
    · -- both edges are inside `S` and at `v`
      refine Classical.not_not.1 fun hne => ?_
      have hne' : a.1 ≠ b.1 := fun h' => hne (Subtype.ext h')
      have ia := hat a.1 ha a.2
      have ib := hat b.1 hb b.2
      exact N.false_of_four_edges_at hcubic hef
        (fun h' => N.not_inside_of_crosses hce (by rw [h']; exact ia))
        (fun h' => N.not_inside_of_crosses hce (by rw [h']; exact ib))
        (fun h' => N.not_inside_of_crosses hcf (by rw [h']; exact ia))
        (fun h' => N.not_inside_of_crosses hcf (by rw [h']; exact ib))
        hne' he.at_left hf.at_left ha hb
    · rw [if_pos ha, if_neg hb] at h
      exact absurd (h ▸ he.at_left) hb
    · rw [if_neg ha, if_pos hb] at h
      exact absurd (h.symm ▸ he.at_left) ha
    · rw [if_neg ha, if_neg hb] at h
      exact Subtype.ext h
  have h2 := Nat.card_le_card_of_injective φ hinj
  have h3 := natCard_add_le_of_imp (fun g : E => N.crosses S g ∧ g ≠ f) (fun g => g = f)
    (fun g => N.crosses S g) (fun g h => h.1) (fun g h => h ▸ hcf) (fun g h h' => h.2 h')
  have h4 : Nat.card {g : E // g = f} = 1 := Nat.card_unique
  have h5 : N.cutSize S' ≤ Nat.card {g : E // N.crosses S g ∧ g ≠ f} := h2
  have h6 : Nat.card {g : E // N.crosses S g ∧ g ≠ f} + Nat.card {g : E // g = f} ≤
      N.cutSize S := h3
  omega

/-- The complement of a cyclic cut is a cyclic cut. -/
theorem IsCyclicCut.not {N : Network V E} {S : V → Prop} (h : N.IsCyclicCut S) :
    N.IsCyclicCut (fun v => ¬ S v) := by
  refine ⟨h.2, ?_⟩
  have h1 := h.1
  rw [numCycles_sub] at h1
  obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.1 h1
  exact Erdos1016.ExactMaximum.numCycles_sub_pos N _ hx
    (fun g hg => ⟨fun k => k (hw g hg).1, fun k => k (hw g hg).2⟩)

/-- **No vertex is on two edges of a smallest cyclic cut of size four.** In a cubic network, let
every cyclic cut have at least four crossing edges, and let the cyclic cut `S` have exactly four.
Then two different crossing edges do not have the same end in `S`. -/
theorem false_of_two_crossing_at_four (N : Network V E) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 4) (hcyc : N.IsCyclicCut S) {e f : E} {v w₁ w₂ : V} (hef : e ≠ f)
    (he : N.Joins e v w₁) (hf : N.Joins f v w₂) (hv : S v) (hw₁ : ¬ S w₁) (hw₂ : ¬ S w₂) :
    False := by
  obtain ⟨S', hS'⟩ : ∃ S' : V → Prop, ∀ u, S' u ↔ (S u ∧ u ≠ v) := ⟨_, fun _ => Iff.rfl⟩
  have h1 := N.cutSize_remove_lt hcubic S S' hS' hef he hf hv hw₁ hw₂
  have hce : N.crosses S e := N.crosses_of_joins he hv hw₁
  have hcf : N.crosses S f := N.crosses_of_joins hf hv hw₂
  -- the cut without `v` is cyclic
  have hcyc' : N.IsCyclicCut S' := by
    constructor
    · -- a cycle of the first side does not pass through `v`
      have h := hcyc.1
      rw [numCycles_sub] at h
      obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.1 h
      have hdeg0 : N.deg x v = 0 := by
        rcases hx.2.1 v with h0 | h2
        · exact h0
        · exfalso
          have h2' : 1 < (Finset.univ.filter fun g : E =>
              x g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card := by
            have h3 : N.deg x v = (Finset.univ.filter fun g : E =>
                x g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card := rfl
            omega
          obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2'
          have ha := (Finset.mem_filter.1 ha).2
          have hb := (Finset.mem_filter.1 hb).2
          have ia := hw a ha.1
          have ib := hw b hb.1
          exact N.false_of_four_edges_at hcubic hef
            (fun h' => N.not_inside_of_crosses hce (by rw [h']; exact ia))
            (fun h' => N.not_inside_of_crosses hce (by rw [h']; exact ib))
            (fun h' => N.not_inside_of_crosses hcf (by rw [h']; exact ia))
            (fun h' => N.not_inside_of_crosses hcf (by rw [h']; exact ib))
            hab he.at_left hf.at_left ha.2 hb.2
      apply Erdos1016.ExactMaximum.numCycles_sub_pos N (N.inside S') hx
      intro g hg
      have hin := hw g hg
      exact ⟨(hS' _).2 ⟨hin.1, fun h' => hg (N.eq_zero_of_deg_eq_zero hdeg0 (Or.inl h'))⟩,
        (hS' _).2 ⟨hin.2, fun h' => hg (N.eq_zero_of_deg_eq_zero hdeg0 (Or.inr h'))⟩⟩
    · have h := hcyc.2
      rw [numCycles_sub] at h
      obtain ⟨⟨x, hx, hw⟩⟩ := Finite.card_pos_iff.1 h
      apply Erdos1016.ExactMaximum.numCycles_sub_pos N (N.outside S') hx
      intro g hg
      have hout := hw g hg
      exact ⟨fun h' => hout.1 ((hS' _).1 h').1, fun h' => hout.2 ((hS' _).1 h').1⟩
  have h2 := hmin S' hcyc'
  omega

/-! ### The sides are poles -/

/-- No vertex of `S` is on two crossing edges of the cut `S`. -/
def NoDoubleEnd (N : Network V E) (S : V → Prop) : Prop :=
  ∀ (e f : E) (v w₁ w₂ : V), e ≠ f → N.Joins e v w₁ → N.Joins f v w₂ → S v → ¬ S w₁ → ¬ S w₂ →
    False

omit [Fintype V] in
/-- If no vertex of `S` is on two crossing edges, then every vertex of `S` is on at most one. -/
theorem crossDeg_le_one_of (N : Network V E) (S : V → Prop) (hno : N.NoDoubleEnd S) {v : V}
    (hv : S v) : N.deg (restrict (fun _ => 1) (N.crosses S)) v ≤ 1 := by
  refine Nat.le_of_not_lt fun h1 => ?_
  have h1' : 1 < (Finset.univ.filter fun g : E =>
      restrict (fun _ => (1 : Bit)) (N.crosses S) g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)).card :=
    h1
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h1'
  have ha := (Finset.mem_filter.1 ha).2
  have hb := (Finset.mem_filter.1 hb).2
  have hca : N.crosses S a := ((restrict_ne_zero_iff _ _ a).1 ha.1).1
  have hcb : N.crosses S b := ((restrict_ne_zero_iff _ _ b).1 hb.1).1
  obtain ⟨wa, hwa⟩ := N.exists_joins ha.2
  obtain ⟨wb, hwb⟩ := N.exists_joins hb.2
  -- the other end of a crossing edge at `v` is not in `S`
  have hother : ∀ (g : E) (w : V), N.crosses S g → N.Joins g v w → ¬ S w := by
    intro g w hc hj hw
    apply hc
    rcases hj with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [k1, k2]
      exact ⟨fun _ => hw, fun _ => hv⟩
    · rw [k1, k2]
      exact ⟨fun _ => hv, fun _ => hw⟩
  exact hno a b v wa wb hab hwa hwb hv (hother a wa hca hwa) (hother b wb hcb hwb)

omit [Fintype V] in
/-- **A connected side without a vertex on two crossing edges is a pole.** In a cubic network,
let no vertex of `S` be on two crossing edges, and let every vertex of `S` be joined to `s₀` by
edges inside `S`. Then the first side is a pole, possibly with isolated vertices. -/
theorem isWeakPole_inside_of (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop)
    (hno : N.NoDoubleEnd S) {s₀ : V}
    (hreach : ∀ u, S u → (N.sub (N.inside S)).graph.Reachable s₀ u) :
    (N.sub (N.inside S)).IsWeakPole := by
  have hzero : ∀ v, ¬ S v → (N.sub (N.inside S)).deg (fun _ => 1) v = 0 := by
    intro v hv
    rw [N.deg_sub_ones (N.inside S) v]
    exact N.deg_inside_eq_zero S hv
  constructor
  · intro v
    by_cases hv : S v
    · have h1 := N.deg_inside_add hcubic S hv
      have h2 := N.crossDeg_le_one_of S hno hv
      omega
    · exact Or.inl (hzero v hv)
  · intro u v hu hv
    have hSu : S u := Classical.not_not.1 fun h => by
      have := hzero u h
      omega
    have hSv : S v := Classical.not_not.1 fun h => by
      have := hzero v h
      omega
    exact (hreach u hSu).symm.trans (hreach v hSv)

omit [Fintype V] in
/-- **The ends of the crossing edges are ports.** In a cubic network, let no vertex of `S` be on
two crossing edges, and let the edge `e` join `s ∈ S` and `t ∉ S`. Then `s` has degree two in the
first side. -/
theorem isPort_inside_of (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop)
    (hno : N.NoDoubleEnd S) {e : E} {s t : V} (he : N.Joins e s t) (hs : S s) (ht : ¬ S t) :
    (N.sub (N.inside S)).IsPort s := by
  have h1 := N.deg_inside_add hcubic S hs
  have h2 := N.crossDeg_le_one_of S hno hs
  have h3 : 0 < N.deg (restrict (fun _ => 1) (N.crosses S)) s := by
    have hne : restrict (fun _ => (1 : Bit)) (N.crosses S) e ≠ 0 := by
      rw [restrict_apply_of_pos _ (N.crosses_of_joins he hs ht)]
      exact one_ne_zero
    rcases he.at_left with h | h
    · rw [← h]
      exact N.deg_src_pos hne
    · rw [← h]
      exact N.deg_dst_pos hne
  unfold IsPort
  omega

/-! ### The four crossing edges -/

/-- **A cut of size four with its ends.** The edges `e 0, …, e 3` are all crossing edges of the
cut `S`. The edge `e i` joins `x i ∈ S` and `y i ∉ S`. The four vertices `x i` are different, and
so are the four vertices `y i`. The two sides are poles, in which the `x i` and the `y i` are
ports. The ranks satisfy `r + 1 = h + k + 4`. -/
structure IsFourCut (N : Network V E) (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V) :
    Prop where
  crosses : ∀ g, N.crosses S g → ∃ i, g = e i
  joins : ∀ i, N.Joins (e i) (x i) (y i)
  mem : ∀ i, S (x i)
  not_mem : ∀ i, ¬ S (y i)
  inj_x : Function.Injective x
  inj_y : Function.Injective y
  pole_in : (N.sub (N.inside S)).IsWeakPole
  pole_out : (N.sub (N.outside S)).IsWeakPole
  port_in : ∀ i, (N.sub (N.inside S)).IsPort (x i)
  port_out : ∀ i, (N.sub (N.outside S)).IsPort (y i)
  rank : networkRank N + 1 =
    networkRank (N.sub (N.inside S)) + networkRank (N.sub (N.outside S)) + 4

/-- **The structure of a smallest cyclic cut of size four.** Let `N` be a connected cubic network
in which every cyclic cut has at least four crossing edges, and let the cyclic cut `S` have
exactly four. Then the crossing edges and their ends are as in `IsFourCut`. -/
theorem exists_isFourCut (N : Network V E) (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop, N.IsCyclicCut S → 4 ≤ N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S = 4) (hcyc : N.IsCyclicCut S) :
    ∃ (e : Fin 4 → E) (x y : Fin 4 → V), N.IsFourCut S e x y := by
  have hS' : N.cutSize (fun v => ¬ S v) = 4 := by
    rw [N.cutSize_not S]
    exact hS
  have hno : N.NoDoubleEnd S := fun e f v w₁ w₂ hef he hf hv h1 h2 =>
    N.false_of_two_crossing_at_four hcubic hmin S hS hcyc hef he hf hv h1 h2
  have hno' : N.NoDoubleEnd (fun v => ¬ S v) := fun e f v w₁ w₂ hef he hf hv h1 h2 =>
    N.false_of_two_crossing_at_four hcubic hmin (fun v => ¬ S v) hS' hcyc.not hef he hf hv h1 h2
  -- the four crossing edges
  have hcard : Nat.card {g : E // N.crosses S g} = 4 := hS
  have φ := Finite.equivFinOfCardEq hcard
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → E, ∀ i, e i = (φ.symm i).1 := ⟨_, fun _ => rfl⟩
  have hecross : ∀ i, N.crosses S (e i) := by
    intro i
    rw [he i]
    exact (φ.symm i).2
  have hall : ∀ g, N.crosses S g → ∃ i, g = e i := by
    intro g hg
    refine ⟨φ ⟨g, hg⟩, ?_⟩
    rw [he, Equiv.symm_apply_apply]
  have heinj : Function.Injective e := by
    intro i j hij
    rw [he i, he j] at hij
    exact φ.symm.injective (Subtype.ext hij)
  have hends : ∀ i, ∃ s t, N.Joins (e i) s t ∧ S s ∧ ¬ S t := fun i =>
    Erdos1016.ExactMaximum.exists_joins_of_crosses N (hecross i)
  choose x y hjoin hx hy using hends
  have hxinj : Function.Injective x := by
    intro i j hij
    refine Classical.not_not.1 fun hne => ?_
    have hj := hjoin j
    rw [← hij] at hj
    exact hno (e i) (e j) (x i) (y i) (y j) (fun h => hne (heinj h)) (hjoin i) hj (hx i) (hy i)
      (hy j)
  have hyinj : Function.Injective y := by
    intro i j hij
    refine Classical.not_not.1 fun hne => ?_
    have hj := (hjoin j).symm
    rw [← hij] at hj
    exact hno' (e i) (e j) (y i) (x i) (x j) (fun h => hne (heinj h)) (hjoin i).symm hj (hy i)
      (fun h => h (hx i)) (fun h => h (hx j))
  -- the two sides are connected
  have hin := N.reachable_inside_of_four hcubic hmin S hS (hx 0) (hy 0)
  have hout : ∀ u, ¬ S u → (N.sub (N.outside S)).graph.Reachable (y 0) u :=
    N.reachable_inside_of_four hcubic hmin (fun v => ¬ S v) hS' (hy 0) (fun h => h (hx 0))
  have hrank := N.networkRank_add_one_of_cut S (hx 0) (hy 0) hN hin hout
  rw [hcard] at hrank
  exact ⟨e, x, y, hall, hjoin, hx, hy, hxinj, hyinj, N.isWeakPole_inside_of hcubic S hno hin,
    N.isWeakPole_inside_of hcubic (fun v => ¬ S v) hno' hout,
    fun i => N.isPort_inside_of hcubic S hno (hjoin i) (hx i) (hy i),
    fun i => N.isPort_inside_of hcubic (fun v => ¬ S v) hno' (hjoin i).symm (hy i)
      (fun h => h (hx i)), hrank⟩

/-! ### A side of rank one -/

/-- **A side of rank one.** In a cubic network, let the cut `S` have four crossing edges, and
let `x 0, …, x 3` be four different vertices of `S`. If the first side has rank one, then `S` has
no other vertices. -/
theorem exists_eq_of_rank_one (N : Network V E) (hcubic : N.IsCubic) (S : V → Prop)
    (hS : N.cutSize S = 4) (x : Fin 4 → V) (hx : ∀ i, S (x i)) (hinj : Function.Injective x)
    (h1 : networkRank (N.sub (N.inside S)) = 1) : ∀ v, S v → ∃ i, v = x i := by
  have e1 := N.three_mul_card_eq hcubic S
  have e2 := N.rank_side_ge S (hx 0)
  have hcard : Nat.card {v : V // S v} ≤ 4 := by omega
  obtain ⟨f, hf⟩ : ∃ f : Fin 4 → {v : V // S v}, ∀ i, (f i).1 = x i :=
    ⟨fun i => ⟨x i, hx i⟩, fun _ => rfl⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hinj
    rw [← hf i, ← hf j, hij]
  have hbij := hfinj.bijective_of_nat_card_le
    (by rw [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]; exact hcard)
  intro v hv
  obtain ⟨i, hi⟩ := hbij.2 ⟨v, hv⟩
  exact ⟨i, by rw [← hf i, hi]⟩

end Erdos1016.BoundaryTrace.Network

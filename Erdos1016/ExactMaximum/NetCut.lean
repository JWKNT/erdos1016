import Erdos1016.ExactMaximum.NetTransfer

set_option autoImplicit false

/-!
# Cycles across a cut

Let `S` be a set of vertices of a network `N`. An edge is inside (both ends in `S`), outside (no
end in `S`), or it crosses (exactly one end in `S`). The two sides of the cut are the networks
`N.sub (N.inside S)` and `N.sub (N.outside S)`.

This file proves the statements about cuts that Section 6 of the paper "The maximum number of
cycles in a graph of large rank" uses for cuts of size at most three:

* an even word has an even number of crossing edges (`even_card_crossSet`);
* a cycle without a crossing edge is a cycle of one side (`numCyclesAcross_empty`);
* the cycles whose crossing edges are exactly `e` and `f` are the sums of `e`, `f`, a path of the
  first side between the ends of `e` and `f` in `S`, and a path of the second side between the
  other ends (`numCyclesAcross_pair`);
* so, for a cut with one, two or three crossing edges, the number of cycles is given by the
  formulas `numCycles_of_one_crossing`, `numCycles_of_two_crossing` and
  `numCycles_of_three_crossing`. The last two are equation (6.1) of the paper.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Arithmetic in `Bit` and counting -/

theorem bit_eq_one_of_ne_zero {a : Bit} (h : a ≠ 0) : a = 1 := by
  rcases bit_cases a with h0 | h1
  · exact absurd h0 h
  · exact h1

theorem bit_eq_of_add_eq_zero {a b : Bit} (h : a + b = 0) : a = b := by
  rcases bit_cases a with ha | ha <;> rcases bit_cases b with hb | hb
  · rw [ha, hb]
  · rw [ha, hb] at h
    exact absurd h (by decide)
  · rw [ha, hb] at h
    exact absurd h (by decide)
  · rw [ha, hb]

/-- Two words with sum zero are equal. -/
theorem word_eq_of_add_eq_zero {ι : Type*} {a b : ι → Bit} (h : a + b = 0) : a = b := by
  funext i
  exact bit_eq_of_add_eq_zero (congrFun h i)

/-- The number of elements with a property, as the size of a finite set. -/
theorem natCard_subtype_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop) :
    Nat.card {a // P a} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Count the elements with a property by the value of a function. -/
theorem natCard_eq_sum_fibers {α β : Type*} [Fintype α] (P : α → Prop) (f : α → β)
    (t : Finset β) (h : ∀ a, P a → f a ∈ t) :
    Nat.card {a // P a} = ∑ b ∈ t, Nat.card {a // P a ∧ f a = b} := by
  rw [natCard_subtype_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := t)
      (fun a ha => h a (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2)]
  apply Finset.sum_congr rfl
  intro b _
  rw [natCard_subtype_eq_card_filter]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of elements with one of two properties that exclude each other. -/
theorem natCard_or_of_disjoint {α : Type*} [Finite α] (P Q : α → Prop)
    (h : ∀ a, P a → Q a → False) :
    Nat.card {a // P a ∨ Q a} = Nat.card {a // P a} + Nat.card {a // Q a} := by
  rw [← Nat.card_sum]
  symm
  let f : {a // P a} ⊕ {a // Q a} → {a // P a ∨ Q a} := fun z =>
    match z with
    | Sum.inl a => ⟨a.1, Or.inl a.2⟩
    | Sum.inr a => ⟨a.1, Or.inr a.2⟩
  apply Nat.card_eq_of_bijective f
  constructor
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have h' : (f (Sum.inl a)).1 = (f (Sum.inl b)).1 := congrArg Subtype.val hab
      exact congrArg Sum.inl (Subtype.ext h')
    · exfalso
      have h' : (f (Sum.inl a)).1 = (f (Sum.inr b)).1 := congrArg Subtype.val hab
      have h'' : a.1 = b.1 := h'
      exact h a.1 a.2 (by rw [h'']; exact b.2)
    · exfalso
      have h' : (f (Sum.inr a)).1 = (f (Sum.inl b)).1 := congrArg Subtype.val hab
      have h'' : a.1 = b.1 := h'
      exact h b.1 b.2 (by rw [← h'']; exact a.2)
    · have h' : (f (Sum.inr a)).1 = (f (Sum.inr b)).1 := congrArg Subtype.val hab
      exact congrArg Sum.inr (Subtype.ext h')
  · rintro ⟨a, ha | ha⟩
    · exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · exact ⟨Sum.inr ⟨a, ha⟩, rfl⟩

omit [Fintype E] in
/-- A sum over the subsets of a set with one element. -/
theorem sum_powerset_singleton {M : Type*} [AddCommMonoid M] (a : E) (F : Finset E → M) :
    ∑ A ∈ ({a} : Finset E).powerset, F A = F ∅ + F {a} := by
  rw [← insert_empty_eq a, Finset.sum_powerset_insert (Finset.not_mem_empty a),
    Finset.powerset_empty, Finset.sum_singleton, Finset.sum_singleton]

/-! ### The words of one or two edges -/

theorem unitPair_apply_left {e f : E} (hef : e ≠ f) : (unitWord e + unitWord f) e = 1 := by
  show unitWord e e + unitWord f e = 1
  rw [unitWord_apply, unitWord_apply, if_pos rfl, if_neg (Ne.symm hef), add_zero]

theorem unitPair_apply_right {e f : E} (hef : e ≠ f) : (unitWord e + unitWord f) f = 1 := by
  show unitWord e f + unitWord f f = 1
  rw [unitWord_apply, unitWord_apply, if_neg hef, if_pos rfl, zero_add]

theorem unitPair_apply_of_ne {e f g : E} (h1 : g ≠ e) (h2 : g ≠ f) :
    (unitWord e + unitWord f) g = 0 := by
  show unitWord e g + unitWord f g = 0
  rw [unitWord_apply, unitWord_apply, if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero]

/-! ### The three kinds of edges -/

/-- Both ends of the edge are in `S`. -/
def inside (N : Network V E) (S : V → Prop) (e : E) : Prop := S (N.src e) ∧ S (N.dst e)

/-- No end of the edge is in `S`. -/
def outside (N : Network V E) (S : V → Prop) (e : E) : Prop := ¬ S (N.src e) ∧ ¬ S (N.dst e)

/-- Exactly one end of the edge is in `S`. -/
def crosses (N : Network V E) (S : V → Prop) (e : E) : Prop := ¬ (S (N.src e) ↔ S (N.dst e))

omit [Fintype V] [Fintype E] in
theorem inside_or_outside_or_crosses (N : Network V E) (S : V → Prop) (e : E) :
    N.inside S e ∨ N.outside S e ∨ N.crosses S e := by
  unfold inside outside crosses
  by_cases h1 : S (N.src e) <;> by_cases h2 : S (N.dst e)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inr fun h => h2 (h.1 h1))
  · exact Or.inr (Or.inr fun h => h1 (h.2 h2))
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

omit [Fintype V] [Fintype E] in
theorem not_outside_of_inside (N : Network V E) {S : V → Prop} {e : E} (h : N.inside S e) :
    ¬ N.outside S e := fun h' => h'.1 h.1

omit [Fintype V] [Fintype E] in
theorem not_crosses_of_inside (N : Network V E) {S : V → Prop} {e : E} (h : N.inside S e) :
    ¬ N.crosses S e := fun h' => h' ⟨fun _ => h.2, fun _ => h.1⟩

omit [Fintype V] [Fintype E] in
theorem not_crosses_of_outside (N : Network V E) {S : V → Prop} {e : E} (h : N.outside S e) :
    ¬ N.crosses S e := fun h' => h' ⟨fun h1 => absurd h1 h.1, fun h2 => absurd h2 h.2⟩

omit [Fintype V] [Fintype E] in
theorem not_inside_of_outside (N : Network V E) {S : V → Prop} {e : E} (h : N.outside S e) :
    ¬ N.inside S e := fun h' => h.1 h'.1

omit [Fintype V] [Fintype E] in
theorem not_inside_of_crosses (N : Network V E) {S : V → Prop} {e : E} (h : N.crosses S e) :
    ¬ N.inside S e := fun h' => N.not_crosses_of_inside h' h

omit [Fintype V] [Fintype E] in
theorem not_outside_of_crosses (N : Network V E) {S : V → Prop} {e : E} (h : N.crosses S e) :
    ¬ N.outside S e := fun h' => N.not_crosses_of_outside h' h

omit [Fintype V] [Fintype E] in
/-- An edge that joins a vertex of `S` and a vertex outside `S` crosses. -/
theorem crosses_of_joins (N : Network V E) {S : V → Prop} {e : E} {s t : V} (h : N.Joins e s t)
    (hs : S s) (ht : ¬ S t) : N.crosses S e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · intro hiff
    rw [h1, h2] at hiff
    exact ht (hiff.1 hs)
  · intro hiff
    rw [h1, h2] at hiff
    exact ht (hiff.2 hs)

omit [Fintype V] [Fintype E] in
/-- Two edges that cross and have different ends in `S` are different. -/
theorem ne_of_joins (N : Network V E) {S : V → Prop} {e f : E} {s₁ s₂ t₁ t₂ : V}
    (he : N.Joins e s₁ t₁) (hs₁ : S s₁) (ht₁ : ¬ S t₁) (hf : N.Joins f s₂ t₂) (hs₂ : S s₂)
    (ht₂ : ¬ S t₂) (hs : s₁ ≠ s₂) : e ≠ f := by
  intro h
  rw [h] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hf with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact hs (h1.symm.trans h3)
  · have h5 : s₁ = t₂ := h1.symm.trans h3
    exact ht₂ (by rw [← h5]; exact hs₁)
  · have h5 : t₁ = s₂ := h1.symm.trans h3
    exact ht₁ (by rw [h5]; exact hs₂)
  · exact hs (h2.symm.trans h4)

/-! ### Parts of a word -/

omit [Fintype V] [Fintype E] in
theorem restrict_add (x y : E → Bit) (p : E → Prop) :
    restrict (x + y) p = restrict x p + restrict y p := by
  funext e
  show restrict (x + y) p e = restrict x p e + restrict y p e
  by_cases h : p e
  · rw [restrict_apply_of_pos _ h, restrict_apply_of_pos _ h, restrict_apply_of_pos _ h]
    rfl
  · rw [restrict_apply_of_neg _ h, restrict_apply_of_neg _ h, restrict_apply_of_neg _ h,
      add_zero]

omit [Fintype V] [Fintype E] in
/-- The part on `p` of a word within `p` is the word. -/
theorem restrict_eq_self {x : E → Bit} {p : E → Prop} (h : Within x p) : restrict x p = x := by
  funext e
  by_cases hp : p e
  · exact restrict_apply_of_pos x hp
  · rw [restrict_apply_of_neg x hp]
    exact (h.eq_zero hp).symm

omit [Fintype V] [Fintype E] in
/-- The part on `q` of a word within `p` is zero if `p` and `q` exclude each other. -/
theorem restrict_eq_zero {x : E → Bit} {p : E → Prop} (q : E → Prop) (h : Within x p)
    (hpq : ∀ e, p e → ¬ q e) : restrict x q = 0 := by
  funext e
  by_cases hq : q e
  · rw [restrict_apply_of_pos x hq]
    exact h.eq_zero (fun hp => hpq e hp hq)
  · exact restrict_apply_of_neg x hq

omit [Fintype V] [Fintype E] in
/-- A word is the sum of its parts on the three kinds of edges. -/
theorem restrict_add_restrict_add_restrict (N : Network V E) (S : V → Prop) (x : N.Word) :
    restrict x (N.inside S) + restrict x (N.outside S) + restrict x (N.crosses S) = x := by
  funext e
  show restrict x (N.inside S) e + restrict x (N.outside S) e + restrict x (N.crosses S) e = x e
  rcases N.inside_or_outside_or_crosses S e with h | h | h
  · rw [restrict_apply_of_pos x h, restrict_apply_of_neg x (N.not_outside_of_inside h),
      restrict_apply_of_neg x (N.not_crosses_of_inside h), add_zero, add_zero]
  · rw [restrict_apply_of_neg x (N.not_inside_of_outside h), restrict_apply_of_pos x h,
      restrict_apply_of_neg x (N.not_crosses_of_outside h), zero_add, add_zero]
  · rw [restrict_apply_of_neg x (N.not_inside_of_crosses h),
      restrict_apply_of_neg x (N.not_outside_of_crosses h), restrict_apply_of_pos x h, zero_add,
      zero_add]

/-- A word within the first side has zero boundary outside `S`. -/
theorem boundary_eq_zero_of_within_inside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.inside S)) {v : V} (hv : ¬ S v) : N.boundary x v = 0 := by
  rw [boundary_eq_deg, N.deg_eq_zero_of_forall]
  · exact Nat.cast_zero
  · intro e he
    refine h.eq_zero fun hin => ?_
    rcases he with he | he
    · exact hv (by rw [← he]; exact hin.1)
    · exact hv (by rw [← he]; exact hin.2)

/-- A word within the second side has zero boundary in `S`. -/
theorem boundary_eq_zero_of_within_outside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.outside S)) {v : V} (hv : S v) : N.boundary x v = 0 := by
  rw [boundary_eq_deg, N.deg_eq_zero_of_forall]
  · exact Nat.cast_zero
  · intro e he
    refine h.eq_zero fun hout => ?_
    rcases he with he | he
    · exact hout.1 (by rw [he]; exact hv)
    · exact hout.2 (by rw [he]; exact hv)

/-- Let `P` be within the first side and `Q` within the second side. If the sum of their
boundaries is `a + b`, where `a` is zero outside `S` and `b` is zero in `S`, then the boundary
of `P` is `a` and the boundary of `Q` is `b`. -/
theorem boundary_split (N : Network V E) {S : V → Prop} {P Q : N.Word} {a b : N.Demand}
    (hP : Within P (N.inside S)) (hQ : Within Q (N.outside S)) (ha : ∀ v, ¬ S v → a v = 0)
    (hb : ∀ v, S v → b v = 0) (h : N.boundary P + N.boundary Q = a + b) :
    N.boundary P = a ∧ N.boundary Q = b := by
  constructor
  · funext v
    have h1 : N.boundary P v + N.boundary Q v = a v + b v := congrFun h v
    by_cases hS : S v
    · rw [N.boundary_eq_zero_of_within_outside hQ hS, hb v hS, add_zero, add_zero] at h1
      exact h1
    · rw [N.boundary_eq_zero_of_within_inside hP hS, ha v hS]
  · funext v
    have h1 : N.boundary P v + N.boundary Q v = a v + b v := congrFun h v
    by_cases hS : S v
    · rw [N.boundary_eq_zero_of_within_outside hQ hS, hb v hS]
    · rw [N.boundary_eq_zero_of_within_inside hP hS, ha v hS, zero_add, zero_add] at h1
      exact h1

/-! ### The parity of the crossing edges -/

theorem sum_ite_eq_ite (S : V → Prop) (c : Bit) (u : V) :
    (∑ v, if S v then (if u = v then c else 0) else 0) = if S u then c else 0 := by
  rw [Finset.sum_eq_single u]
  · rw [if_pos rfl]
  · intro v _ hv
    rw [if_neg (Ne.symm hv)]
    exact ite_self 0
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- **Cut parity.** The sum of the boundary of `x` over the vertices of `S` is the sum of `x`
over the crossing edges. -/
theorem cut_parity (N : Network V E) (S : V → Prop) (x : N.Word) :
    (∑ v, if S v then N.boundary x v else 0) = ∑ e, if N.crosses S e then x e else 0 := by
  have h1 : ∀ v, (if S v then N.boundary x v else 0) =
      ∑ e, ((if S v then (if N.src e = v then x e else 0) else 0) +
        (if S v then (if N.dst e = v then x e else 0) else 0)) := by
    intro v
    by_cases hS : S v
    · simp only [if_pos hS]
      rw [boundary_apply, Finset.sum_add_distrib]
    · simp only [if_neg hS, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib, sum_ite_eq_ite S (x e) (N.src e),
    sum_ite_eq_ite S (x e) (N.dst e)]
  by_cases h1 : S (N.src e) <;> by_cases h2 : S (N.dst e)
  · have hc : ¬ N.crosses S e := fun h => h ⟨fun _ => h2, fun _ => h1⟩
    rw [if_pos h1, if_pos h2, if_neg hc]
    exact bit_add_self (x e)
  · have hc : N.crosses S e := fun h => h2 (h.1 h1)
    rw [if_pos h1, if_neg h2, if_pos hc, add_zero]
  · have hc : N.crosses S e := fun h => h1 (h.2 h2)
    rw [if_neg h1, if_pos h2, if_pos hc, zero_add]
  · have hc : ¬ N.crosses S e := fun h => h ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    rw [if_neg h1, if_neg h2, if_neg hc, add_zero]

/-- The crossing edges of the word `x`. -/
def crossSet (N : Network V E) (S : V → Prop) (x : N.Word) : Finset E :=
  Finset.univ.filter fun e => N.crosses S e ∧ x e ≠ 0

omit [Fintype V] in
theorem mem_crossSet (N : Network V E) {S : V → Prop} {x : N.Word} {e : E} :
    e ∈ N.crossSet S x ↔ N.crosses S e ∧ x e ≠ 0 := by
  unfold crossSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

omit [Fintype V] in
theorem cast_card_crossSet (N : Network V E) (S : V → Prop) (x : N.Word) :
    ((N.crossSet S x).card : Bit) = ∑ e, if N.crosses S e then x e else 0 := by
  unfold crossSet
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : N.crosses S e
  · rcases bit_cases (x e) with hx | hx
    · simp [hc, hx]
    · simp [hc, hx]
  · simp [hc]

/-- **An even word has an even number of crossing edges.** -/
theorem even_card_crossSet (N : Network V E) (S : V → Prop) {x : N.Word}
    (hx : N.boundary x = 0) : Even (N.crossSet S x).card := by
  rw [← ZMod.eq_zero_iff_even]
  have h := N.cast_card_crossSet S x
  rw [← N.cut_parity S x, hx] at h
  rw [h]
  simp

/-! ### Cycles by their crossing edges -/

/-- The number of cycles whose set of crossing edges is `A`. -/
def numCyclesAcross (N : Network V E) (S : V → Prop) (A : Finset E) : ℕ :=
  Nat.card {x : N.Word // N.IsCycleWord x ∧ N.crossSet S x = A}

omit [Fintype V] in
/-- Count the cycles by their sets of crossing edges. -/
theorem numCycles_eq_sum_across (N : Network V E) (S : V → Prop) (T : Finset E)
    (hT : ∀ g, N.crosses S g → g ∈ T) :
    N.numCycles = ∑ A ∈ T.powerset, N.numCyclesAcross S A := by
  unfold numCycles numCyclesAcross
  apply natCard_eq_sum_fibers (fun x : N.Word => N.IsCycleWord x) (fun x => N.crossSet S x)
  intro x _
  rw [Finset.mem_powerset]
  intro e he
  exact hT e (N.mem_crossSet.1 he).1

/-- No cycle has an odd number of crossing edges. -/
theorem numCyclesAcross_eq_zero_of_odd (N : Network V E) (S : V → Prop) {A : Finset E}
    (hA : ¬ Even A.card) : N.numCyclesAcross S A = 0 := by
  unfold numCyclesAcross
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun x => hA ?_⟩
  rw [← x.2.2]
  exact N.even_card_crossSet S x.2.1.boundary_eq_zero

theorem numCyclesAcross_singleton (N : Network V E) (S : V → Prop) (e : E) :
    N.numCyclesAcross S {e} = 0 := by
  apply N.numCyclesAcross_eq_zero_of_odd S
  rw [Finset.card_singleton]
  rintro ⟨k, hk⟩
  omega

theorem numCyclesAcross_triple (N : Network V E) (S : V → Prop) {e f g : E} (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) : N.numCyclesAcross S {e, f, g} = 0 := by
  apply N.numCyclesAcross_eq_zero_of_odd S
  have h3 : ({e, f, g} : Finset E).card = 3 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
    · rw [Finset.mem_singleton]
      exact hfg
    · rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hef h
      · exact heg h
  rw [h3]
  rintro ⟨k, hk⟩
  omega

/-! ### Cycles without a crossing edge -/

omit [Fintype V] in
theorem crossSet_eq_empty_of_within_inside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.inside S)) : N.crossSet S x = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  have h1 := N.mem_crossSet.1 he
  exact N.not_crosses_of_inside (h e h1.2) h1.1

omit [Fintype V] in
theorem crossSet_eq_empty_of_within_outside (N : Network V E) {S : V → Prop} {x : N.Word}
    (h : Within x (N.outside S)) : N.crossSet S x = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  have h1 := N.mem_crossSet.1 he
  exact N.not_crosses_of_outside (h e h1.2) h1.1

/-- A cycle without a crossing edge lies in one side. -/
theorem IsCycleWord.within_inside_or_outside {N : Network V E} {S : V → Prop} {x : N.Word}
    (hx : N.IsCycleWord x) (h0 : N.crossSet S x = ∅) :
    Within x (N.inside S) ∨ Within x (N.outside S) := by
  have hnc : ∀ e, x e ≠ 0 → ¬ N.crosses S e := by
    intro e he hc
    have hmem : e ∈ N.crossSet S x := N.mem_crossSet.2 ⟨hc, he⟩
    rw [h0] at hmem
    exact absurd hmem (Finset.not_mem_empty e)
  have hclosed : ∀ e, x e ≠ 0 → ¬ False → ¬ False → (S (N.src e) ↔ S (N.dst e)) :=
    fun e he _ _ => Classical.not_not.1 (hnc e he)
  obtain ⟨y, hy⟩ : ∃ y : N.Word, y = restrict x fun e => S (N.src e) ∨ S (N.dst e) :=
    ⟨_, rfl⟩
  have hy0 : N.boundary y = 0 := by
    funext w
    rw [hy, N.boundary_restrict_of_closed x S (fun _ => False) (fun _ h => h.elim) hclosed
      (fun h => h), hx.boundary_eq_zero]
    simp
  have hysub : N.IsSubword y x := by
    rw [hy]
    exact N.restrict_isSubword x _
  rcases Classical.em (y = 0) with hz | hz
  · right
    intro e he
    have h1 : ¬ (S (N.src e) ∨ S (N.dst e)) := by
      intro hor
      have h2 : y e ≠ 0 := by
        rw [hy]
        exact (restrict_ne_zero_iff x _ e).2 ⟨hor, he⟩
      exact h2 (congrFun hz e)
    exact ⟨fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
  · left
    have hyx : y = x := hx.eq_of_even_subword hysub hy0 hz
    intro e he
    have h1 : y e ≠ 0 := by
      rw [hyx]
      exact he
    rw [hy] at h1
    have hor := ((restrict_ne_zero_iff x _ e).1 h1).1
    have hiff := hclosed e he (fun h => h) (fun h => h)
    rcases hor with h | h
    · exact ⟨h, hiff.1 h⟩
    · exact ⟨hiff.2 h, h⟩

/-- **Cycles without a crossing edge.** They are the cycles of the two sides. -/
theorem numCyclesAcross_empty (N : Network V E) (S : V → Prop) :
    N.numCyclesAcross S ∅ =
      (N.sub (N.inside S)).numCycles + (N.sub (N.outside S)).numCycles := by
  rw [numCycles_sub, numCycles_sub,
    ← natCard_or_of_disjoint (fun x : N.Word => N.IsCycleWord x ∧ Within x (N.inside S))
      (fun x => N.IsCycleWord x ∧ Within x (N.outside S))]
  · unfold numCyclesAcross
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    constructor
    · rintro ⟨hx, h0⟩
      rcases hx.within_inside_or_outside h0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨hx, N.crossSet_eq_empty_of_within_inside h⟩
      · exact ⟨hx, N.crossSet_eq_empty_of_within_outside h⟩
  · rintro x ⟨hx, hin⟩ ⟨_, hout⟩
    obtain ⟨e, he⟩ := hx.exists_edge
    exact N.not_outside_of_inside (hin e he) (hout e he)

/-! ### Cycles through two crossing edges -/

/-- The boundary of the word of two crossing edges. -/
theorem boundary_unitPair (N : Network V E) {e f : E} {s₁ s₂ t₁ t₂ : V}
    (he : N.Joins e s₁ t₁) (hf : N.Joins f s₂ t₂) :
    N.boundary (unitWord e + unitWord f) = N.pathDemand s₁ s₂ + N.pathDemand t₁ t₂ := by
  rw [map_add, N.boundary_unitWord_of_joins he, N.boundary_unitWord_of_joins hf]
  show unitWord s₁ + unitWord t₁ + (unitWord s₂ + unitWord t₂) =
    unitWord s₁ + unitWord s₂ + (unitWord t₁ + unitWord t₂)
  abel

/-- **Gluing two paths.** Let `e` and `f` be two crossing edges. A path of the first side between
their ends in `S`, a path of the second side between their other ends, and the two edges form a
cycle. Its crossing edges are `e` and `f`. -/
theorem isCycleWord_glue (N : Network V E) (S : V → Prop) {e f : E} {s₁ s₂ t₁ t₂ : V}
    (he : N.Joins e s₁ t₁) (hs₁ : S s₁) (ht₁ : ¬ S t₁) (hf : N.Joins f s₂ t₂) (hs₂ : S s₂)
    (ht₂ : ¬ S t₂) (hef : e ≠ f) {P Q : N.Word} (hP : N.IsPathWord s₁ s₂ P)
    (hPin : Within P (N.inside S)) (hQ : N.IsPathWord t₁ t₂ Q)
    (hQout : Within Q (N.outside S)) :
    N.IsCycleWord (P + Q + (unitWord e + unitWord f)) ∧
      N.crossSet S (P + Q + (unitWord e + unitWord f)) = {e, f} := by
  have hce : N.crosses S e := N.crosses_of_joins he hs₁ ht₁
  have hcf : N.crosses S f := N.crosses_of_joins hf hs₂ ht₂
  obtain ⟨x, hxdef⟩ : ∃ x : N.Word, x = P + Q + (unitWord e + unitWord f) := ⟨_, rfl⟩
  rw [← hxdef]
  -- the values of `x` on the three kinds of edges
  have hxin : ∀ g, N.inside S g → x g = P g := by
    intro g hg
    have h1 : Q g = 0 := hQout.eq_zero (N.not_outside_of_inside hg)
    have h2 : (unitWord e + unitWord f) g = 0 :=
      unitPair_apply_of_ne (fun h => N.not_crosses_of_inside hg (h ▸ hce))
        (fun h => N.not_crosses_of_inside hg (h ▸ hcf))
    rw [hxdef]
    show P g + Q g + (unitWord e + unitWord f) g = P g
    rw [h1, h2, add_zero, add_zero]
  have hxout : ∀ g, N.outside S g → x g = Q g := by
    intro g hg
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_outside hg)
    have h2 : (unitWord e + unitWord f) g = 0 :=
      unitPair_apply_of_ne (fun h => N.not_crosses_of_outside hg (h ▸ hce))
        (fun h => N.not_crosses_of_outside hg (h ▸ hcf))
    rw [hxdef]
    show P g + Q g + (unitWord e + unitWord f) g = Q g
    rw [h1, h2, zero_add, add_zero]
  have hxcr : ∀ g, N.crosses S g → x g = (unitWord e + unitWord f) g := by
    intro g hg
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_crosses hg)
    have h2 : Q g = 0 := hQout.eq_zero (N.not_outside_of_crosses hg)
    rw [hxdef]
    show P g + Q g + (unitWord e + unitWord f) g = (unitWord e + unitWord f) g
    rw [h1, h2, zero_add, zero_add]
  have hxe : x e = 1 := by
    rw [hxcr e hce]
    exact unitPair_apply_left hef
  have hxf : x f = 1 := by
    rw [hxcr f hcf]
    exact unitPair_apply_right hef
  have hxother : ∀ g, N.crosses S g → g ≠ e → g ≠ f → x g = 0 := by
    intro g hg h1 h2
    rw [hxcr g hg]
    exact unitPair_apply_of_ne h1 h2
  have hx0 : N.boundary x = 0 := by
    rw [hxdef, map_add, map_add, hP.boundary_eq, hQ.boundary_eq, N.boundary_unitPair he hf]
    exact word_add_self _
  -- an even sub-word of `x` without the edge `e` is zero
  have hstar : ∀ y : N.Word, N.IsSubword y x → N.boundary y = 0 → y e = 0 → y = 0 := by
    intro y hsub hy0 hye
    have hyother : ∀ g, N.crosses S g → g ≠ e → g ≠ f → y g = 0 := by
      intro g hg h1 h2
      exact Classical.not_not.1 fun hne => hsub g hne (hxother g hg h1 h2)
    have hsum : (∑ g, if N.crosses S g then y g else 0) = y e + y f := by
      rw [Finset.sum_eq_add e f hef]
      · rw [if_pos hce, if_pos hcf]
      · intro g _ hg
        by_cases hc : N.crosses S g
        · rw [if_pos hc]
          exact hyother g hc hg.1 hg.2
        · rw [if_neg hc]
      · intro h
        exact absurd (Finset.mem_univ e) h
      · intro h
        exact absurd (Finset.mem_univ f) h
    have hpar : y e + y f = 0 := by
      rw [← hsum, ← N.cut_parity S y, hy0]
      simp
    have hyf : y f = 0 := by
      rw [hye, zero_add] at hpar
      exact hpar
    have hnc : ∀ g, y g ≠ 0 → ¬ N.crosses S g := by
      intro g hg hc
      by_cases h1 : g = e
      · exact hg (h1 ▸ hye)
      · by_cases h2 : g = f
        · exact hg (h2 ▸ hyf)
        · exact hg (hyother g hc h1 h2)
    have hclosed : ∀ g, y g ≠ 0 → ¬ False → ¬ False → (S (N.src g) ↔ S (N.dst g)) :=
      fun g hg _ _ => Classical.not_not.1 (hnc g hg)
    -- the part of `y` in `S` is an even sub-word of `P`
    have h1 : restrict y (fun g => S (N.src g) ∨ S (N.dst g)) = 0 := by
      apply hP.eq_zero_of_even_subword
      · intro g hg
        obtain ⟨hor, hyg⟩ := (restrict_ne_zero_iff y _ g).1 hg
        have hiff := hclosed g hyg (fun h => h) (fun h => h)
        have hin : N.inside S g := by
          rcases hor with h | h
          · exact ⟨h, hiff.1 h⟩
          · exact ⟨hiff.2 h, h⟩
        rw [← hxin g hin]
        exact hsub g hyg
      · funext w
        rw [N.boundary_restrict_of_closed y S (fun _ => False) (fun _ h => h.elim) hclosed
          (fun h => h), hy0]
        simp
    -- the part of `y` outside `S` is an even sub-word of `Q`
    have hclosed' : ∀ g, y g ≠ 0 → ¬ False → ¬ False → (¬ S (N.src g) ↔ ¬ S (N.dst g)) :=
      fun g hg h1 h2 => not_congr (hclosed g hg h1 h2)
    have h2 : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) = 0 := by
      apply hQ.eq_zero_of_even_subword
      · intro g hg
        obtain ⟨hor, hyg⟩ := (restrict_ne_zero_iff y _ g).1 hg
        have hiff := hclosed' g hyg (fun h => h) (fun h => h)
        have hout : N.outside S g := by
          rcases hor with h | h
          · exact ⟨h, hiff.1 h⟩
          · exact ⟨hiff.2 h, h⟩
        rw [← hxout g hout]
        exact hsub g hyg
      · funext w
        rw [N.boundary_restrict_of_closed y (fun v => ¬ S v) (fun _ => False)
          (fun _ h => h.elim) hclosed' (fun h => h), hy0]
        simp
    funext g
    refine Classical.not_not.1 fun hg => ?_
    by_cases hS : S (N.src g)
    · have h3 : restrict y (fun g => S (N.src g) ∨ S (N.dst g)) g ≠ 0 :=
        (restrict_ne_zero_iff y _ g).2 ⟨Or.inl hS, hg⟩
      exact h3 (congrFun h1 g)
    · have h3 : restrict y (fun g => ¬ S (N.src g) ∨ ¬ S (N.dst g)) g ≠ 0 :=
        (restrict_ne_zero_iff y _ g).2 ⟨Or.inl hS, hg⟩
      exact h3 (congrFun h2 g)
  refine ⟨?_, ?_⟩
  · apply N.isCycleWord_of_minimal
    · intro h
      rw [h] at hxe
      exact zero_ne_one hxe
    · exact hx0
    · intro y hsub hy0
      rcases bit_cases (y e) with hye | hye
      · exact Or.inl (hstar y hsub hy0 hye)
      · right
        have hz : x + y = 0 := by
          apply hstar (x + y)
          · intro g hg
            refine fun hxg => hg ?_
            have hyg : y g = 0 := Classical.not_not.1 fun hne => hsub g hne hxg
            show x g + y g = 0
            rw [hxg, hyg, add_zero]
          · rw [map_add, hx0, hy0, add_zero]
          · show x e + y e = 0
            rw [hxe, hye]
            exact bit_add_self 1
        exact (word_eq_of_add_eq_zero hz).symm
  · ext g
    rw [N.mem_crossSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hg⟩
      refine Classical.not_not.1 fun hno => hg ?_
      exact hxother g hc (fun h => hno (Or.inl h)) (fun h => hno (Or.inr h))
    · rintro (h | h)
      · rw [h]
        exact ⟨hce, by rw [hxe]; exact one_ne_zero⟩
      · rw [h]
        exact ⟨hcf, by rw [hxf]; exact one_ne_zero⟩

/-- **The parts of a cycle through two crossing edges.** Let `x` be a cycle whose crossing edges
are exactly `e` and `f`. Then the part of `x` in the first side is a path between the ends of `e`
and `f` in `S`, the part in the second side is a path between the other ends, and `x` is the sum
of these two paths and the two edges. -/
theorem IsCycleWord.parts_of_crossSet_pair {N : Network V E} {S : V → Prop} {e f : E}
    {s₁ s₂ t₁ t₂ : V} (he : N.Joins e s₁ t₁) (hs₁ : S s₁) (ht₁ : ¬ S t₁)
    (hf : N.Joins f s₂ t₂) (hs₂ : S s₂) (ht₂ : ¬ S t₂) (hs : s₁ ≠ s₂) (ht : t₁ ≠ t₂)
    (hef : e ≠ f) {x : N.Word} (hx : N.IsCycleWord x) (hcs : N.crossSet S x = {e, f}) :
    N.IsPathWord s₁ s₂ (restrict x (N.inside S)) ∧
      N.IsPathWord t₁ t₂ (restrict x (N.outside S)) ∧
      x = restrict x (N.inside S) + restrict x (N.outside S) + (unitWord e + unitWord f) := by
  have hce : N.crosses S e := N.crosses_of_joins he hs₁ ht₁
  have hcf : N.crosses S f := N.crosses_of_joins hf hs₂ ht₂
  have hmem : ∀ g, (N.crosses S g ∧ x g ≠ 0) ↔ (g = e ∨ g = f) := by
    intro g
    rw [← N.mem_crossSet, hcs, Finset.mem_insert, Finset.mem_singleton]
  have hxe : x e = 1 := bit_eq_one_of_ne_zero ((hmem e).2 (Or.inl rfl)).2
  have hxf : x f = 1 := bit_eq_one_of_ne_zero ((hmem f).2 (Or.inr rfl)).2
  have hcross : restrict x (N.crosses S) = unitWord e + unitWord f := by
    funext g
    by_cases hc : N.crosses S g
    · rw [restrict_apply_of_pos x hc]
      by_cases h1 : g = e
      · rw [h1, hxe]
        exact (unitPair_apply_left hef).symm
      · by_cases h2 : g = f
        · rw [h2, hxf]
          exact (unitPair_apply_right hef).symm
        · rw [unitPair_apply_of_ne h1 h2]
          refine Classical.not_not.1 fun hne => ?_
          rcases (hmem g).1 ⟨hc, hne⟩ with h | h
          · exact h1 h
          · exact h2 h
    · rw [restrict_apply_of_neg x hc]
      exact (unitPair_apply_of_ne (fun h : g = e => hc (h ▸ hce))
        (fun h : g = f => hc (h ▸ hcf))).symm
  have hsum : x =
      restrict x (N.inside S) + restrict x (N.outside S) + (unitWord e + unitWord f) := by
    rw [← hcross]
    exact (N.restrict_add_restrict_add_restrict S x).symm
  have hb : N.boundary (restrict x (N.inside S)) + N.boundary (restrict x (N.outside S)) =
      N.pathDemand s₁ s₂ + N.pathDemand t₁ t₂ := by
    apply word_eq_of_add_eq_zero
    rw [← N.boundary_unitPair he hf, ← map_add N.boundary, ← map_add N.boundary, ← hsum]
    exact hx.boundary_eq_zero
  have ha1 : ∀ v, ¬ S v → N.pathDemand s₁ s₂ v = 0 := by
    intro v hv
    have h1 : v ≠ s₁ := fun h => hv (h ▸ hs₁)
    have h2 : v ≠ s₂ := fun h => hv (h ▸ hs₂)
    simp [pathDemand, h1, h2]
  have hb1 : ∀ v, S v → N.pathDemand t₁ t₂ v = 0 := by
    intro v hv
    have h1 : v ≠ t₁ := fun h => ht₁ (h ▸ hv)
    have h2 : v ≠ t₂ := fun h => ht₂ (h ▸ hv)
    simp [pathDemand, h1, h2]
  obtain ⟨hbP, hbQ⟩ := N.boundary_split (within_restrict x (N.inside S))
    (within_restrict x (N.outside S)) ha1 hb1 hb
  have hminP : ∀ y : N.Word, N.IsSubword y (restrict x (N.inside S)) → N.boundary y = 0 →
      y = 0 := by
    intro y hsub hy0
    refine Classical.not_not.1 fun hne => ?_
    have hyx : y = x :=
      hx.eq_of_even_subword (fun g hg => N.restrict_isSubword x _ g (hsub g hg)) hy0 hne
    have h1 : y e ≠ 0 := by
      rw [hyx, hxe]
      exact one_ne_zero
    exact N.not_inside_of_crosses hce (within_restrict x (N.inside S) e (hsub e h1))
  have hminQ : ∀ y : N.Word, N.IsSubword y (restrict x (N.outside S)) → N.boundary y = 0 →
      y = 0 := by
    intro y hsub hy0
    refine Classical.not_not.1 fun hne => ?_
    have hyx : y = x :=
      hx.eq_of_even_subword (fun g hg => N.restrict_isSubword x _ g (hsub g hg)) hy0 hne
    have h1 : y e ≠ 0 := by
      rw [hyx, hxe]
      exact one_ne_zero
    exact N.not_outside_of_crosses hce (within_restrict x (N.outside S) e (hsub e h1))
  exact ⟨N.isPathWord_of_minimal hs hbP hminP, N.isPathWord_of_minimal ht hbQ hminQ, hsum⟩

/-- **Cycles through two crossing edges.** Let `e` join `s₁ ∈ S` and `t₁ ∉ S`, and let `f` join
`s₂ ∈ S` and `t₂ ∉ S`, with `s₁ ≠ s₂` and `t₁ ≠ t₂`. The number of cycles whose crossing edges
are exactly `e` and `f` is the number of paths from `s₁` to `s₂` in the first side times the
number of paths from `t₁` to `t₂` in the second side. -/
theorem numCyclesAcross_pair (N : Network V E) (S : V → Prop) {e f : E} {s₁ s₂ t₁ t₂ : V}
    (he : N.Joins e s₁ t₁) (hs₁ : S s₁) (ht₁ : ¬ S t₁) (hf : N.Joins f s₂ t₂) (hs₂ : S s₂)
    (ht₂ : ¬ S t₂) (hs : s₁ ≠ s₂) (ht : t₁ ≠ t₂) :
    N.numCyclesAcross S {e, f} =
      (N.sub (N.inside S)).numPaths s₁ s₂ * (N.sub (N.outside S)).numPaths t₁ t₂ := by
  have hef : e ≠ f := N.ne_of_joins he hs₁ ht₁ hf hs₂ ht₂ hs
  rw [numPaths_sub, numPaths_sub, ← Nat.card_prod]
  symm
  let g : {P : N.Word // N.IsPathWord s₁ s₂ P ∧ Within P (N.inside S)} ×
      {Q : N.Word // N.IsPathWord t₁ t₂ Q ∧ Within Q (N.outside S)} →
      {x : N.Word // N.IsCycleWord x ∧ N.crossSet S x = {e, f}} := fun pq =>
    ⟨pq.1.1 + pq.2.1 + (unitWord e + unitWord f),
      N.isCycleWord_glue S he hs₁ ht₁ hf hs₂ ht₂ hef pq.1.2.1 pq.1.2.2 pq.2.2.1 pq.2.2.2⟩
  unfold numCyclesAcross
  apply Nat.card_eq_of_bijective g
  constructor
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
    have h' : (g (P, Q)).1 = (g (P', Q')).1 := congrArg Subtype.val h
    have h'' : P.1 + Q.1 + (unitWord e + unitWord f) =
        P'.1 + Q'.1 + (unitWord e + unitWord f) := h'
    have h3 : P.1 + Q.1 = P'.1 + Q'.1 := add_right_cancel h''
    have hPP : P.1 = P'.1 := by
      have h4 : restrict (P.1 + Q.1) (N.inside S) = restrict (P'.1 + Q'.1) (N.inside S) := by
        rw [h3]
      rw [restrict_add, restrict_add, restrict_eq_self P.2.2, restrict_eq_self P'.2.2,
        restrict_eq_zero (N.inside S) Q.2.2 (fun _ hg => N.not_inside_of_outside hg),
        restrict_eq_zero (N.inside S) Q'.2.2 (fun _ hg => N.not_inside_of_outside hg),
        add_zero, add_zero] at h4
      exact h4
    have hQQ : Q.1 = Q'.1 := by
      have h4 : restrict (P.1 + Q.1) (N.outside S) = restrict (P'.1 + Q'.1) (N.outside S) := by
        rw [h3]
      rw [restrict_add, restrict_add, restrict_eq_self Q.2.2, restrict_eq_self Q'.2.2,
        restrict_eq_zero (N.outside S) P.2.2 (fun _ hg => N.not_outside_of_inside hg),
        restrict_eq_zero (N.outside S) P'.2.2 (fun _ hg => N.not_outside_of_inside hg),
        zero_add, zero_add] at h4
      exact h4
    exact Prod.ext (Subtype.ext hPP) (Subtype.ext hQQ)
  · rintro ⟨x, hx, hcs⟩
    obtain ⟨hP, hQ, hsum⟩ := hx.parts_of_crossSet_pair he hs₁ ht₁ hf hs₂ ht₂ hs ht hef hcs
    refine ⟨(⟨restrict x (N.inside S), hP, within_restrict x _⟩,
      ⟨restrict x (N.outside S), hQ, within_restrict x _⟩), ?_⟩
    exact Subtype.ext hsum.symm

/-! ### The number of cycles of a graph with a small cut -/

/-- **A cut with at most one crossing edge.** Every cycle lies in one side. -/
theorem numCycles_of_one_crossing (N : Network V E) (S : V → Prop) {e : E}
    (hC : ∀ g, N.crosses S g → g = e) :
    N.numCycles = (N.sub (N.inside S)).numCycles + (N.sub (N.outside S)).numCycles := by
  rw [N.numCycles_eq_sum_across S {e} (fun g hg => Finset.mem_singleton.2 (hC g hg)),
    sum_powerset_singleton, N.numCyclesAcross_empty S, N.numCyclesAcross_singleton S e,
    add_zero]

/-- **Equation (6.1) of the paper for a cut of size two.** Let the crossing edges be `e` and
`f`, where `e` joins `s₁ ∈ S` and `t₁ ∉ S`, and `f` joins `s₂ ∈ S` and `t₂ ∉ S`, with `s₁ ≠ s₂`
and `t₁ ≠ t₂`. Then the number of cycles is the sum of the numbers of cycles of the two sides
and of the product of the numbers of paths between the ends of the two edges in each side. -/
theorem numCycles_of_two_crossing (N : Network V E) (S : V → Prop) {e f : E}
    {s₁ s₂ t₁ t₂ : V} (hC : ∀ g, N.crosses S g → g = e ∨ g = f) (he : N.Joins e s₁ t₁)
    (hs₁ : S s₁) (ht₁ : ¬ S t₁) (hf : N.Joins f s₂ t₂) (hs₂ : S s₂) (ht₂ : ¬ S t₂)
    (hs : s₁ ≠ s₂) (ht : t₁ ≠ t₂) :
    N.numCycles = (N.sub (N.inside S)).numCycles + (N.sub (N.outside S)).numCycles +
      (N.sub (N.inside S)).numPaths s₁ s₂ * (N.sub (N.outside S)).numPaths t₁ t₂ := by
  have hef : e ≠ f := N.ne_of_joins he hs₁ ht₁ hf hs₂ ht₂ hs
  have hT : ∀ g, N.crosses S g → g ∈ ({e, f} : Finset E) := by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact hC g hg
  have hnot : e ∉ ({f} : Finset E) := by
    rw [Finset.mem_singleton]
    exact hef
  rw [N.numCycles_eq_sum_across S {e, f} hT, Finset.sum_powerset_insert hnot,
    sum_powerset_singleton, sum_powerset_singleton, insert_empty_eq,
    N.numCyclesAcross_empty S, N.numCyclesAcross_singleton S f,
    N.numCyclesAcross_singleton S e,
    N.numCyclesAcross_pair S he hs₁ ht₁ hf hs₂ ht₂ hs ht, add_zero, zero_add]

/-- **Equation (6.1) of the paper for a cut of size three.** Let the crossing edges be `e₁`,
`e₂`, `e₃`, where `eᵢ` joins `sᵢ ∈ S` and `tᵢ ∉ S`, and let the `sᵢ` be distinct and the `tᵢ` be
distinct. Then the number of cycles is the sum of the numbers of cycles of the two sides and,
over the three pairs `i < j`, of the product of the number of paths from `sᵢ` to `sⱼ` in the
first side and the number of paths from `tᵢ` to `tⱼ` in the second side. -/
theorem numCycles_of_three_crossing (N : Network V E) (S : V → Prop) {e₁ e₂ e₃ : E}
    {s₁ s₂ s₃ t₁ t₂ t₃ : V} (hC : ∀ g, N.crosses S g → g = e₁ ∨ g = e₂ ∨ g = e₃)
    (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂) (h₃ : N.Joins e₃ s₃ t₃)
    (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃) (ht₁ : ¬ S t₁) (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃) (ht12 : t₁ ≠ t₂) (ht13 : t₁ ≠ t₃)
    (ht23 : t₂ ≠ t₃) :
    N.numCycles = (N.sub (N.inside S)).numCycles + (N.sub (N.outside S)).numCycles +
      (N.sub (N.inside S)).numPaths s₁ s₂ * (N.sub (N.outside S)).numPaths t₁ t₂ +
      (N.sub (N.inside S)).numPaths s₁ s₃ * (N.sub (N.outside S)).numPaths t₁ t₃ +
      (N.sub (N.inside S)).numPaths s₂ s₃ * (N.sub (N.outside S)).numPaths t₂ t₃ := by
  have h12 : e₁ ≠ e₂ := N.ne_of_joins h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12
  have h13 : e₁ ≠ e₃ := N.ne_of_joins h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13
  have h23 : e₂ ≠ e₃ := N.ne_of_joins h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23
  have hT : ∀ g, N.crosses S g → g ∈ ({e₁, e₂, e₃} : Finset E) := by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    exact hC g hg
  have hnot1 : e₁ ∉ ({e₂, e₃} : Finset E) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact h12 h
    · exact h13 h
  have hnot2 : e₂ ∉ ({e₃} : Finset E) := by
    rw [Finset.mem_singleton]
    exact h23
  rw [N.numCycles_eq_sum_across S {e₁, e₂, e₃} hT, Finset.sum_powerset_insert hnot1,
    Finset.sum_powerset_insert hnot2, Finset.sum_powerset_insert hnot2,
    sum_powerset_singleton, sum_powerset_singleton, sum_powerset_singleton,
    sum_powerset_singleton]
  simp only [insert_empty_eq]
  rw [N.numCyclesAcross_empty S, N.numCyclesAcross_singleton S e₃,
    N.numCyclesAcross_singleton S e₂, N.numCyclesAcross_singleton S e₁,
    N.numCyclesAcross_triple S h12 h13 h23,
    N.numCyclesAcross_pair S h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12 ht12,
    N.numCyclesAcross_pair S h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13 ht13,
    N.numCyclesAcross_pair S h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23 ht23]
  ring

end Erdos1016.BoundaryTrace.Network

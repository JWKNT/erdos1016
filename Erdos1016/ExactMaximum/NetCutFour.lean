import Erdos1016.ExactMaximum.NetPairs

set_option autoImplicit false

/-!
# Cycles across a cut with four edges

This file proves Lemma 6.4 of the paper "The maximum number of cycles in a graph of large rank"
as a counting statement about a cut `S` of a network.

Let the crossing edge `eᵢ` join `sᵢ ∈ S` and `tᵢ ∉ S` for `i = 1, 2, 3, 4`, with distinct `sᵢ`
and distinct `tᵢ`. For a side and a pairing of its four ends, count the pairs of vertex-disjoint
paths of the side that join the ends as the pairing says.

* `numCyclesAcross_four`: the number of cycles through all four edges is the sum, over the
  ordered pairs of different pairings, of the product of the two counts.
* `numCycles_of_four_crossing`: if there is no other crossing edge, the number of cycles of the
  network is the sum of the numbers of cycles of the two sides, of the six products of numbers
  of paths between two ends, and of the number above.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

local instance netCutFourDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### Counting pairs of disjoint paths -/

/-- The number of pairs of vertex-disjoint paths from `a` to `b` and from `c` to `d`. -/
def numPathPairs (N : Network V E) (a b c d : V) : ℕ :=
  Nat.card {AB : N.Word × N.Word // N.IsPathPair a b c d AB.1 AB.2}

/-- The pairs of vertex-disjoint paths from `a` to `b` and from `c` to `d` within `p`. -/
abbrev PathPairsIn (N : Network V E) (p : E → Prop) (a b c d : V) : Type _ :=
  {AB : N.Word × N.Word // N.IsPathPair a b c d AB.1 AB.2 ∧ Within AB.1 p ∧ Within AB.2 p}

/-- The number of pairs of vertex-disjoint paths from `a` to `b` and from `c` to `d` within
`p`. -/
def numPathPairsIn (N : Network V E) (p : E → Prop) (a b c d : V) : ℕ :=
  Nat.card (N.PathPairsIn p a b c d)

omit [Fintype V] in
theorem vertexDisjoint_extend_iff (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (y y' : {e : E // p e} → Bit) :
    N.VertexDisjoint (extend p y) (extend p y') ↔ (N.sub p).VertexDisjoint y y' := by
  constructor
  · intro h v
    have h1 := h v
    rw [N.deg_extend p y v, N.deg_extend p y' v] at h1
    exact h1
  · intro h v
    rw [N.deg_extend p y v, N.deg_extend p y' v]
    exact h v

omit [Fintype V] in
theorem isPathPair_extend_iff (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (a b c d : V) (y y' : {e : E // p e} → Bit) :
    N.IsPathPair a b c d (extend p y) (extend p y') ↔ (N.sub p).IsPathPair a b c d y y' :=
  and_congr (N.isPathWord_extend_iff p a b y)
    (and_congr (N.isPathWord_extend_iff p c d y') (N.vertexDisjoint_extend_iff p y y'))

omit [Fintype V] in
/-- The path pairs of a part are the path pairs of the network within the part. -/
theorem numPathPairs_sub (N : Network V E) (p : E → Prop) [Fintype {e : E // p e}]
    (a b c d : V) : (N.sub p).numPathPairs a b c d = N.numPathPairsIn p a b c d := by
  let f : {yy : (N.sub p).Word × (N.sub p).Word // (N.sub p).IsPathPair a b c d yy.1 yy.2} →
      N.PathPairsIn p a b c d := fun yy =>
    ⟨(extend p yy.1.1, extend p yy.1.2),
      (N.isPathPair_extend_iff p a b c d yy.1.1 yy.1.2).2 yy.2,
      within_extend p yy.1.1, within_extend p yy.1.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u w h
      have h' : (f u).1 = (f w).1 := congrArg Subtype.val h
      have h1 : extend p u.1.1 = extend p w.1.1 := congrArg Prod.fst h'
      have h2 : extend p u.1.2 = extend p w.1.2 := congrArg Prod.snd h'
      exact Subtype.ext (Prod.ext (extend_injective p h1) (extend_injective p h2))
    · rintro ⟨⟨A, B⟩, hAB, hA, hB⟩
      have hAB' : N.IsPathPair a b c d A B := hAB
      have hA' : Within A p := hA
      have hB' : Within B p := hB
      have hpull : (N.sub p).IsPathPair a b c d (pull p A) (pull p B) := by
        rw [← N.isPathPair_extend_iff p, extend_pull p hA', extend_pull p hB']
        exact hAB'
      refine ⟨⟨(pull p A, pull p B), hpull⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext (extend_pull p hA') (extend_pull p hB')
  exact Nat.card_eq_of_bijective f hf

omit [Fintype V] in
/-- The second path can be taken in either direction. -/
theorem numPathPairsIn_swap_right (N : Network V E) (p : E → Prop) (a b c d : V) :
    N.numPathPairsIn p a b c d = N.numPathPairsIn p a b d c :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    ⟨fun h => ⟨h.1.swap_right, h.2⟩, fun h => ⟨h.1.swap_right, h.2⟩⟩)

/-! ### Glued words -/

omit [Fintype V] [Fintype E] in
theorem restrict_inside_glue (N : Network V E) {S : V → Prop} {P Q R : N.Word}
    (hP : Within P (N.inside S)) (hQ : Within Q (N.outside S)) (hR : Within R (N.crosses S)) :
    restrict (P + Q + R) (N.inside S) = P := by
  rw [restrict_add, restrict_add, restrict_eq_self hP,
    restrict_eq_zero (N.inside S) hQ (fun _ h => N.not_inside_of_outside h),
    restrict_eq_zero (N.inside S) hR (fun _ h => N.not_inside_of_crosses h), add_zero, add_zero]

omit [Fintype V] [Fintype E] in
theorem restrict_outside_glue (N : Network V E) {S : V → Prop} {P Q R : N.Word}
    (hP : Within P (N.inside S)) (hQ : Within Q (N.outside S)) (hR : Within R (N.crosses S)) :
    restrict (P + Q + R) (N.outside S) = Q := by
  rw [restrict_add, restrict_add, restrict_eq_self hQ,
    restrict_eq_zero (N.outside S) hP (fun _ h => N.not_outside_of_inside h),
    restrict_eq_zero (N.outside S) hR (fun _ h => N.not_outside_of_crosses h), zero_add,
    add_zero]

omit [Fintype V] in
/-- The crossing edges of a glued word are the edges of its crossing part. -/
theorem mem_crossSet_glue (N : Network V E) {S : V → Prop} {P Q R : N.Word}
    (hP : Within P (N.inside S)) (hQ : Within Q (N.outside S)) (hR : Within R (N.crosses S))
    (g : E) : g ∈ N.crossSet S (P + Q + R) ↔ R g ≠ 0 := by
  rw [N.mem_crossSet]
  constructor
  · rintro ⟨hc, hg⟩ hR0
    apply hg
    show P g + Q g + R g = 0
    rw [hP.eq_zero (N.not_inside_of_crosses hc), hQ.eq_zero (N.not_outside_of_crosses hc), hR0,
      add_zero, add_zero]
  · intro hg
    have hc := hR g hg
    refine ⟨hc, ?_⟩
    show P g + Q g + R g ≠ 0
    rw [hP.eq_zero (N.not_inside_of_crosses hc), hQ.eq_zero (N.not_outside_of_crosses hc),
      zero_add, zero_add]
    exact hg

/-! ### Cycles through four crossing edges with a given pairing in the first side -/

/-- The cycles with crossing set `T` whose part in the first side is a pair of disjoint paths
from `a` to `b` and from `c` to `d`. -/
abbrev CyclesFour (N : Network V E) (S : V → Prop) (T : Finset E) (a b c d : V) : Type _ :=
  {x : N.Word // N.IsCycleWord x ∧ N.crossSet S x = T ∧
    ∃ A B : N.Word, N.IsPathPair a b c d A B ∧ restrict x (N.inside S) = A + B}

/-- **Cycles through four crossing edges, with the pairing `s₁s₂ | s₃s₄` in the first side.**
Their number is the number of path pairs of the first side for this pairing, times the number of
path pairs of the second side for the two other pairings `t₁t₃ | t₂t₄` and `t₁t₄ | t₂t₃`. -/
theorem natCard_cyclesFour (N : Network V E) (S : V → Prop) {e₁ e₂ e₃ e₄ : E}
    {s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : V} (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂)
    (h₃ : N.Joins e₃ s₃ t₃) (h₄ : N.Joins e₄ s₄ t₄) (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃)
    (hs₄ : S s₄) (ht₁ : ¬ S t₁) (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃) (ht₄ : ¬ S t₄)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs14 : s₁ ≠ s₄) (hs23 : s₂ ≠ s₃) (hs24 : s₂ ≠ s₄)
    (hs34 : s₃ ≠ s₄) (ht12 : t₁ ≠ t₂) (ht13 : t₁ ≠ t₃) (ht14 : t₁ ≠ t₄) (ht23 : t₂ ≠ t₃)
    (ht24 : t₂ ≠ t₄) (ht34 : t₃ ≠ t₄) {T : Finset E}
    (hT : ∀ g, g ∈ T ↔ g = e₁ ∨ g = e₂ ∨ g = e₃ ∨ g = e₄) :
    Nat.card (N.CyclesFour S T s₁ s₂ s₃ s₄) =
      N.numPathPairsIn (N.inside S) s₁ s₂ s₃ s₄ *
        (N.numPathPairsIn (N.outside S) t₁ t₃ t₂ t₄ +
          N.numPathPairsIn (N.outside S) t₁ t₄ t₂ t₃) := by
  have hc₁ : N.crosses S e₁ := N.crosses_of_joins h₁ hs₁ ht₁
  have hc₂ : N.crosses S e₂ := N.crosses_of_joins h₂ hs₂ ht₂
  have hc₃ : N.crosses S e₃ := N.crosses_of_joins h₃ hs₃ ht₃
  have hc₄ : N.crosses S e₄ := N.crosses_of_joins h₄ hs₄ ht₄
  have h12 : e₁ ≠ e₂ := N.ne_of_joins h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12
  have h13 : e₁ ≠ e₃ := N.ne_of_joins h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13
  have h14 : e₁ ≠ e₄ := N.ne_of_joins h₁ hs₁ ht₁ h₄ hs₄ ht₄ hs14
  have h23 : e₂ ≠ e₃ := N.ne_of_joins h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23
  have h24 : e₂ ≠ e₄ := N.ne_of_joins h₂ hs₂ ht₂ h₄ hs₄ ht₄ hs24
  have h34 : e₃ ≠ e₄ := N.ne_of_joins h₃ hs₃ ht₃ h₄ hs₄ ht₄ hs34
  obtain ⟨R, hR⟩ : ∃ R : N.Word,
      R = unitWord e₁ + unitWord e₂ + (unitWord e₃ + unitWord e₄) := ⟨_, rfl⟩
  have hRcr : Within R (N.crosses S) := by
    rw [hR]
    exact ((within_unitWord hc₁).add (within_unitWord hc₂)).add
      ((within_unitWord hc₃).add (within_unitWord hc₄))
  have hRmem : ∀ g, R g ≠ 0 ↔ g ∈ T := by
    intro g
    rw [hT, hR]
    constructor
    · intro hg
      refine Classical.not_not.1 fun hno => hg ?_
      exact unitQuad_apply_of_ne (fun h => hno (Or.inl h)) (fun h => hno (Or.inr (Or.inl h)))
        (fun h => hno (Or.inr (Or.inr (Or.inl h)))) (fun h => hno (Or.inr (Or.inr (Or.inr h))))
    · rintro (h | h | h | h)
      · rw [h, unitQuad_apply_one h12 h13 h14]
        exact one_ne_zero
      · rw [h, unitQuad_apply_two h12 h23 h24]
        exact one_ne_zero
      · rw [h, unitQuad_apply_three h13 h23 h34]
        exact one_ne_zero
      · rw [h, unitQuad_apply_four h14 h24 h34]
        exact one_ne_zero
  -- a glued word that is a cycle belongs to the class
  have key : ∀ A B C D : N.Word, N.IsPathPair s₁ s₂ s₃ s₄ A B → Within A (N.inside S) →
      Within B (N.inside S) → Within C (N.outside S) → Within D (N.outside S) →
      N.IsCycleWord (A + B + (C + D) + R) →
      N.IsCycleWord (A + B + (C + D) + R) ∧ N.crossSet S (A + B + (C + D) + R) = T ∧
        ∃ A' B' : N.Word, N.IsPathPair s₁ s₂ s₃ s₄ A' B' ∧
          restrict (A + B + (C + D) + R) (N.inside S) = A' + B' := by
    intro A B C D hAB hA hB hC hD hcyc
    refine ⟨hcyc, ?_, A, B, hAB, N.restrict_inside_glue (hA.add hB) (hC.add hD) hRcr⟩
    ext g
    rw [N.mem_crossSet_glue (hA.add hB) (hC.add hD) hRcr, hRmem]
  have cyc₁ : ∀ A B C D : N.Word, N.IsPathPair s₁ s₂ s₃ s₄ A B → Within A (N.inside S) →
      Within B (N.inside S) → N.IsPathPair t₁ t₃ t₂ t₄ C D → Within C (N.outside S) →
      Within D (N.outside S) → N.IsCycleWord (A + B + (C + D) + R) := by
    intro A B C D hAB hA hB hCD hC hD
    rw [hR]
    exact N.isCycleWord_glue4 S h₁ h₂ h₃ h₄ hs₁ hs₂ hs₃ hs₄ ht₁ ht₂ ht₃ ht₄ hAB hA hB hCD hC hD
  have cyc₂ : ∀ A B C D : N.Word, N.IsPathPair s₁ s₂ s₃ s₄ A B → Within A (N.inside S) →
      Within B (N.inside S) → N.IsPathPair t₁ t₄ t₂ t₃ C D → Within C (N.outside S) →
      Within D (N.outside S) → N.IsCycleWord (A + B + (C + D) + R) := by
    intro A B C D hAB hA hB hCD hC hD
    have h := N.isCycleWord_glue4 S h₁ h₂ h₄ h₃ hs₁ hs₂ hs₄ hs₃ ht₁ ht₂ ht₄ ht₃ hAB.swap_right
      hA hB hCD hC hD
    rw [hR, add_comm (unitWord e₃) (unitWord e₄)]
    exact h
  -- the parts of two equal glued words are equal
  have hsplit : ∀ A B C D A' B' C' D' : N.Word, Within A (N.inside S) →
      Within B (N.inside S) → Within C (N.outside S) → Within D (N.outside S) →
      Within A' (N.inside S) → Within B' (N.inside S) → Within C' (N.outside S) →
      Within D' (N.outside S) → A + B + (C + D) + R = A' + B' + (C' + D') + R →
      A + B = A' + B' ∧ C + D = C' + D' := by
    intro A B C D A' B' C' D' hA hB hC hD hA' hB' hC' hD' h
    have k1 : restrict (A + B + (C + D) + R) (N.inside S) =
        restrict (A' + B' + (C' + D') + R) (N.inside S) := by rw [h]
    have k2 : restrict (A + B + (C + D) + R) (N.outside S) =
        restrict (A' + B' + (C' + D') + R) (N.outside S) := by rw [h]
    rw [N.restrict_inside_glue (hA.add hB) (hC.add hD) hRcr,
      N.restrict_inside_glue (hA'.add hB') (hC'.add hD') hRcr] at k1
    rw [N.restrict_outside_glue (hA.add hB) (hC.add hD) hRcr,
      N.restrict_outside_glue (hA'.add hB') (hC'.add hD') hRcr] at k2
    exact ⟨k1, k2⟩
  unfold numPathPairsIn
  rw [← Nat.card_sum, ← Nat.card_prod]
  symm
  let φ : N.PathPairsIn (N.inside S) s₁ s₂ s₃ s₄ ×
      (N.PathPairsIn (N.outside S) t₁ t₃ t₂ t₄ ⊕ N.PathPairsIn (N.outside S) t₁ t₄ t₂ t₃) →
      N.CyclesFour S T s₁ s₂ s₃ s₄ := fun z =>
    match z with
    | (AB, Sum.inl CD) =>
      ⟨AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R,
        key _ _ _ _ AB.2.1 AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
          (cyc₁ _ _ _ _ AB.2.1 AB.2.2.1 AB.2.2.2 CD.2.1 CD.2.2.1 CD.2.2.2)⟩
    | (AB, Sum.inr CD) =>
      ⟨AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R,
        key _ _ _ _ AB.2.1 AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
          (cyc₂ _ _ _ _ AB.2.1 AB.2.2.1 AB.2.2.2 CD.2.1 CD.2.2.1 CD.2.2.2)⟩
  apply Nat.card_eq_of_bijective φ
  constructor
  · rintro ⟨AB, CD | CD⟩ ⟨AB', CD' | CD'⟩ h
    · have hv : (φ (AB, Sum.inl CD)).1 = (φ (AB', Sum.inl CD')).1 := congrArg Subtype.val h
      have hv' : AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R =
          AB'.1.1 + AB'.1.2 + (CD'.1.1 + CD'.1.2) + R := hv
      obtain ⟨hin, hout⟩ := hsplit _ _ _ _ _ _ _ _ AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
        AB'.2.2.1 AB'.2.2.2 CD'.2.2.1 CD'.2.2.2 hv'
      obtain ⟨hA, hB⟩ := AB.2.1.eq_of_add_eq AB'.2.1 hin
      obtain ⟨hC, hD⟩ := CD.2.1.eq_of_add_eq CD'.2.1 hout
      have hAB : AB = AB' := Subtype.ext (Prod.ext hA hB)
      have hCD : CD = CD' := Subtype.ext (Prod.ext hC hD)
      rw [hAB, hCD]
    · exfalso
      have hv : (φ (AB, Sum.inl CD)).1 = (φ (AB', Sum.inr CD')).1 := congrArg Subtype.val h
      have hv' : AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R =
          AB'.1.1 + AB'.1.2 + (CD'.1.1 + CD'.1.2) + R := hv
      obtain ⟨_, hout⟩ := hsplit _ _ _ _ _ _ _ _ AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
        AB'.2.2.1 AB'.2.2.2 CD'.2.2.1 CD'.2.2.2 hv'
      exact CD.2.1.false_of_add_eq CD'.2.1 hout (by rw [CD.2.1.2.1.2.2.1]; exact Nat.one_pos)
    · exfalso
      have hv : (φ (AB, Sum.inr CD)).1 = (φ (AB', Sum.inl CD')).1 := congrArg Subtype.val h
      have hv' : AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R =
          AB'.1.1 + AB'.1.2 + (CD'.1.1 + CD'.1.2) + R := hv
      obtain ⟨_, hout⟩ := hsplit _ _ _ _ _ _ _ _ AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
        AB'.2.2.1 AB'.2.2.2 CD'.2.2.1 CD'.2.2.2 hv'
      exact CD.2.1.false_of_add_eq CD'.2.1 hout (by rw [CD.2.1.2.1.2.2.1]; exact Nat.one_pos)
    · have hv : (φ (AB, Sum.inr CD)).1 = (φ (AB', Sum.inr CD')).1 := congrArg Subtype.val h
      have hv' : AB.1.1 + AB.1.2 + (CD.1.1 + CD.1.2) + R =
          AB'.1.1 + AB'.1.2 + (CD'.1.1 + CD'.1.2) + R := hv
      obtain ⟨hin, hout⟩ := hsplit _ _ _ _ _ _ _ _ AB.2.2.1 AB.2.2.2 CD.2.2.1 CD.2.2.2
        AB'.2.2.1 AB'.2.2.2 CD'.2.2.1 CD'.2.2.2 hv'
      obtain ⟨hA, hB⟩ := AB.2.1.eq_of_add_eq AB'.2.1 hin
      obtain ⟨hC, hD⟩ := CD.2.1.eq_of_add_eq CD'.2.1 hout
      have hAB : AB = AB' := Subtype.ext (Prod.ext hA hB)
      have hCD : CD = CD' := Subtype.ext (Prod.ext hC hD)
      rw [hAB, hCD]
  · rintro ⟨x, hx, hcs, A, B, hAB, hxin⟩
    obtain ⟨hsum, _, hbQ, _, hminQ, _, hdegQ⟩ := hx.parts_of_crossSet_four h₁ h₂ h₃ h₄ hs₁ hs₂
      hs₃ hs₄ ht₁ ht₂ ht₃ ht₄ hs12 hs13 hs14 hs23 hs24 hs34 hT hcs
    have hA : Within A (N.inside S) := fun g hg =>
      within_restrict x (N.inside S) g (by rw [hxin]; exact hAB.isSubword_left g hg)
    have hB : Within B (N.inside S) := fun g hg =>
      within_restrict x (N.inside S) g (by rw [hxin]; exact hAB.isSubword_right g hg)
    have hbQ' : N.boundary (restrict x (N.outside S)) =
        N.pathDemand t₁ t₃ + N.pathDemand t₂ t₄ := by
      rw [hbQ]
      show unitWord t₁ + unitWord t₂ + (unitWord t₃ + unitWord t₄) =
        unitWord t₁ + unitWord t₃ + (unitWord t₂ + unitWord t₄)
      abel
    have hxT : ∀ g, g ∈ T → x g ≠ 0 := by
      intro g hg
      rw [← hcs] at hg
      exact (N.mem_crossSet.1 hg).2
    have hval : ∀ C D : N.Word, restrict x (N.outside S) = C + D →
        A + B + (C + D) + R = x := by
      intro C D hQ
      rw [← hxin, ← hQ, hR]
      exact hsum.symm
    rcases N.exists_pathPair_of_minimal ht13 ht12 ht14 ht23.symm ht34 ht24 hbQ' hdegQ hminQ with
      ⟨C, D, hCD, hQ⟩ | ⟨C, D, hCD, hQ⟩ | ⟨C, D, hCD, hQ⟩
    · have hC : Within C (N.outside S) := fun g hg =>
        within_restrict x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_left g hg)
      have hD : Within D (N.outside S) := fun g hg =>
        within_restrict x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_right g hg)
      refine ⟨(⟨(A, B), hAB, hA, hB⟩, Sum.inl ⟨(C, D), hCD, hC, hD⟩), ?_⟩
      exact Subtype.ext (hval C D hQ)
    · -- the same pairing in both sides: the cycle through `e₁`, `e₂` is a proper part of `x`
      exfalso
      have hC : Within C (N.outside S) := fun g hg =>
        within_restrict x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_left g hg)
      have hAx : N.IsSubword A x := fun g hg =>
        N.restrict_isSubword x (N.inside S) g (by rw [hxin]; exact hAB.isSubword_left g hg)
      have hCx : N.IsSubword C x := fun g hg =>
        N.restrict_isSubword x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_left g hg)
      have heq := hx.eq_glue_of_subword h₁ hs₁ ht₁ h₂ hs₂ ht₂ h12 hAB.1 hA hCD.1 hC hAx hCx
        (hxT e₁ ((hT e₁).2 (Or.inl rfl))) (hxT e₂ ((hT e₂).2 (Or.inr (Or.inl rfl))))
      have h3 : x e₃ ≠ 0 := hxT e₃ ((hT e₃).2 (Or.inr (Or.inr (Or.inl rfl))))
      apply h3
      rw [← heq]
      show A e₃ + C e₃ + (unitWord e₁ + unitWord e₂) e₃ = 0
      rw [hA.eq_zero (N.not_inside_of_crosses hc₃), hC.eq_zero (N.not_outside_of_crosses hc₃),
        unitPair_apply_of_ne (Ne.symm h13) (Ne.symm h23), add_zero, add_zero]
    · have hC : Within C (N.outside S) := fun g hg =>
        within_restrict x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_left g hg)
      have hD : Within D (N.outside S) := fun g hg =>
        within_restrict x (N.outside S) g (by rw [hQ]; exact hCD.isSubword_right g hg)
      refine ⟨(⟨(A, B), hAB, hA, hB⟩, Sum.inr ⟨(C, D), hCD.swap_right, hC, hD⟩), ?_⟩
      exact Subtype.ext (hval C D hQ)

/-! ### All cycles through four crossing edges -/

/-- **Lemma 6.4 of the paper: cycles through all four crossing edges.** Their number is the sum,
over the ordered pairs of different pairings, of the number of path pairs of the first side for
the first pairing times the number of path pairs of the second side for the second pairing. -/
theorem numCyclesAcross_four (N : Network V E) (S : V → Prop) {e₁ e₂ e₃ e₄ : E}
    {s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : V} (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂)
    (h₃ : N.Joins e₃ s₃ t₃) (h₄ : N.Joins e₄ s₄ t₄) (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃)
    (hs₄ : S s₄) (ht₁ : ¬ S t₁) (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃) (ht₄ : ¬ S t₄)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs14 : s₁ ≠ s₄) (hs23 : s₂ ≠ s₃) (hs24 : s₂ ≠ s₄)
    (hs34 : s₃ ≠ s₄) (ht12 : t₁ ≠ t₂) (ht13 : t₁ ≠ t₃) (ht14 : t₁ ≠ t₄) (ht23 : t₂ ≠ t₃)
    (ht24 : t₂ ≠ t₄) (ht34 : t₃ ≠ t₄) :
    N.numCyclesAcross S {e₁, e₂, e₃, e₄} =
      N.numPathPairsIn (N.inside S) s₁ s₂ s₃ s₄ *
          (N.numPathPairsIn (N.outside S) t₁ t₃ t₂ t₄ +
            N.numPathPairsIn (N.outside S) t₁ t₄ t₂ t₃) +
        N.numPathPairsIn (N.inside S) s₁ s₃ s₂ s₄ *
          (N.numPathPairsIn (N.outside S) t₁ t₂ t₃ t₄ +
            N.numPathPairsIn (N.outside S) t₁ t₄ t₂ t₃) +
        N.numPathPairsIn (N.inside S) s₁ s₄ s₂ s₃ *
          (N.numPathPairsIn (N.outside S) t₁ t₂ t₃ t₄ +
            N.numPathPairsIn (N.outside S) t₁ t₃ t₂ t₄) := by
  obtain ⟨T, hTdef⟩ : ∃ T : Finset E, T = {e₁, e₂, e₃, e₄} := ⟨_, rfl⟩
  have hT : ∀ g, g ∈ T ↔ g = e₁ ∨ g = e₂ ∨ g = e₃ ∨ g = e₄ := by
    intro g
    rw [hTdef, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  have hT2 : ∀ g, g ∈ T ↔ g = e₁ ∨ g = e₃ ∨ g = e₂ ∨ g = e₄ := by
    intro g
    rw [hT]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  have hT3 : ∀ g, g ∈ T ↔ g = e₁ ∨ g = e₄ ∨ g = e₂ ∨ g = e₃ := by
    intro g
    rw [hT]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  rw [← hTdef]
  -- the three classes
  have hclass : N.numCyclesAcross S T =
      Nat.card (N.CyclesFour S T s₁ s₂ s₃ s₄) +
        (Nat.card (N.CyclesFour S T s₁ s₃ s₂ s₄) + Nat.card (N.CyclesFour S T s₁ s₄ s₂ s₃)) := by
    rw [← natCard_or_of_disjoint
        (fun x : N.Word => N.IsCycleWord x ∧ N.crossSet S x = T ∧
          ∃ A B : N.Word, N.IsPathPair s₁ s₃ s₂ s₄ A B ∧ restrict x (N.inside S) = A + B)
        (fun x : N.Word => N.IsCycleWord x ∧ N.crossSet S x = T ∧
          ∃ A B : N.Word, N.IsPathPair s₁ s₄ s₂ s₃ A B ∧ restrict x (N.inside S) = A + B),
      ← natCard_or_of_disjoint
        (fun x : N.Word => N.IsCycleWord x ∧ N.crossSet S x = T ∧
          ∃ A B : N.Word, N.IsPathPair s₁ s₂ s₃ s₄ A B ∧ restrict x (N.inside S) = A + B)]
    · unfold numCyclesAcross
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨hx, hcs⟩
        obtain ⟨_, hbP, _, hminP, _, hdegP, _⟩ := hx.parts_of_crossSet_four h₁ h₂ h₃ h₄ hs₁
          hs₂ hs₃ hs₄ ht₁ ht₂ ht₃ ht₄ hs12 hs13 hs14 hs23 hs24 hs34 hT hcs
        rcases N.exists_pathPair_of_minimal hs12 hs13 hs14 hs23 hs24 hs34 hbP hdegP hminP with
          ⟨A, B, hAB, hW⟩ | ⟨A, B, hAB, hW⟩ | ⟨A, B, hAB, hW⟩
        · exact Or.inl ⟨hx, hcs, A, B, hAB, hW⟩
        · exact Or.inr (Or.inl ⟨hx, hcs, A, B, hAB, hW⟩)
        · exact Or.inr (Or.inr ⟨hx, hcs, A, B, hAB, hW⟩)
      · rintro (h | h | h)
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.1, h.2.1⟩
        · exact ⟨h.1, h.2.1⟩
    · -- the first class is disjoint from the other two
      rintro x ⟨_, _, A, B, hAB, hW⟩ (⟨_, _, A', B', hAB', hW'⟩ | ⟨_, _, A', B', hAB', hW'⟩)
      · exact hAB.false_of_add_eq hAB' (hW.symm.trans hW')
          (by rw [hAB.2.1.2.1]; exact Nat.one_pos)
      · exact hAB.false_of_add_eq hAB' (hW.symm.trans hW')
          (by rw [hAB.2.1.2.2.1]; exact Nat.one_pos)
    · -- the second class is disjoint from the third one
      rintro x ⟨_, _, A, B, hAB, hW⟩ ⟨_, _, A', B', hAB', hW'⟩
      exact hAB.false_of_add_eq hAB' (hW.symm.trans hW')
        (by rw [hAB.2.1.2.2.1]; exact Nat.one_pos)
  rw [hclass,
    N.natCard_cyclesFour S h₁ h₂ h₃ h₄ hs₁ hs₂ hs₃ hs₄ ht₁ ht₂ ht₃ ht₄ hs12 hs13 hs14 hs23
      hs24 hs34 ht12 ht13 ht14 ht23 ht24 ht34 hT,
    N.natCard_cyclesFour S h₁ h₃ h₂ h₄ hs₁ hs₃ hs₂ hs₄ ht₁ ht₃ ht₂ ht₄ hs13 hs12 hs14
      hs23.symm hs34 hs24 ht13 ht12 ht14 ht23.symm ht34 ht24 hT2,
    N.natCard_cyclesFour S h₁ h₄ h₂ h₃ hs₁ hs₄ hs₂ hs₃ ht₁ ht₄ ht₂ ht₃ hs14 hs12 hs13
      hs24.symm hs34.symm hs23 ht14 ht12 ht13 ht24.symm ht34.symm ht23 hT3,
    N.numPathPairsIn_swap_right (N.outside S) t₁ t₄ t₃ t₂,
    N.numPathPairsIn_swap_right (N.outside S) t₁ t₂ t₄ t₃,
    N.numPathPairsIn_swap_right (N.outside S) t₁ t₃ t₄ t₂, add_assoc]

/-! ### The number of cycles of a graph with a cut of four edges -/

/-- **Lemma 6.4 of the paper.** Let exactly four edges cross the cut: `eᵢ` joins `sᵢ ∈ S` and
`tᵢ ∉ S`, with distinct `sᵢ` and distinct `tᵢ`. Write `X` and `Y` for the two sides. Then the
number of cycles is `c(X) + c(Y)`, plus the sum over the six pairs `i < j` of the number of paths
from `sᵢ` to `sⱼ` in `X` times the number of paths from `tᵢ` to `tⱼ` in `Y`, plus the sum over the
ordered pairs of different pairings of the number of path pairs of `X` for the first pairing
times the number of path pairs of `Y` for the second pairing. -/
theorem numCycles_of_four_crossing (N : Network V E) (S : V → Prop) {e₁ e₂ e₃ e₄ : E}
    {s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : V} (hC : ∀ g, N.crosses S g → g = e₁ ∨ g = e₂ ∨ g = e₃ ∨ g = e₄)
    (h₁ : N.Joins e₁ s₁ t₁) (h₂ : N.Joins e₂ s₂ t₂) (h₃ : N.Joins e₃ s₃ t₃)
    (h₄ : N.Joins e₄ s₄ t₄) (hs₁ : S s₁) (hs₂ : S s₂) (hs₃ : S s₃) (hs₄ : S s₄) (ht₁ : ¬ S t₁)
    (ht₂ : ¬ S t₂) (ht₃ : ¬ S t₃) (ht₄ : ¬ S t₄) (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃)
    (hs14 : s₁ ≠ s₄) (hs23 : s₂ ≠ s₃) (hs24 : s₂ ≠ s₄) (hs34 : s₃ ≠ s₄) (ht12 : t₁ ≠ t₂)
    (ht13 : t₁ ≠ t₃) (ht14 : t₁ ≠ t₄) (ht23 : t₂ ≠ t₃) (ht24 : t₂ ≠ t₄) (ht34 : t₃ ≠ t₄) :
    N.numCycles = (N.sub (N.inside S)).numCycles + (N.sub (N.outside S)).numCycles +
      ((N.sub (N.inside S)).numPaths s₁ s₂ * (N.sub (N.outside S)).numPaths t₁ t₂ +
        (N.sub (N.inside S)).numPaths s₁ s₃ * (N.sub (N.outside S)).numPaths t₁ t₃ +
        (N.sub (N.inside S)).numPaths s₁ s₄ * (N.sub (N.outside S)).numPaths t₁ t₄ +
        (N.sub (N.inside S)).numPaths s₂ s₃ * (N.sub (N.outside S)).numPaths t₂ t₃ +
        (N.sub (N.inside S)).numPaths s₂ s₄ * (N.sub (N.outside S)).numPaths t₂ t₄ +
        (N.sub (N.inside S)).numPaths s₃ s₄ * (N.sub (N.outside S)).numPaths t₃ t₄) +
      ((N.sub (N.inside S)).numPathPairs s₁ s₂ s₃ s₄ *
          ((N.sub (N.outside S)).numPathPairs t₁ t₃ t₂ t₄ +
            (N.sub (N.outside S)).numPathPairs t₁ t₄ t₂ t₃) +
        (N.sub (N.inside S)).numPathPairs s₁ s₃ s₂ s₄ *
          ((N.sub (N.outside S)).numPathPairs t₁ t₂ t₃ t₄ +
            (N.sub (N.outside S)).numPathPairs t₁ t₄ t₂ t₃) +
        (N.sub (N.inside S)).numPathPairs s₁ s₄ s₂ s₃ *
          ((N.sub (N.outside S)).numPathPairs t₁ t₂ t₃ t₄ +
            (N.sub (N.outside S)).numPathPairs t₁ t₃ t₂ t₄)) := by
  have h12 : e₁ ≠ e₂ := N.ne_of_joins h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12
  have h13 : e₁ ≠ e₃ := N.ne_of_joins h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13
  have h14 : e₁ ≠ e₄ := N.ne_of_joins h₁ hs₁ ht₁ h₄ hs₄ ht₄ hs14
  have h23 : e₂ ≠ e₃ := N.ne_of_joins h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23
  have h24 : e₂ ≠ e₄ := N.ne_of_joins h₂ hs₂ ht₂ h₄ hs₄ ht₄ hs24
  have h34 : e₃ ≠ e₄ := N.ne_of_joins h₃ hs₃ ht₃ h₄ hs₄ ht₄ hs34
  have hTmem : ∀ g, N.crosses S g → g ∈ ({e₁, e₂, e₃, e₄} : Finset E) := by
    intro g hg
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    exact hC g hg
  have hnot1 : e₁ ∉ ({e₂, e₃, e₄} : Finset E) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact h12 h
    · exact h13 h
    · exact h14 h
  have hnot2 : e₂ ∉ ({e₃, e₄} : Finset E) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact h23 h
    · exact h24 h
  have hnot3 : e₃ ∉ ({e₄} : Finset E) := by
    rw [Finset.mem_singleton]
    exact h34
  rw [N.numCycles_eq_sum_across S {e₁, e₂, e₃, e₄} hTmem, Finset.sum_powerset_insert hnot1,
    Finset.sum_powerset_insert hnot2, Finset.sum_powerset_insert hnot2,
    Finset.sum_powerset_insert hnot3, Finset.sum_powerset_insert hnot3,
    Finset.sum_powerset_insert hnot3, Finset.sum_powerset_insert hnot3]
  simp only [sum_powerset_singleton, insert_empty_eq]
  rw [N.numCyclesAcross_empty S, N.numCyclesAcross_singleton S e₄,
    N.numCyclesAcross_singleton S e₃, N.numCyclesAcross_singleton S e₂,
    N.numCyclesAcross_singleton S e₁, N.numCyclesAcross_triple S h23 h24 h34,
    N.numCyclesAcross_triple S h13 h14 h34, N.numCyclesAcross_triple S h12 h14 h24,
    N.numCyclesAcross_triple S h12 h13 h23,
    N.numCyclesAcross_pair S h₃ hs₃ ht₃ h₄ hs₄ ht₄ hs34 ht34,
    N.numCyclesAcross_pair S h₂ hs₂ ht₂ h₄ hs₄ ht₄ hs24 ht24,
    N.numCyclesAcross_pair S h₂ hs₂ ht₂ h₃ hs₃ ht₃ hs23 ht23,
    N.numCyclesAcross_pair S h₁ hs₁ ht₁ h₄ hs₄ ht₄ hs14 ht14,
    N.numCyclesAcross_pair S h₁ hs₁ ht₁ h₃ hs₃ ht₃ hs13 ht13,
    N.numCyclesAcross_pair S h₁ hs₁ ht₁ h₂ hs₂ ht₂ hs12 ht12,
    N.numCyclesAcross_four S h₁ h₂ h₃ h₄ hs₁ hs₂ hs₃ hs₄ ht₁ ht₂ ht₃ ht₄ hs12 hs13 hs14 hs23
      hs24 hs34 ht12 ht13 ht14 ht23 ht24 ht34]
  simp only [numPathPairs_sub]
  ring

end Erdos1016.BoundaryTrace.Network

import Erdos1016.ExactMaximum.PathFirstEdge
import Erdos1016.ExactMaximum.NetSmallCut
import Erdos1016.ExactMaximum.NetSub
import Erdos1016.ExactMaximum.NetJoin

set_option autoImplicit false

/-!
# A shortest cycle of a cubic network

The proof of Theorem 7.1 of the paper "The maximum number of cycles in a graph of large rank"
starts with a shortest cycle `C` of a cubic multigraph of girth at least five. This file proves
the facts about `C` that the proof uses, for a cycle word `C` of a cubic network such that no
cycle has fewer edges:

* `IsCycleWord.exists_exit`: every vertex of `C` is on exactly one edge that is not in `C`;
* `IsCycleWord.no_chord`: an edge that is not in `C` does not have both ends on `C`
  (if `C` has at least three edges);
* `IsCycleWord.no_two_feet`: a vertex outside `C` is on at most one edge to `C`
  (if `C` has at least five edges).

The proofs use words only. Two vertices of `C` split `C` into two sub-words (`exists_arc`). A
chord, or two edges from an outside vertex, together with one of the two sub-words is a nonzero
word with even degrees. It contains a cycle, and one of the two cycles is shorter than `C`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace.Network

open BoundaryDecay

local instance shortestCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ### The number of edges of a word -/

omit [Fintype V] in
/-- A sub-word has at most as many edges. -/
theorem IsSubword.size_le {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) :
    size y ≤ size x := by
  unfold size
  apply Finset.card_le_card
  intro g hg
  exact Finset.mem_filter.2 ⟨Finset.mem_univ g, h g (Finset.mem_filter.1 hg).2⟩

omit [Fintype V] in
/-- The sum of two words has at most as many edges as the two words together. -/
theorem size_add_le (x y : E → Bit) : size (x + y) ≤ size x + size y := by
  unfold size
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro g hg
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  have hg' := (Finset.mem_filter.1 hg).2
  by_cases hx : x g = 0
  · right
    refine ⟨Finset.mem_univ g, fun hy => hg' ?_⟩
    show x g + y g = 0
    rw [hx, hy, add_zero]
  · exact Or.inl ⟨Finset.mem_univ g, hx⟩

omit [Fintype V] in
/-- A single edge. -/
theorem size_unitWord (f : E) : size (unitWord f : E → Bit) = 1 := by
  unfold size
  rw [Finset.card_eq_one]
  refine ⟨f, ?_⟩
  ext g
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hg⟩
    refine Classical.not_not.1 fun hne => hg ?_
    exact unitWord_apply_of_ne (fun h => hne h.symm)
  · intro hg
    refine ⟨Finset.mem_univ g, ?_⟩
    rw [hg, unitWord_apply_self]
    exact one_ne_zero

omit [Fintype V] in
/-- A word without a sub-word: the numbers of edges add up. -/
theorem size_add_of_subword {N : Network V E} {y x : N.Word} (h : N.IsSubword y x) :
    size (x + y) + size y = size x := by
  unfold size
  have hsub : (Finset.univ.filter fun g : E => y g ≠ 0) ⊆
      Finset.univ.filter fun g : E => x g ≠ 0 := by
    intro g hg
    exact Finset.mem_filter.2 ⟨Finset.mem_univ g, h g (Finset.mem_filter.1 hg).2⟩
  have heq : (Finset.univ.filter fun g : E => (x + y) g ≠ 0) =
      (Finset.univ.filter fun g : E => x g ≠ 0) \ (Finset.univ.filter fun g : E => y g ≠ 0) := by
    ext g
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨-, hg⟩
      by_cases hy : y g = 0
      · refine ⟨⟨Finset.mem_univ g, fun hx => hg ?_⟩, fun h' => h'.2 hy⟩
        show x g + y g = 0
        rw [hx, hy, add_zero]
      · exfalso
        apply hg
        show x g + y g = 0
        rw [bit_eq_one_of_ne_zero hy, bit_eq_one_of_ne_zero (h g hy)]
        exact bit_add_self 1
    · rintro ⟨⟨-, hx⟩, hy⟩
      have hy0 : y g = 0 := Classical.not_not.1 fun h' => hy ⟨Finset.mem_univ g, h'⟩
      refine ⟨Finset.mem_univ g, ?_⟩
      show x g + y g ≠ 0
      rw [hy0, add_zero]
      exact hx
  rw [heq]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- A nonzero word with even degrees has at least as many edges as a shortest cycle. -/
theorem size_le_of_even (N : Network V E) {C : N.Word}
    (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z) {Z : N.Word}
    (hZ : N.boundary Z = 0) (hne : Z ≠ 0) : size C ≤ size Z := by
  obtain ⟨z, hz, hsub⟩ := N.exists_isCycleWord_subword Z hZ hne
  exact le_trans (hmin z hz) hsub.size_le

/-! ### The exit edge of a vertex of a cycle -/

omit [Fintype V] in
/-- **The exit edge.** In a cubic network, a vertex of a cycle `C` is on exactly one edge that is
not an edge of `C`. -/
theorem IsCycleWord.exists_exit {N : Network V E} (hcubic : N.IsCubic) {C : N.Word}
    (hC : N.IsCycleWord C) {v : V} (hv : 0 < N.deg C v) :
    ∃ (f : E) (w : V), N.Joins f v w ∧ C f = 0 ∧
      ∀ g, (N.src g = v ∨ N.dst g = v) → C g = 0 → g = f := by
  have h2 : N.deg C v = 2 := by
    rcases hC.2.1 v with h | h
    · omega
    · exact h
  have h3 : N.deg (fun _ => 1) v = 3 := hcubic v
  obtain ⟨A, hA⟩ : ∃ A : Finset E, A = Finset.univ.filter
      (fun g : E => (fun _ => (1 : Bit)) g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset E, B = Finset.univ.filter
      (fun g : E => C g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)) := ⟨_, rfl⟩
  have memA : ∀ g, g ∈ A ↔ (N.src g = v ∨ N.dst g = v) := by
    intro g
    rw [hA, Finset.mem_filter]
    exact ⟨fun h => h.2.2, fun h => ⟨Finset.mem_univ g, one_ne_zero, h⟩⟩
  have memB : ∀ g, g ∈ B ↔ (C g ≠ 0 ∧ (N.src g = v ∨ N.dst g = v)) := by
    intro g
    rw [hB, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ g, h⟩⟩
  have hAc : A.card = 3 := by
    rw [hA]
    exact h3
  have hBc : B.card = 2 := by
    rw [hB]
    exact h2
  have hBA : B ⊆ A := fun g hg => (memA g).2 ((memB g).1 hg).2
  have hd : (A \ B).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hBA
    omega
  obtain ⟨f, hf⟩ := Finset.card_eq_one.1 hd
  have hfmem : f ∈ A \ B := by
    rw [hf]
    exact Finset.mem_singleton_self f
  have hfA := (Finset.mem_sdiff.1 hfmem).1
  have hfB := (Finset.mem_sdiff.1 hfmem).2
  have hfv := (memA f).1 hfA
  obtain ⟨w, hw⟩ := N.exists_joins hfv
  refine ⟨f, w, hw, Classical.not_not.1 fun h => hfB ((memB f).2 ⟨h, hfv⟩), ?_⟩
  intro g hgv hg
  have hgmem : g ∈ A \ B :=
    Finset.mem_sdiff.2 ⟨(memA g).2 hgv, fun h => ((memB g).1 h).1 hg⟩
  rw [hf] at hgmem
  exact Finset.mem_singleton.1 hgmem

/-! ### Chords and feet -/

/-- **The two arcs of a cycle.** For two vertices of a cycle `C` some sub-word of `C` has odd
degree exactly at these two vertices. -/
theorem IsCycleWord.exists_arc {N : Network V E} {C : N.Word} (hC : N.IsCycleWord C)
    {u₁ u₂ : V} (h₁ : 0 < N.deg C u₁) (h₂ : 0 < N.deg C u₂) :
    ∃ A : N.Word, N.IsSubword A C ∧ N.boundary A = unitWord u₁ + unitWord u₂ :=
  N.exists_join_of_reachable C (hC.2.2 u₁ u₂ h₁ h₂)

/-- **A shortest cycle has no chord.** Let no cycle have fewer edges than the cycle `C`, and
let `C` have at least three edges. Then an edge that is not in `C` does not have both ends on
`C`. -/
theorem IsCycleWord.no_chord {N : Network V E} {C : N.Word} (hC : N.IsCycleWord C)
    (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z) (h3 : 3 ≤ size C) {f : E}
    {u₁ u₂ : V} (hf : N.Joins f u₁ u₂) (hCf : C f = 0) (h₁ : 0 < N.deg C u₁)
    (h₂ : 0 < N.deg C u₂) : False := by
  obtain ⟨A, hA, hbA⟩ := hC.exists_arc h₁ h₂
  have key : ∀ A' : N.Word, N.IsSubword A' C → N.boundary A' = unitWord u₁ + unitWord u₂ →
      size C ≤ size A' + 1 := by
    intro A' hA' hb
    have hA'f : A' f = 0 := Classical.not_not.1 fun h => hA' f h hCf
    have hZ : N.boundary (A' + unitWord f) = 0 := by
      rw [map_add, hb, N.boundary_unitWord_of_joins hf]
      exact word_add_self _
    have hne : A' + unitWord f ≠ 0 := by
      intro h
      have h1 : (A' + unitWord f) f = 0 := congrFun h f
      have h2 : (A' + unitWord f) f = 1 := by
        show A' f + unitWord f f = 1
        rw [hA'f, unitWord_apply_self, zero_add]
      rw [h2] at h1
      exact one_ne_zero h1
    have h1 := N.size_le_of_even hmin hZ hne
    have h2 := size_add_le A' (unitWord f)
    rw [size_unitWord] at h2
    omega
  have k1 := key A hA hbA
  have k2 := key (C + A) hA.add_self (by rw [map_add, hC.boundary_eq_zero, zero_add, hbA])
  have k3 := size_add_of_subword hA
  omega

/-- **A vertex outside a shortest cycle has at most one edge to it.** Let no cycle have fewer
edges than the cycle `C`, and let `C` have at least five edges. Then two different edges at a
vertex outside `C` do not both end on `C`. -/
theorem IsCycleWord.no_two_feet {N : Network V E} {C : N.Word} (hC : N.IsCycleWord C)
    (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z) (h5 : 5 ≤ size C) {f₁ f₂ : E}
    {w u₁ u₂ : V} (hne : f₁ ≠ f₂) (hf₁ : N.Joins f₁ w u₁) (hf₂ : N.Joins f₂ w u₂)
    (hw : N.deg C w = 0) (h₁ : 0 < N.deg C u₁) (h₂ : 0 < N.deg C u₂) : False := by
  have hC₁ : C f₁ = 0 := N.eq_zero_of_deg_eq_zero hw hf₁.at_left
  have hC₂ : C f₂ = 0 := N.eq_zero_of_deg_eq_zero hw hf₂.at_left
  obtain ⟨A, hA, hbA⟩ := hC.exists_arc h₁ h₂
  have key : ∀ A' : N.Word, N.IsSubword A' C → N.boundary A' = unitWord u₁ + unitWord u₂ →
      size C ≤ size A' + 2 := by
    intro A' hA' hb
    have hA'f : A' f₁ = 0 := Classical.not_not.1 fun h => hA' f₁ h hC₁
    have hZ : N.boundary (A' + (unitWord f₁ + unitWord f₂)) = 0 := by
      rw [map_add, map_add, hb, N.boundary_unitWord_of_joins hf₁,
        N.boundary_unitWord_of_joins hf₂]
      have e1 : (unitWord u₁ : V → Bit) + unitWord u₂ +
          (unitWord w + unitWord u₁ + (unitWord w + unitWord u₂)) =
          (unitWord u₁ + unitWord u₁) + ((unitWord u₂ + unitWord u₂) +
            (unitWord w + unitWord w)) := by abel
      rw [e1, word_add_self, word_add_self, word_add_self, add_zero, add_zero]
    have hne' : A' + (unitWord f₁ + unitWord f₂) ≠ 0 := by
      intro h
      have h1 : (A' + (unitWord f₁ + unitWord f₂)) f₁ = 0 := congrFun h f₁
      have h2 : (A' + (unitWord f₁ + unitWord f₂)) f₁ = 1 := by
        show A' f₁ + (unitWord f₁ f₁ + unitWord f₂ f₁) = 1
        rw [hA'f, unitWord_apply_self, unitWord_apply_of_ne (fun h' => hne h'.symm), zero_add,
          add_zero]
      rw [h2] at h1
      exact one_ne_zero h1
    have h1 := N.size_le_of_even hmin hZ hne'
    have h2 := size_add_le A' (unitWord f₁ + unitWord f₂)
    have h3 := size_add_le (unitWord f₁ : E → Bit) (unitWord f₂)
    rw [size_unitWord, size_unitWord] at h3
    omega
  have k1 := key A hA hbA
  have k2 := key (C + A) hA.add_self (by rw [map_add, hC.boundary_eq_zero, zero_add, hbA])
  have k3 := size_add_of_subword hA
  omega

/-- The other end of the exit edge of a vertex of a shortest cycle is outside the cycle. -/
theorem IsCycleWord.deg_exit_eq_zero {N : Network V E} {C : N.Word} (hC : N.IsCycleWord C)
    (hmin : ∀ z : N.Word, N.IsCycleWord z → size C ≤ size z) (h3 : 3 ≤ size C) {f : E}
    {v w : V} (hf : N.Joins f v w) (hCf : C f = 0) (hv : 0 < N.deg C v) : N.deg C w = 0 := by
  refine Classical.not_not.1 fun h => ?_
  exact hC.no_chord hmin h3 hf hCf hv (Nat.pos_of_ne_zero h)

end Erdos1016.BoundaryTrace.Network

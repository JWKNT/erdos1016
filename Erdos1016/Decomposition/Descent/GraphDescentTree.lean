import Erdos1016.Decomposition.Descent.SplitExteriorBounds
import Erdos1016.Decomposition.Descent.AdditiveRootEstimate

set_option autoImplicit false

/-!
# Adapter from actual graph decompositions to the §9 abstract tree

Each decomposition node is translated using its actual region size, cut size,
and original exterior-component count. The local hypotheses of the abstract
root theorem are derived from the graph split lemmas and potential ledger.
-/

noncomputable section
namespace Erdos1016.Proof.GraphDescentTree

open Erdos1016.SafeCore
open Erdos1016.Proof.SplitExteriorBounds

namespace Additive
export Erdos1016.Proof.AdditiveRootEstimate
  (RegionTree size boundary exterior nodePotential sizePow hasNegativeLeaf
    LocallyValid NegativeLeavesStop LeafExteriorsPositive smallNegativeLeafCount)
end Additive

variable (G : PhysicalGraph)

/-- Replace every actual decomposition region by its §9 size/boundary/exterior
triple, retaining the binary decomposition shape. -/
def toRegionTree {U : Finset G.Vertex} :
    Decomposition G canonicalParameters U → Additive.RegionTree
  | .leaf U _ _ => .leaf U.card (cutSize G U) (G.originalExteriorComponents U)
  | .node _ _ _ l r =>
      .fork U.card (cutSize G U) (G.originalExteriorComponents U)
        (toRegionTree l) (toRegionTree r)

private theorem nodePotential_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.nodePotential (toRegionTree G t) = potential G canonicalParameters U := by
  cases t <;>
    simp [toRegionTree, Additive.nodePotential, Additive.size,
      Additive.boundary, Additive.sizePow, potential, budget, canonicalParameters,
      canonicalParameters, cutSize]

private theorem exterior_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.exterior (toRegionTree G t) = G.originalExteriorComponents U := by
  cases t <;> rfl

private theorem hasNegativeLeaf_toRegionTree_iff {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.hasNegativeLeaf (toRegionTree G t) = true ↔
      ∃ L ∈ t.leaves, potential G canonicalParameters L < 0 := by
  induction t with
  | leaf U hconn hexp =>
      change decide (Additive.nodePotential (toRegionTree G
        (.leaf U hconn hexp)) < 0) = true ↔ _
      rw [nodePotential_toRegionTree G (.leaf U hconn hexp)]
      simp [Decomposition.leaves]
  | node hconn s hcheap l r ihl ihr =>
      change (Additive.hasNegativeLeaf (toRegionTree G l) ||
        Additive.hasNegativeLeaf (toRegionTree G r)) = true ↔ _
      rw [Bool.or_eq_true, Decomposition.leaves]
      rw [ihl, ihr]
      constructor
      · rintro (⟨L, hL, hneg⟩ | ⟨L, hL, hneg⟩)
        · exact ⟨L, Finset.mem_union_left _ hL, hneg⟩
        · exact ⟨L, Finset.mem_union_right _ hL, hneg⟩
      · rintro ⟨L, hL, hneg⟩
        rcases Finset.mem_union.mp hL with hL | hL
        · exact Or.inl ⟨L, hL, hneg⟩
        · exact Or.inr ⟨L, hL, hneg⟩

private theorem hasNoNegativeLeaf_toRegionTree_iff {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.hasNegativeLeaf (toRegionTree G t) = false ↔
      ∀ L ∈ t.leaves, 0 ≤ potential G canonicalParameters L := by
  constructor
  · intro h L hL
    by_contra hnonneg
    have hneg : potential G canonicalParameters L < 0 := lt_of_not_ge hnonneg
    have htrue := (hasNegativeLeaf_toRegionTree_iff G t).2 ⟨L, hL, hneg⟩
    rw [h] at htrue
    contradiction
  · intro h
    cases hflag : Additive.hasNegativeLeaf (toRegionTree G t) with
    | false => rfl
    | true =>
        obtain ⟨L, hL, hneg⟩ := (hasNegativeLeaf_toRegionTree_iff G t).1 hflag
        exact False.elim ((not_lt_of_ge (h L hL)) hneg)

private theorem negativeLeavesStop_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) (T0 : ℕ → ℕ)
    (hstop : ∀ L ∈ t.leaves, potential G canonicalParameters L < 0 →
      L.card < T0 (G.originalExteriorComponents L)) :
    Additive.NegativeLeavesStop T0 (toRegionTree G t) := by
  induction t with
  | leaf U hconn hexp =>
      intro hneg
      exact hstop U (by simp [Decomposition.leaves])
        (by simpa only [nodePotential_toRegionTree] using hneg)
  | node hconn s hcheap l r ihl ihr =>
      exact ⟨ihl (fun L hL hneg => hstop L (Finset.mem_union_left _ hL) hneg),
        ihr (fun L hL hneg => hstop L (Finset.mem_union_right _ hL) hneg)⟩

private theorem leafExteriorsPositive_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U)
    (hpositive : ∀ L ∈ t.leaves, 1 ≤ G.originalExteriorComponents L) :
    Additive.LeafExteriorsPositive (toRegionTree G t) := by
  induction t with
  | leaf U hconn hexp =>
      simpa [toRegionTree, Additive.LeafExteriorsPositive, Decomposition.leaves]
        using hpositive U (by simp [Decomposition.leaves])
  | node hconn s hcheap l r ihl ihr =>
      exact ⟨ihl (fun L hL => hpositive L (Finset.mem_union_left _ hL)),
        ihr (fun L hL => hpositive L (Finset.mem_union_right _ hL))⟩

def smallNegativeLeaves {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) : Finset (Finset G.Vertex) :=
  t.leaves.filter (fun L => potential G canonicalParameters L < 0 ∧
    G.originalExteriorComponents L ≤ 2)

private theorem smallNegativeLeafCount_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.smallNegativeLeafCount (toRegionTree G t) =
      (smallNegativeLeaves G t).card := by
  induction t with
  | leaf U hconn hexp =>
      change (if Additive.nodePotential (toRegionTree G
        (.leaf U hconn hexp)) < 0 ∧ G.originalExteriorComponents U ≤ 2
        then 1 else 0) = _
      rw [nodePotential_toRegionTree G (.leaf U hconn hexp)]
      by_cases hsmall : potential G canonicalParameters U < 0 ∧
          G.originalExteriorComponents U ≤ 2
      · simp [smallNegativeLeaves, Decomposition.leaves, Finset.filter_singleton, hsmall]
      · simp [smallNegativeLeaves, Decomposition.leaves, Finset.filter_singleton, hsmall]
  | node hconn s hcheap l r ihl ihr =>
      have hdisj := Decomposition.separated_leaf_families s l r
      have hdisjFiltered : Disjoint
          (l.leaves.filter (fun L => potential G canonicalParameters L < 0 ∧
            G.originalExteriorComponents L ≤ 2))
          (r.leaves.filter (fun L => potential G canonicalParameters L < 0 ∧
            G.originalExteriorComponents L ≤ 2)) :=
        hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      simp only [toRegionTree, Additive.smallNegativeLeafCount,
        smallNegativeLeaves, Decomposition.leaves]
      rw [Finset.filter_union, Finset.card_union_of_disjoint hdisjFiltered]
      rw [ihl, ihr]
      dsimp [smallNegativeLeaves]

/-- Actual graph decomposition hypotheses implying the abstract finite-tree
local validity. `potential_split_le` supplies the child-potential inequality;
contact coverage and exact split updates supply exterior sum. If one child has
no negative leaf, `potential_sum_le` forces nonnegative root potential, so it
contacts the old exterior and the retained child count is monotone. -/
theorem toRegionTree_locallyValid {U : Finset G.Vertex}
    (hG : G.IsConnected) (t : Decomposition G canonicalParameters U) :
    Additive.LocallyValid (toRegionTree G t) := by
  induction t with
  | leaf U hconn hexp => trivial
  | node hconn s hcheap l r ihl ihr =>
      have hpotActual := potential_split_le G canonicalParameters hcheap
      have hpot : Additive.nodePotential (toRegionTree G l) +
          Additive.nodePotential (toRegionTree G r) ≤
          Additive.nodePotential (toRegionTree G (.node hconn s hcheap l r)) := by
        simpa only [nodePotential_toRegionTree] using hpotActual
      have hext := child_exterior_count_sum_le G hG s
      have hleftFlag := hasNegativeLeaf_toRegionTree_iff G l
      have hrightFlag := hasNegativeLeaf_toRegionTree_iff G r
      have hleftNo := hasNoNegativeLeaf_toRegionTree_iff G l
      have hrightNo := hasNoNegativeLeaf_toRegionTree_iff G r
      refine ⟨ihl, ihr, hpot, ?_, ?_, ?_⟩
      · simpa only [exterior_toRegionTree] using hext
      · intro hpairs
        have hleftNeg : Additive.hasNegativeLeaf (toRegionTree G l) = true := hpairs.1
        have hrightNeg : Additive.hasNegativeLeaf (toRegionTree G r) = false := hpairs.2
        have hL := hleftFlag.mp hleftNeg
        have hR := hrightNo.mp hrightNeg
        simpa only [exterior_toRegionTree] using
          retained_left_exterior_le_of_leaf_subtrees G canonicalParameters hG hcheap l hL r hR
      · intro hpairs
        have hleftNeg : Additive.hasNegativeLeaf (toRegionTree G l) = false := hpairs.1
        have hrightNeg : Additive.hasNegativeLeaf (toRegionTree G r) = true := hpairs.2
        have hL := hleftNo.mp hleftNeg
        have hR := hrightFlag.mp hrightNeg
        simpa only [exterior_toRegionTree] using
          retained_right_exterior_le_of_leaf_subtrees G canonicalParameters hG hcheap r hR l hL

private theorem size_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.size (toRegionTree G t) = U.card := by
  cases t <;> rfl

private theorem boundary_toRegionTree {U : Finset G.Vertex}
    (t : Decomposition G canonicalParameters U) :
    Additive.boundary (toRegionTree G t) = cutSize G U := by
  cases t <;> rfl

private theorem sizePow_monotone : Monotone Additive.sizePow := by
  intro n m hnm
  dsimp [Additive.sizePow]
  exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) (by norm_num)

private theorem sizePow_nonnegative (n : ℕ) : 0 ≤ Additive.sizePow n := by
  dsimp [Additive.sizePow]
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- Apply the abstract §9 root estimate to an actual graph decomposition.
The stopping and exceptional-leaf bounds are stated directly for the actual
terminal regions; the adapter proves all tree-local hypotheses before invoking
the abstract theorem. -/
theorem general_root_additive_inequality_of_decomposition
    {U : Finset G.Vertex} (hG : G.IsConnected)
    (t : Decomposition G canonicalParameters U) (M : ℕ) (T0 : ℕ → ℕ)
    (hnegative : ∃ L ∈ t.leaves, potential G canonicalParameters L < 0)
    (hsmall : (smallNegativeLeaves G t).card ≤ M)
    (hleafExteriorPositive : ∀ L ∈ t.leaves,
      1 ≤ G.originalExteriorComponents L)
    (hrootExteriorPositive : 1 ≤ G.originalExteriorComponents U)
    (hMpositive : 1 ≤ M)
    (hstop : ∀ L ∈ t.leaves, potential G canonicalParameters L < 0 →
      L.card < T0 (G.originalExteriorComponents L))
    (hTmono : Monotone T0) :
    Additive.sizePow U.card ≤ (cutSize G U : ℝ) / (1 / 16 : ℝ) +
      (G.originalExteriorComponents U + 2 * M : ℝ) *
        Additive.sizePow (T0 (G.originalExteriorComponents U + M)) := by
  have htreeValid := toRegionTree_locallyValid G hG t
  have htreeNegative := (hasNegativeLeaf_toRegionTree_iff G t).2 hnegative
  have htreeSmall : Additive.smallNegativeLeafCount (toRegionTree G t) ≤ M := by
    rw [smallNegativeLeafCount_toRegionTree G t]
    exact hsmall
  have htreePositive := leafExteriorsPositive_toRegionTree G t hleafExteriorPositive
  have htreeStop := negativeLeavesStop_toRegionTree G t T0 hstop
  have htreeRootExteriorPositive :
      1 ≤ Additive.exterior (toRegionTree G t) := by
    simpa only [exterior_toRegionTree] using hrootExteriorPositive
  have habstract := Erdos1016.Proof.AdditiveRootEstimate.general_root_additive_inequality
    (toRegionTree G t) M T0 htreeValid htreeNegative htreeSmall htreePositive
    htreeRootExteriorPositive hMpositive htreeStop hTmono sizePow_monotone
    sizePow_nonnegative
  simpa only [size_toRegionTree, boundary_toRegionTree, exterior_toRegionTree] using
    habstract

end Erdos1016.Proof.GraphDescentTree
end

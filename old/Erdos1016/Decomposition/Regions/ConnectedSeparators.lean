import Erdos1016.Decomposition.Regions.ComponentPartition

set_option autoImplicit false

/-!
# Nested disjoint connected separators

This proves manuscript Lemma 4.1 inside any ACTUAL induced ambient region.
There is no planarity, expansion, path-length, or degree assumption.
The cardinality bound is obtained by an injection into `Fin (s + 1)`.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyConnectedSeparatorsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

def separatorSide (U S : Finset G.Vertex) (x : G.Vertex) : Finset G.Vertex :=
  reachSet G (U \ S) x

/-- The entire removed vertex region is connected, not merely its trace. -/
structure SeparatingRegion (U : Finset G.Vertex) (x w : G.Vertex)
    (S : Finset G.Vertex) : Prop where
  subset : S ⊆ U
  connected : ConnectedRegion G S
  x_mem : x ∈ U \ S
  w_mem : w ∈ U \ S
  separates : ¬ InReach G (U \ S) x w

namespace SeparatingRegion
variable {G : PhysicalGraph} {U S : Finset G.Vertex} {x w : G.Vertex}



end SeparatingRegion

theorem reachSets_disjoint_of_not_reachable {U : Finset G.Vertex}
    {x w : G.Vertex} (hx : x ∈ U) (hw : w ∈ U)
    (hsep : ¬ InReach G U x w) :
    Disjoint (reachSet G U x) (reachSet G U w) := by
  apply Finset.disjoint_left.2
  intro v hvx hvw
  have px := ((mem_reachSet G U x v).1 hvx).2
  have pw := ((mem_reachSet G U w v).1 hvw).2
  exact hsep (px.trans pw.symm)

/-- If T is outside the x-side of S, restoring S connects that whole side
and S itself to x without using T. Every edge used is an original edge. -/
theorem move_past_removed_region {U S T : Finset G.Vertex} {x : G.Vertex}
    (hU : ConnectedRegion G U) (hS : ConnectedRegion G S) (hSU : S ⊆ U)
    (hTU : T ⊆ U) (hST : Disjoint S T) (hx : x ∈ U \ S)
    (hdis : Disjoint (separatorSide G U S x) T) :
    separatorSide G U S x ⊆ separatorSide G U T x ∧
      S ⊆ separatorSide G U T x := by
  let A := separatorSide G U S x
  have hA : A ∈ components G (U \ S) := root_component_mem G hx
  have hxA : x ∈ A := self_mem_reachSet G hx
  have hAV : A ⊆ U \ T := by
    intro v hv
    exact Finset.mem_sdiff.2
      ⟨(Finset.mem_sdiff.1 (component_subset G hA hv)).1,
        fun hvT => Finset.disjoint_left.1 hdis hv hvT⟩
  have hxT : x ∈ U \ T := hAV hxA
  have hAT : A ⊆ separatorSide G U T x := by
    intro v hv
    exact (mem_reachSet G (U \ T) x v).2
      ⟨hAV hv, ((component_connected G hA).2 x hxA v hv).mono hAV⟩
  have hSV : S ⊆ U \ T := by
    intro v hv
    exact Finset.mem_sdiff.2 ⟨hSU hv, fun hvT => Finset.disjoint_left.1 hST hv hvT⟩
  obtain ⟨a, ha, s, hs, has⟩ := (crossing_nonempty_iff G A S).1
    (component_touches_separator G hU hSU hS.1 hA)
  have hsa : s ∈ separatorSide G U T x := by
    have pa := ((mem_reachSet G (U \ T) x a).1 (hAT ha)).2
    exact (mem_reachSet G (U \ T) x s).2 ⟨hSV hs, .step pa (hSV hs) has⟩
  exact ⟨hAT, connected_subset_component G hS hSV
    (root_component_mem G hxT) hs hsa⟩

private theorem card_lt_of_subset_extra {α : Type*} [DecidableEq α]
    {A B : Finset α} (hAB : A ⊆ B) {v : α} (hvB : v ∈ B) (hvA : v ∉ A) :
    A.card < B.card := by
  have hsub : insert v A ⊆ B := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hvB
    · exact hAB hu
  have h := Finset.card_le_card hsub
  rw [Finset.card_insert_of_not_mem hvA] at h
  omega

/-- Two disjoint connected x--w separators have strictly nested x-sides.
The strict cardinal inequality is included for the subsequent finite count. -/
theorem separator_sides_strictly_nested {U S T : Finset G.Vertex}
    {x w : G.Vertex} (hU : ConnectedRegion G U)
    (hS : SeparatingRegion G U x w S) (hT : SeparatingRegion G U x w T)
    (hST : Disjoint S T) :
    (separatorSide G U S x ⊆ separatorSide G U T x ∧
      (separatorSide G U S x).card < (separatorSide G U T x).card) ∨
    (separatorSide G U T x ⊆ separatorSide G U S x ∧
      (separatorSide G U T x).card < (separatorSide G U S x).card) := by
  have hTUS : T ⊆ U \ S := by
    intro v hv
    exact Finset.mem_sdiff.2 ⟨hT.subset hv,
      fun hvS => Finset.disjoint_left.1 hST hvS hv⟩
  rcases connected_subset_or_disjoint_component G hT.connected hTUS
    (root_component_mem G hS.x_mem) with hinside | houtside
  · right
    have hxw := reachSets_disjoint_of_not_reachable G hS.x_mem hS.w_mem hS.separates
    have hWT : Disjoint (separatorSide G U S w) T := by
      apply Finset.disjoint_left.2
      intro v hvW hvT
      exact Finset.disjoint_left.1 hxw (hinside hvT) hvW
    have hrestore := move_past_removed_region G hU hS.connected hS.subset
      hT.subset hST hS.w_mem hWT
    have hxtwt := reachSets_disjoint_of_not_reachable G hT.x_mem hT.w_mem hT.separates
    have hAT : separatorSide G U T x ∈ components G (U \ T) :=
      root_component_mem G hT.x_mem
    have hATin : separatorSide G U T x ⊆ U \ S := by
      intro v hv
      refine Finset.mem_sdiff.2
        ⟨(Finset.mem_sdiff.1 (component_subset G hAT hv)).1, ?_⟩
      intro hvS
      exact Finset.disjoint_left.1 hxtwt hv (hrestore.2 hvS)
    have hsub : separatorSide G U T x ⊆ separatorSide G U S x :=
      connected_subset_component G (component_connected G hAT) hATin
        (root_component_mem G hS.x_mem)
        (self_mem_reachSet G hT.x_mem) (self_mem_reachSet G hS.x_mem)
    obtain ⟨t, ht⟩ := hT.connected.1
    have htn : t ∉ separatorSide G U T x := by
      intro htA
      exact (Finset.mem_sdiff.1 (reachSet_subset G (U \ T) x htA)).2 ht
    exact ⟨hsub, card_lt_of_subset_extra hsub (hinside ht) htn⟩
  · left
    have hrestore := move_past_removed_region G hU hS.connected hS.subset
      hT.subset hST hS.x_mem houtside.symm
    obtain ⟨s, hs⟩ := hS.connected.1
    have hsn : s ∉ separatorSide G U S x := by
      intro hsA
      exact (Finset.mem_sdiff.1 (reachSet_subset G (U \ S) x hsA)).2 hs
    exact ⟨hrestore.1, card_lt_of_subset_extra hrestore.1 (hrestore.2 hs) hsn⟩

/-- Source Lemma 4.1, with indexed separators and a concrete finite bound. -/
theorem bounded_sides_bound_separators {ι : Type*} [DecidableEq ι]
    (U : Finset G.Vertex) (hU : ConnectedRegion G U) (x w : G.Vertex)
    (F : Finset ι) (S : ι → Finset G.Vertex) (s : ℕ)
    (hsep : ∀ i ∈ F, SeparatingRegion G U x w (S i))
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hsize : ∀ i ∈ F, (separatorSide G U (S i) x).card ≤ s) :
    F.card ≤ s + 1 := by
  let f : {i // i ∈ F} → Fin (s + 1) := fun i =>
    ⟨(separatorSide G U (S i.1) x).card, Nat.lt_succ_of_le (hsize i.1 i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hcard : (separatorSide G U (S i.1) x).card =
        (separatorSide G U (S j.1) x).card := congrArg Fin.val hij
    rcases separator_sides_strictly_nested G hU (hsep i.1 i.2) (hsep j.1 j.2)
      (hdis i.1 i.2 j.1 j.2 hne) with ⟨_, hlt⟩ | ⟨_, hlt⟩ <;> omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The separated x-side is one of the components away from w. -/
theorem separatorSide_mem_offRoot {U S : Finset G.Vertex} {x w : G.Vertex}
    (h : SeparatingRegion G U x w S) :
    separatorSide G U S x ∈ offRootComponents G (U \ S) w := by
  apply (mem_offRootComponents G (U \ S) _ w).2
  exact ⟨root_component_mem G h.x_mem, fun hw =>
    h.separates ((mem_reachSet G (U \ S) x w).1 hw).2⟩

theorem separatorSide_subset_offRoot {U S : Finset G.Vertex} {x w : G.Vertex}
    (h : SeparatingRegion G U x w S) :
    separatorSide G U S x ⊆ offRootVertices G (U \ S) w := by
  intro v hv
  exact Finset.mem_biUnion.2 ⟨_, separatorSide_mem_offRoot G h, hv⟩

end Erdos1016.CycleSupply

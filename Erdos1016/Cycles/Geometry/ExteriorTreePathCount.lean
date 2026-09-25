import Erdos1016.Cycles.Geometry.WalkBlockCover
import Erdos1016.Cycles.Geometry.CubicTreeBoundary
import Erdos1016.Cycles.Geometry.CycleExternalNeighbors

set_option autoImplicit false

/-! Small cubic exterior trees attached to two disjoint cycles are bounded
 by the product of the cycles' short-block counts. The joining paths,
 block labels, and distinct endpoints are all constructed from graph data. -/
noncomputable section
namespace Erdos1016.Proof.ExteriorTreePathCount
open SimpleGraph
open ShortJoiningPaths CubicTreeBoundary
open Erdos1016.Nonbacktracking.ShortWalks
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The tree contribution to the exterior-link estimate. Every region is
 an actual induced tree, with its actual cut bounded by t; no joining-path
 family or packing/count certificate is an input. -/
theorem card_exterior_trees_le_length_blocks
    {I : Type*} [Fintype I] {a b : V}
    (C : G.Walk a a) (C' : G.Walk b b) (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hdegree : ∀ v ∈ C.support, G.degree v ≤ 3)
    (F : I → Finset V) (hFdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hFC : ∀ i x, x ∈ F i → x ∉ C.support)
    (hFC' : ∀ i x, x ∈ F i → x ∉ C'.support)
    (htree : ∀ i, (G.induce (↑(F i) : Set V)).IsTree)
    (hcubic : ∀ i v, v ∈ F i → G.degree v = 3)
    (D t q : ℕ) (hq : 0 < q) (hg : GirthGreater G D)
    (hbudget : 2 * (t + 2 * q) ≤ D)
    (hcut : ∀ i, (∑ v ∈ F i, (G.neighborFinset v \ F i).card) ≤ t)
    (hattachC : ∀ i, ∃ u ∈ C.support, ∃ x ∈ F i, G.Adj u x)
    (hattachC' : ∀ i, ∃ v ∈ C'.support, ∃ y ∈ F i, G.Adj y v) :
    Fintype.card I ≤ (C.length / q + 1) * (C'.length / q + 1) := by
  choose start hstart next hnext hadj using hattachC
  choose finish hfinish last hlast hadj' using hattachC'
  have hinj := region_attachment_starts_injective C hC hdegree F hFdisjoint
    hFC start next hstart hnext hadj
  have hpath : ∀ i, ∃ p : G.Walk (start i) (finish i),
      p.IsPath ∧ p.length ≤ t ∧
        ∀ v ∈ p.support, v = start i ∨ v = finish i ∨ v ∈ F i := by
    intro i
    have hstartout : start i ∉ F i := fun hi => hFC i _ hi (hstart i)
    have hfinishout : finish i ∉ F i := fun hi => hFC' i _ hi (hfinish i)
    have hne : start i ≠ finish i := by
      intro heq
      exact Set.disjoint_left.mp hdisjoint (hstart i) (heq ▸ hfinish i)
    obtain ⟨p, hp, hlen, hsup⟩ := exists_joining_path_through_cubic_tree G (F i)
      (htree i) (hcubic i) hstartout hfinishout hne (hnext i) (hlast i) (hadj i) (hadj' i)
    exact ⟨p, hp, hlen.le.trans (hcut i), hsup⟩
  choose path path_isPath path_length path_support using hpath
  apply card_short_joining_paths_le_length_blocks C C' hdisjoint D t q hq hg hbudget
    start finish hinj hstart hfinish path path_isPath path_length
  · intro i v hv hCv
    rcases path_support i v hv with heq | heq | hFv
    · exact heq
    · exact False.elim (Set.disjoint_left.mp hdisjoint hCv (heq ▸ hfinish i))
    · exact False.elim (hFC i v hFv hCv)
  · intro i v hv hC'v
    rcases path_support i v hv with heq | heq | hFv
    · exact False.elim (Set.disjoint_left.mp hdisjoint (heq ▸ hstart i) hC'v)
    · exact heq
    · exact False.elim (hFC' i v hFv hC'v)

end Erdos1016.Proof.ExteriorTreePathCount

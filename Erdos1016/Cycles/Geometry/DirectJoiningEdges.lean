import Erdos1016.Cycles.Geometry.WalkBlockCover
import Erdos1016.Cycles.Geometry.CycleExternalNeighbors

set_option autoImplicit false

/-! Direct edges between the two cycles satisfy the same block-pair bound
 as short exterior tree paths. They are actual ambient graph edges. -/
noncomputable section
namespace Erdos1016.Proof.ShortJoiningPaths
open SimpleGraph
open Erdos1016.Nonbacktracking.ShortWalks
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

abbrev DirectJoiningEdges {a b : V} (C : G.Walk a a) (C' : G.Walk b b) :=
  {uv : V × V // uv.1 ∈ C.support ∧ uv.2 ∈ C'.support ∧ G.Adj uv.1 uv.2}

theorem card_direct_joining_edges_le_length_blocks
    {a b : V} (C : G.Walk a a) (C' : G.Walk b b) (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hdegree : ∀ v ∈ C.support, G.degree v ≤ 3)
    (D q : ℕ) (hq : 0 < q) (hg : GirthGreater G D)
    (hbudget : 2 * (1 + 2 * q) ≤ D) :
    Fintype.card (DirectJoiningEdges C C') ≤
      (C.length / q + 1) * (C'.length / q + 1) := by
  let start : DirectJoiningEdges C C' → V := fun e => e.1.1
  let finish : DirectJoiningEdges C C' → V := fun e => e.1.2
  let p : ∀ e : DirectJoiningEdges C C', G.Walk (start e) (finish e) :=
    fun e => e.2.2.2.toWalk
  have hinj : Function.Injective start := by
    intro i j heq
    have hnext : finish i = finish j := cycle_external_neighbor_unique C hC i.2.1
      (hdegree _ i.2.1) i.2.2.2 (by simpa only [show i.1.1 = j.1.1 from heq] using j.2.2.2)
      (fun h => Set.disjoint_left.mp hdisjoint h i.2.2.1)
      (fun h => Set.disjoint_left.mp hdisjoint h j.2.2.1)
    exact Subtype.ext (Prod.ext heq hnext)
  apply card_short_joining_paths_le_length_blocks C C' hdisjoint D 1 q hq hg hbudget
    start finish hinj (fun e => e.2.1) (fun e => e.2.2.1) p
    (fun e => Walk.IsPath.of_adj e.2.2.2) (fun e => by simp [p])
  · intro i v hv hCv
    have hvs : v = start i ∨ v = finish i := by simpa [p, start, finish] using hv
    rcases hvs with heq | heq
    · exact heq
    · exact False.elim (Set.disjoint_left.mp hdisjoint hCv (heq ▸ i.2.2.1))
  · intro i v hv hC'v
    have hvs : v = start i ∨ v = finish i := by simpa [p, start, finish] using hv
    rcases hvs with heq | heq
    · exact False.elim (Set.disjoint_left.mp hdisjoint (heq ▸ i.2.1) hC'v)
    · exact heq

end Erdos1016.Proof.ShortJoiningPaths

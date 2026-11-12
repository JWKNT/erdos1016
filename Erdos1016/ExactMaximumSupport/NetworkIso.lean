import Erdos1016.ExactMaximum.NetCircuits

set_option autoImplicit false

/-!
# Relabel physical networks without fixing edge orientations

The vertex and edge maps are equivalences. Every image label has the required two ends.
The maps preserve physical degrees, paths, cycles, and cycle-space rank.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

universe u v u' v'
variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}

/-- An undirected isomorphism retains every physical label. -/
structure NetworkIso (N : Network V E) (N' : Network V' E') where
  vertices : V ≃ V'
  edges : E ≃ E'
  joins : ∀ e, N'.Joins (edges e) (vertices (N.src e)) (vertices (N.dst e))

namespace NetworkIso
variable {N : Network V E} {N' : Network V' E'} (R : NetworkIso N N')

/-- Relabel an edge word. -/
def push (x : N.Word) : N'.Word := fun e' => x (R.edges.symm e')

theorem push_apply (x : N.Word) (e : E) : R.push x (R.edges e)=x e := by
  exact congrArg x (R.edges.symm_apply_apply e)

theorem push_injective : Function.Injective R.push := by
  intro x y h
  funext e
  have hh := congrFun h (R.edges e)
  simpa only [push_apply] using hh

theorem push_zero : R.push (0 : N.Word)=0 := rfl

/-- Reverse the physical-label isomorphism. -/
def symm : NetworkIso N' N where
  vertices := R.vertices.symm
  edges := R.edges.symm
  joins e' := by
    have h := R.joins (R.edges.symm e')
    rw [R.edges.apply_symm_apply] at h
    rcases h with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · left
      constructor
      · simpa only [R.vertices.symm_apply_apply] using (congrArg R.vertices.symm hs).symm
      · simpa only [R.vertices.symm_apply_apply] using (congrArg R.vertices.symm ht).symm
    · right
      constructor
      · simpa only [R.vertices.symm_apply_apply] using (congrArg R.vertices.symm ht).symm
      · simpa only [R.vertices.symm_apply_apply] using (congrArg R.vertices.symm hs).symm

theorem symm_push_push (x : N.Word) : R.symm.push (R.push x)=x := by
  funext e
  exact congrArg x (R.edges.symm_apply_apply e)

theorem push_symm_push (x : N'.Word) : R.push (R.symm.push x)=x := by
  funext e
  exact congrArg x (R.edges.apply_symm_apply e)

theorem isSubword_push {x y : N.Word} (h : N.IsSubword y x) :
    N'.IsSubword (R.push y) (R.push x) := fun e' he' => h (R.edges.symm e') he'

variable [Fintype V] [Fintype E] [Fintype V'] [Fintype E']

omit [Fintype V] [Fintype V'] in
/-- Physical selected degrees are unchanged. -/
theorem deg_push (x : N.Word) (v : V) : N'.deg (R.push x) (R.vertices v)=N.deg x v := by
  classical
  rw [N'.deg_eq_sum,N.deg_eq_sum,← Equiv.sum_comp R.edges]
  apply Finset.sum_congr rfl
  intro e _
  rw [R.push_apply]
  rcases R.joins e with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · simp only [hs,ht,R.vertices.injective.eq_iff]
  · simp only [hs,ht,R.vertices.injective.eq_iff,or_comm]

/-- The parity boundary is unchanged at corresponding vertices. -/
theorem boundary_push (x : N.Word) (v : V) :
    N'.boundary (R.push x) (R.vertices v)=N.boundary x v := by
  rw [N'.boundary_eq_deg,N.boundary_eq_deg,R.deg_push]

theorem boundary_push_eq_zero {x : N.Word} (hx : N.boundary x=0) :
    N'.boundary (R.push x)=0 := by
  funext v'
  have h := R.boundary_push x (R.vertices.symm v')
  simpa only [R.vertices.apply_symm_apply,hx,Pi.zero_apply] using h

/-- The image of an actual physical cycle is an actual physical cycle. -/
theorem isCycleWord_push {x : N.Word} (hx : N.IsCycleWord x) :
    N'.IsCycleWord (R.push x) := by
  obtain ⟨hne,hzero,hmin⟩ := (N.isCycleWord_iff_minimal x).1 hx
  apply N'.isCycleWord_of_minimal
  · intro h
    exact hne (R.push_injective (h.trans R.push_zero.symm))
  · exact R.boundary_push_eq_zero hzero
  · intro y hy hz
    have hsub := R.symm.isSubword_push hy
    rw [R.symm_push_push] at hsub
    rcases hmin (R.symm.push y) hsub (R.symm.boundary_push_eq_zero hz) with h | h
    · left
      rw [← R.push_symm_push y,h,R.push_zero]
    · right
      rw [← R.push_symm_push y,h]

/-- A physical cycle is preserved in both directions. -/
theorem isCycleWord_push_iff (x : N.Word) :
    N'.IsCycleWord (R.push x) ↔ N.IsCycleWord x := by
  refine ⟨fun h => ?_,fun h => R.isCycleWord_push h⟩
  have hh := R.symm.isCycleWord_push h
  simpa only [R.symm_push_push] using hh

/-- The exact cycle count is unchanged. -/
theorem numCycles_eq (R : NetworkIso N N') : N'.numCycles=N.numCycles := by
  apply Eq.symm
  apply Nat.card_eq_of_bijective
    (fun x : {x : N.Word // N.IsCycleWord x} =>
      (⟨R.push x.1,R.isCycleWord_push x.2⟩ : {x : N'.Word // N'.IsCycleWord x}))
  constructor
  · intro x y h
    exact Subtype.ext (R.push_injective (congrArg Subtype.val h))
  · intro y
    refine ⟨⟨R.symm.push y.1,R.symm.isCycleWord_push y.2⟩,?_⟩
    exact Subtype.ext (R.push_symm_push y.1)

omit [Fintype V] [Fintype E] [Fintype V'] [Fintype E'] in
/-- The designated endpoint boundary is unchanged. -/
theorem pathDemand_apply (s t v : V) :
    N'.pathDemand (R.vertices s) (R.vertices t) (R.vertices v)=N.pathDemand s t v := by
  classical
  simp [Network.pathDemand,Pi.single_apply,R.vertices.injective.eq_iff]

/-- An actual path maps to an actual path with the corresponding ends. -/
theorem isPathWord_push {s t : V} {x : N.Word} (hx : N.IsPathWord s t x) :
    N'.IsPathWord (R.vertices s) (R.vertices t) (R.push x) := by
  obtain ⟨hne,hbd,hmin⟩ := (N.isPathWord_iff_minimal s t x).1 hx
  apply N'.isPathWord_of_minimal
  · exact fun h => hne (R.vertices.injective h)
  · funext v'
    have hb := R.boundary_push x (R.vertices.symm v')
    have hd := R.pathDemand_apply s t (R.vertices.symm v')
    rw [R.vertices.apply_symm_apply] at hb hd
    rw [hb,hbd,hd]
  · intro y hy hz
    have hsub := R.symm.isSubword_push hy
    rw [R.symm_push_push] at hsub
    have he := hmin (R.symm.push y) hsub (R.symm.boundary_push_eq_zero hz)
    rw [← R.push_symm_push y,he,R.push_zero]

/-- A path is preserved in both directions. -/
theorem isPathWord_push_iff (s t : V) (x : N.Word) :
    N'.IsPathWord (R.vertices s) (R.vertices t) (R.push x) ↔ N.IsPathWord s t x := by
  refine ⟨fun h => ?_,fun h => R.isPathWord_push h⟩
  have hh := R.symm.isPathWord_push h
  change N.IsPathWord (R.vertices.symm (R.vertices s))
    (R.vertices.symm (R.vertices t)) (R.symm.push (R.push x)) at hh
  simpa only [R.vertices.symm_apply_apply,R.symm_push_push] using hh

/-- Exact designated path counts are unchanged. -/
theorem numPaths_eq (s t : V) : N'.numPaths (R.vertices s) (R.vertices t)=N.numPaths s t := by
  apply Eq.symm
  apply Nat.card_eq_of_bijective
    (fun x : {x : N.Word // N.IsPathWord s t x} =>
      (⟨R.push x.1,R.isPathWord_push x.2⟩ :
        {x : N'.Word // N'.IsPathWord (R.vertices s) (R.vertices t) x}))
  constructor
  · intro x y h
    exact Subtype.ext (R.push_injective (congrArg Subtype.val h))
  · intro y
    have hpath : N.IsPathWord s t (R.symm.push y.1) := by
      have hh := R.symm.isPathWord_push y.2
      simpa only [symm,R.vertices.symm_apply_apply] using hh
    refine ⟨⟨R.symm.push y.1,hpath⟩,?_⟩
    exact Subtype.ext (R.push_symm_push y.1)

/-- The physical cycle-space rank is unchanged. -/
theorem networkRank_eq (R : NetworkIso N N') : networkRank N'=networkRank N := by
  let f : N.CycleSpace → N'.CycleSpace := fun x =>
    ⟨R.push x.1,LinearMap.mem_ker.mpr (R.boundary_push_eq_zero (LinearMap.mem_ker.mp x.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (R.push_injective (congrArg Subtype.val h))
    · intro y
      refine ⟨⟨R.symm.push y.1,
        LinearMap.mem_ker.mpr (R.symm.boundary_push_eq_zero (LinearMap.mem_ker.mp y.2))⟩,?_⟩
      exact Subtype.ext (R.push_symm_push y.1)
  have hc := Fintype.card_of_bijective hf
  rw [cycleSpace_card_network,cycleSpace_card_network] at hc
  exact (Nat.pow_right_injective (le_refl 2) hc).symm

omit [Fintype V] [Fintype V'] in
/-- Vertex-disjoint supports remain vertex-disjoint. -/
theorem vertexDisjoint_push {x y : N.Word} (h : N.VertexDisjoint x y) :
    N'.VertexDisjoint (R.push x) (R.push y) := by
  intro v'
  obtain ⟨v,rfl⟩ := R.vertices.surjective v'
  rw [R.deg_push,R.deg_push]
  exact h v

omit [Fintype V] [Fintype V'] in
/-- Vertex-disjoint supports are preserved in both directions. -/
theorem vertexDisjoint_push_iff (x y : N.Word) :
    N'.VertexDisjoint (R.push x) (R.push y) ↔ N.VertexDisjoint x y := by
  refine ⟨fun h => ?_,fun h => R.vertexDisjoint_push h⟩
  have hh := R.symm.vertexDisjoint_push h
  simpa only [R.symm_push_push] using hh

end NetworkIso
end Erdos1016.ExactMaximumSupport

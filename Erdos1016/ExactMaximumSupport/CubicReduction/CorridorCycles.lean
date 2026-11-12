import Erdos1016.ExactMaximumSupport.CubicReduction.MinimalCycles
import Erdos1016.Graph.Suppression.MarkedCorridors

set_option autoImplicit false

/-!
# Cycles compress through canonical degree-two corridors

Expansion puts one coefficient on each nonempty, disjoint corridor support.
Thus it preserves support inclusion. A proper nonzero even subword of a
compressed physical cycle would expand to a proper even subword of that cycle.
The minimal-support criterion proves connectedness of the compressed cycle.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.CubicReduction

open ShortProof

theorem route_expand_support_mono (A B : FiniteMultiGraph)
    (R : FiniteMultiGraph.EdgeDisjointRouteSystem A B) (x y : A.EdgeWord)
    (hsub : ∀ e, x e ≠ 0 → y e ≠ 0) :
    ∀ p, FiniteMultiGraph.expand A B R x p ≠ 0 →
      FiniteMultiGraph.expand A B R y p ≠ 0 := by
  classical
  intro p hp
  rw [FiniteMultiGraph.expand_apply] at hp
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  have hmem : p ∈ R.support e := by
    by_contra hn
    simp only [hn, if_false, ne_eq, not_true_eq_false] at he
  rw [if_pos hmem] at he
  rw [FiniteMultiGraph.expand_apply_of_mem_support A B R y e p hmem]
  exact hsub e he

variable (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.IsConnected) (hP : P.Nonempty)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)

def corridorPhysicalEquiv :
    (MarkedCorridors.graph G P hconn hP hdegree).CycleSpace ≃ₗ[F₂] G.CycleSpace :=
  (MarkedCorridors.cycleSpaceEquiv G P hconn hP hdegree).trans
    (CycleCore.physicalMultigraphEquiv G).symm

theorem corridorPhysicalEquiv_apply
    (x : (MarkedCorridors.graph G P hconn hP hdegree).CycleSpace) (e : G.Edge) :
    (corridorPhysicalEquiv G P hconn hP hdegree x).1 e =
      FiniteMultiGraph.expand _ _ (MarkedCorridors.routes G P hconn hP hdegree) x.1 e := rfl

theorem corridor_isCycleWord (hmax : ∀ v, G.degree v ≤ 3) (C : G.CycleWord) :
    (MarkedCorridors.graph G P hconn hP hdegree).IsCycleWord
      ((corridorPhysicalEquiv G P hconn hP hdegree).symm ⟨C.1, C.2.2.1⟩).1 := by
  let M := MarkedCorridors.graph G P hconn hP hdegree
  let L := corridorPhysicalEquiv G P hconn hP hdegree
  let c : G.CycleSpace := ⟨C.1, C.2.2.1⟩
  let y := L.symm c
  apply subcubic_isCycleWord_of_minimal M
    (MarkedCorridors.degree_le_three G P hconn hP hdegree hmax) y
  · intro hy
    have hy' : y = 0 := Subtype.ext hy
    have hc : c = 0 := by
      have he := congrArg L hy'
      simpa only [y, LinearEquiv.apply_symm_apply, map_zero] using he
    exact C.2.1 (congrArg (fun z : G.CycleSpace => z.1) hc)
  · intro z hz hsub
    have hp : (L z).1 ≠ 0 := by
      intro hp0
      have hp' : L z = 0 := Subtype.ext hp0
      have hz' : z = 0 := L.injective (by simpa only [map_zero] using hp')
      exact hz (congrArg (fun z : M.CycleSpace => z.1) hz')
    have hpc : (L z).1 = C.1 := physical_even_subword_eq G C (L z) hp (by
      intro e he
      have h := route_expand_support_mono M (CycleCore.asMultigraph G)
        (MarkedCorridors.routes G P hconn hP hdegree) z.1 y.1 hsub e he
      change (L y).1 e ≠ 0 at h
      simpa only [y, LinearEquiv.apply_symm_apply] using h)
    have hproj : L z = L y := by
      rw [show L y = c from L.apply_symm_apply c]
      exact Subtype.ext hpc
    exact congrArg (fun z : M.CycleSpace => z.1) (L.injective hproj)

def corridorCycleEmbedding (hmax : ∀ v, G.degree v ≤ 3) :
    G.CycleWord ↪ {x : (MarkedCorridors.graph G P hconn hP hdegree).EdgeWord //
      (MarkedCorridors.graph G P hconn hP hdegree).IsCycleWord x} where
  toFun C := ⟨_, corridor_isCycleWord G P hconn hP hdegree hmax C⟩
  inj' := by
    intro C D h
    have h' := congrArg Subtype.val h
    have heq := (corridorPhysicalEquiv G P hconn hP hdegree).symm.injective
      (Subtype.ext h')
    apply Subtype.ext
    exact congrArg (fun z : G.CycleSpace => z.1) heq

theorem cycleCount_le_corridor (hmax : ∀ v, G.degree v ≤ 3) :
    Fintype.card G.CycleWord ≤ (MarkedCorridors.graph G P hconn hP hdegree).numCycles := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective (corridorCycleEmbedding G P hconn hP hdegree hmax)
    (corridorCycleEmbedding G P hconn hP hdegree hmax).injective

end Erdos1016.ExactMaximumSupport.CubicReduction

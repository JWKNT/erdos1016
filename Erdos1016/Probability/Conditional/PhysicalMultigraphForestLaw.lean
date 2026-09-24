import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.PhysicalMultigraphForestLaw

open Erdos1016
open Erdos1016.Proof.CleanupSpecification

private def toFiniteMultiGraph (G : PhysicalGraph) : FiniteMultiGraph where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  src := G.src
  dst := G.dst

private theorem boundary_toFiniteMultiGraph (G : PhysicalGraph) (x : G.Word) :
    ∀ v, G.boundary x v = (toFiniteMultiGraph G).boundary x v := by
  intro v
  rfl

private def internalWord (G : PhysicalGraph) (S : Finset G.Vertex)
    (x : (toFiniteMultiGraph G).CycleSpace) : (toFiniteMultiGraph G).EdgeWord :=
  fun e => if e ∈ internalEdges (toFiniteMultiGraph G) S then x.1 e else 0

private def internalLinearForestEvent (G : PhysicalGraph) (S : Finset G.Vertex)
    (x : (toFiniteMultiGraph G).CycleSpace) : Prop :=
  IsLinearForestWord (toFiniteMultiGraph G) (internalWord G S x)

/-- The full cycle spaces use different boundary-map structures, but their
edge words and uniform measures are identified by the boundary equality. -/
def physicalToMultiCycleEquiv (G : PhysicalGraph) :
    G.CycleSpace ≃ (toFiniteMultiGraph G).CycleSpace where
  toFun x := ⟨x.1, by
    apply LinearMap.mem_ker.mpr
    funext v
    rw [← boundary_toFiniteMultiGraph G x.1 v]
    exact congrFun (LinearMap.mem_ker.mp x.2) v⟩
  invFun x := ⟨x.1, by
    apply LinearMap.mem_ker.mpr
    funext v
    rw [boundary_toFiniteMultiGraph G x.1 v]
    exact congrFun (LinearMap.mem_ker.mp x.2) v⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- Requiring the internal selected word to be a linear forest is stronger
than requiring its support to be acyclic on the physical induced region. -/
theorem regionForestProbability_le_originalForestFraction
    (G : PhysicalGraph) (S : Finset G.Vertex) :
    regionForestProbability (toFiniteMultiGraph G) S ≤
      G.originalForestFraction S := by
  classical
  let Q : G.CycleSpace → Prop := fun x =>
    ((G.selectedGraph x.1).induce (↑S : Set G.Vertex)).IsAcyclic
  let P : (toFiniteMultiGraph G).CycleSpace → Prop := internalLinearForestEvent G S
  have htransfer : G.originalForestFraction S =
      Finite.density (fun x : (toFiniteMultiGraph G).CycleSpace =>
        Q ((physicalToMultiCycleEquiv G).symm x)) := by
    unfold PhysicalGraph.originalForestFraction
    exact Finite.density_equiv (physicalToMultiCycleEquiv G) (by
      intro x
      rfl)
  have himp : ∀ x : (toFiniteMultiGraph G).CycleSpace,
      P x → Q ((physicalToMultiCycleEquiv G).symm x) := by
    intro x hx
    have hacyc :
        (selectedGraph (toFiniteMultiGraph G) (internalWord G S x)).IsAcyclic :=
      hx.2.2.1
    have hInd :
        ((selectedGraph (toFiniteMultiGraph G) (internalWord G S x)).induce
          (↑S : Set G.Vertex)).IsAcyclic := by
      intro u p hp
      let incl : (selectedGraph (toFiniteMultiGraph G)
          (internalWord G S x)).induce (↑S : Set G.Vertex) →g
            selectedGraph (toFiniteMultiGraph G) (internalWord G S x) :=
        { toFun := Subtype.val
          map_rel' := by intro a b hab; exact hab }
      have hp' : (p.map incl).IsCycle :=
        (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
      exact hacyc (p.map incl) hp'
    have hgraph :
        (selectedGraph (toFiniteMultiGraph G) (internalWord G S x)).induce
            (↑S : Set G.Vertex) =
          (G.selectedGraph x.1).induce (↑S : Set G.Vertex) := by
      ext u v
      constructor
      · intro huv
        rcases huv with ⟨hne, e, he, hend⟩
        have heI : e ∈ internalEdges (toFiniteMultiGraph G) S := by
          by_contra hnot
          simp [internalWord, hnot] at he
        have hex : x.1 e ≠ 0 := by
          simpa [internalWord, heI] using he
        refine ⟨e, hex, ?_⟩
        rcases hend with h | h
        · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
        · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩
      · intro huv
        rcases huv with ⟨e, he, hend⟩
        have hsrc : G.src e ∈ S := by
          rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · change G.src e = u.1 at hs
            exact hs.symm ▸ u.2
          · change G.src e = v.1 at hs
            exact hs.symm ▸ v.2
        have hdst : G.dst e ∈ S := by
          rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · change G.dst e = v.1 at ht
            exact ht.symm ▸ v.2
          · change G.dst e = u.1 at ht
            exact ht.symm ▸ u.2
        have heI : e ∈ internalEdges (toFiniteMultiGraph G) S := by
          simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hsrc, hdst⟩
        have he' : internalWord G S x e ≠ 0 := by
          simpa [internalWord, heI] using he
        have hne : u.1 ≠ v.1 := by
          intro heq
          rcases hend with h | h
          · exact G.noLoops e (h.1.trans (heq.trans h.2.symm))
          · exact G.noLoops e (h.1.trans (heq.symm.trans h.2.symm))
        refine ⟨hne, e, he', ?_⟩
        rcases hend with h | h
        · exact Or.inl ⟨by simpa using h.1, by simpa using h.2⟩
        · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩
    change ((G.selectedGraph ((physicalToMultiCycleEquiv G).symm x).1).induce
      (↑S : Set G.Vertex)).IsAcyclic
    have hword : ((physicalToMultiCycleEquiv G).symm x).1 = x.1 := rfl
    rw [hword, ← hgraph]
    exact hInd
  have hmeasure : Finite.density P ≤
      Finite.density (fun x : (toFiniteMultiGraph G).CycleSpace =>
        Q ((physicalToMultiCycleEquiv G).symm x)) := by
    unfold Finite.density
    apply div_le_div_of_nonneg_right
    · exact Finite.count_mono himp
    · exact Nat.cast_nonneg _
  have hprob : regionForestProbability (toFiniteMultiGraph G) S =
      Finite.density P := by
    change regionForestProbability (toFiniteMultiGraph G) S =
      Finite.density (fun x : (toFiniteMultiGraph G).CycleSpace =>
        IsLinearForestWord (toFiniteMultiGraph G) (internalWord G S x))
    unfold regionForestProbability Finite.density Finite.count internalWord
    have hcard :
        (Fintype.card (toFiniteMultiGraph G).CycleSpace : ℝ) =
          (2 : ℝ) ^ (toFiniteMultiGraph G).cycleRank := by
      exact_mod_cast (toFiniteMultiGraph G).cycleSpace_card
    rw [← hcard]
    simp [Finset.sum_boole]
  rw [hprob, htransfer]
  exact hmeasure

end Erdos1016.Proof.PhysicalMultigraphForestLaw

end

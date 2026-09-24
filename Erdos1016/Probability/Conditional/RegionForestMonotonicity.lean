import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.RegionForestMonotonicity

open Erdos1016
open Erdos1016.Proof.CleanupSpecification

private def internalWord (Γ : FiniteMultiGraph) (H : Finset Γ.Vertex)
    (x : Γ.CycleSpace) : Γ.EdgeWord :=
  fun e => if e ∈ internalEdges Γ H then x.1 e else 0

private theorem internalEdges_mono (Γ : FiniteMultiGraph)
    {K H : Finset Γ.Vertex} (hKH : K ⊆ H) :
    internalEdges Γ K ⊆ internalEdges Γ H := by
  intro e he
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨hKH he.1, hKH he.2⟩

/-- Restricting a selected multigraph word to fewer internal edges preserves
the linear-forest property. The selected simple graph is a subgraph, and the
incidence degrees can only decrease. -/
theorem isLinearForestWord_internal_mono
    (Γ : FiniteMultiGraph) {K H : Finset Γ.Vertex}
    (hKH : K ⊆ H) (x : Γ.CycleSpace)
    (hH : IsLinearForestWord Γ (internalWord Γ H x)) :
    IsLinearForestWord Γ (internalWord Γ K x) := by
  classical
  let wK := internalWord Γ K x
  let wH := internalWord Γ H x
  change IsLinearForestWord Γ wH at hH
  have hEdges := internalEdges_mono Γ hKH
  have hword (e : Γ.Edge) (he : e ∈ internalEdges Γ K) : wK e = wH e := by
    calc
      wK e = x.1 e := by simp [wK, internalWord, he]
      _ = wH e := by simp [wH, internalWord, hEdges he]
  have hselected (e : Γ.Edge) (he : wK e ≠ 0) :
      e ∈ internalEdges Γ K ∧ wK e = x.1 e := by
    by_cases hk : e ∈ internalEdges Γ K
    · exact ⟨hk, by simp [wK, internalWord, hk]⟩
    · have hz : wK e = 0 := by simp [wK, internalWord, hk]
      exact (he hz).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    have heK := (hselected e he).1
    have heH : e ∈ internalEdges Γ H := hEdges heK
    have heHnz : wH e ≠ 0 := by
      rw [← hword e heK]
      exact he
    exact hH.1 e heHnz
  · intro e f hef he he' hend
    have heK := (hselected e he).1
    have hfK := (hselected f he').1
    apply hH.2.1 e f hef
    · intro hz
      apply he
      have hzK : wK e = 0 := by rw [hword e heK]; exact hz
      exact hzK
    · intro hz
      apply he'
      have hzK : wK f = 0 := by rw [hword f hfK]; exact hz
      exact hzK
    · exact hend
  · intro v p hp
    let f : (selectedGraph Γ wK) →g (selectedGraph Γ wH) :=
      { toFun := id
        map_rel' := by
          intro a b hab
          rcases hab with ⟨hne, ⟨e, he, hend⟩⟩
          have heK := (hselected e he).1
          have heH : e ∈ internalEdges Γ H := hEdges heK
          refine ⟨hne, ⟨e, ?_, hend⟩⟩
          rw [← hword e heK]
          exact he }
    have hp' : (p.map f).IsCycle := by
      exact (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (fun _ _ h => h)).2 hp
    exact hH.2.2.1 (p.map f) hp'
  · intro v
    let SK := (Finset.univ.filter fun e : Γ.Edge => wK e ≠ 0).filter
      fun e => Γ.src e = v
    let SH := (Finset.univ.filter fun e : Γ.Edge => wH e ≠ 0).filter
      fun e => Γ.src e = v
    let TK := (Finset.univ.filter fun e : Γ.Edge => wK e ≠ 0).filter
      fun e => Γ.dst e = v
    let TH := (Finset.univ.filter fun e : Γ.Edge => wH e ≠ 0).filter
      fun e => Γ.dst e = v
    have hSK : SK ⊆ SH := by
      intro e he
      rcases Finset.mem_filter.mp he with ⟨hbase, hsrc⟩
      rcases Finset.mem_filter.mp hbase with ⟨_, heNZ⟩
      have heHnz : wH e ≠ 0 := by
        have heK := (hselected e heNZ).1
        rw [← hword e heK]
        exact heNZ
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, heHnz⟩, hsrc⟩
    have hTK : TK ⊆ TH := by
      intro e he
      rcases Finset.mem_filter.mp he with ⟨hbase, hdst⟩
      rcases Finset.mem_filter.mp hbase with ⟨_, heNZ⟩
      have heHnz : wH e ≠ 0 := by
        have heK := (hselected e heNZ).1
        rw [← hword e heK]
        exact heNZ
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, heHnz⟩, hdst⟩
    have hcards := Nat.add_le_add (Finset.card_le_card hSK) (Finset.card_le_card hTK)
    have hdegH : SH.card + TH.card ≤ 2 := by
      simpa [SH, TH, selectedDegree, Finset.filter_filter,
        and_assoc, and_left_comm, and_comm, wH] using hH.2.2.2 v
    exact hcards.trans hdegH

/-- Forest probability for an induced region is monotone under shrinking the
vertex set. High probability on a root region therefore passes to each leaf
region in a Section 9 cut tree. -/
theorem regionForestProbability_mono
    (Γ : FiniteMultiGraph) {K H : Finset Γ.Vertex} (hKH : K ⊆ H) :
    regionForestProbability Γ H ≤ regionForestProbability Γ K := by
  classical
  let A := Finset.univ.filter fun x : Γ.CycleSpace =>
    IsLinearForestWord Γ (internalWord Γ H x)
  let B := Finset.univ.filter fun x : Γ.CycleSpace =>
    IsLinearForestWord Γ (internalWord Γ K x)
  have hAB : A ⊆ B := by
    intro x hx
    have hforest := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      isLinearForestWord_internal_mono Γ hKH x hforest⟩
  have hden : 0 ≤ (2 : ℝ) ^ Γ.cycleRank := by positivity
  unfold regionForestProbability
  change (A.card : ℝ) / (2 : ℝ) ^ Γ.cycleRank ≤
    (B.card : ℝ) / (2 : ℝ) ^ Γ.cycleRank
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hAB) hden



end Erdos1016.Proof.RegionForestMonotonicity

end

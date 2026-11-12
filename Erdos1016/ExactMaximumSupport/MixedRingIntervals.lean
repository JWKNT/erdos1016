import Erdos1016.ExactMaximumSupport.MixedRingIntervalSupport

set_option autoImplicit false

/-!
# Extracting the active interval of a partial even-sector cycle

The extrema are chosen from the actual selected physical support.
No interval representation or connectedness certificate is supplied as a premise.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- An even interface has either neither label or both labels selected. -/
theorem even_interface_dichotomy (z : RingEdge T → Bit) (hz : HasEvenInterfaces T z)
    (i : Fin (k+1)) :
    (∀ b,z (interfaceEdge T i b)=0) ∨ (∀ b,z (interfaceEdge T i b)=1) := by
  have heq := even_interface_equal T z hz i
  rcases bit_cases (z (interfaceEdge T i false)) with h | h
  · left
    intro b
    cases b
    · exact h
    · exact heq.symm.trans h
  · right
    intro b
    cases b
    · exact h
    · exact heq.symm.trans h

/-- A partial even-sector cycle determines a proper interval in the opened tile order. -/
theorem exists_active_interval (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z)
    (heven : HasEvenInterfaces T z) (c : Fin (k+1))
    (hcut : ∀ b,z (interfaceEdge T c b)=0)
    (hused : ∃ q b,z (interfaceEdge T q b)≠0) :
    ∃ i j : Fin (k+1), tileLevel c i<tileLevel c j ∧ i≠j ∧
      WithinTiles T (Finset.univ.filter fun q =>
        tileLevel c i≤tileLevel c q ∧ tileLevel c q≤tileLevel c j) z ∧
      ∀ q b,z (interfaceEdge T q b)=
        if tileLevel c i≤tileLevel c q ∧ tileLevel c q<tileLevel c j then 1 else 0 := by
  classical
  let N := ring T hk twist
  let R : Finset (Vertex T) := Finset.univ.filter fun w => 0<N.deg z w
  have hne : R.Nonempty := by
    obtain ⟨e,he⟩ := hz.exists_edge
    exact ⟨N.src e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,N.deg_src_pos he⟩⟩
  obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image R (fun w => tileLevel c w.1) hne
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image R (fun w => tileLevel c w.1) hne
  have hup : 0<N.deg z u := (Finset.mem_filter.mp hu).2
  have hvp : 0<N.deg z v := (Finset.mem_filter.mp hv).2
  have hbound (w : Vertex T) (hw : 0<N.deg z w) :
      tileLevel c u.1≤tileLevel c w.1 ∧ tileLevel c w.1≤tileLevel c v.1 := by
    have hwR : w∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
    exact ⟨hmin w hwR,hmax w hwR⟩
  have hlt : tileLevel c u.1<tileLevel c v.1 := by
    obtain ⟨q,b,hq⟩ := hused
    have hqc : q≠c := by intro h; subst q; exact hq (hcut b)
    have hs := hbound _ (N.deg_src_pos hq)
    have ht := hbound _ (N.deg_dst_pos hq)
    rw [interface_src_tile] at hs
    rw [interface_dst_level T hk twist c q hqc b] at ht
    omega
  refine ⟨u.1,v.1,hlt,fun h => (ne_of_lt hlt) (congrArg (tileLevel c) h),
    within_tiles_of_extrema T hk twist z c _ _ hbound,?_⟩
  intro q b
  by_cases hqc : q=c
  · subst q
    rw [hcut]
    have hj := tileLevel_le c v.1
    rw [tileLevel_self]
    simp only [show ¬(tileLevel c u.1≤k ∧ k<tileLevel c v.1) by omega,if_false]
  · have hp := interface_pattern_of_extrema T hk twist z hz heven c hcut
      u v hup hvp hbound q hqc
    by_cases hi : tileLevel c u.1≤tileLevel c q ∧ tileLevel c q<tileLevel c v.1
    · rw [if_pos hi]
      exact hp.mpr hi b
    · rw [if_neg hi]
      rcases even_interface_dichotomy T z heven q with h | h
      · exact h b
      · exact False.elim (hi (hp.mp h))

end Erdos1016.ExactMaximumSupport.MixedTiles

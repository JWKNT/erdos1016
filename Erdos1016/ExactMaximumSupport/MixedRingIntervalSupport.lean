import Erdos1016.ExactMaximumSupport.MixedRingLinearization
import Erdos1016.ExactMaximumSupport.MixedRingFibers
import Erdos1016.ExactMaximumSupport.CycleLayerSpan

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Actual interval support after cutting an unused ring interface

A cycle's minimum and maximum occupied tile levels determine every interface label.
This derives the interval pattern from physical selected support and cut parity.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The interface after a tile starts in that tile. -/
theorem interface_src_tile (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (i : Fin (k+1)) (b : Bool) :
    ((ring T hk twist).src (interfaceEdge T i b)).1=i := by
  cases i using Fin.lastCases <;> simp [interfaceEdge,ring,ringSrc,chain,chainSrc,link,right]

/-- Away from the cut, each interface ends at the next level. -/
theorem interface_dst_level (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (c i : Fin (k+1)) (hi : i≠c) (b : Bool) :
    tileLevel c ((ring T hk twist).dst (interfaceEdge T i b)).1=tileLevel c i+1 := by
  cases i using Fin.lastCases
  · simpa [interfaceEdge,ring,ringDst,left] using tileLevel_close c hi.symm
  · rename_i j
    simpa [interfaceEdge,ring,ringDst,chain,chainDst,link,left] using tileLevel_link c j hi

/-- The two physical labels at an even interface agree. -/
theorem even_interface_equal (z : RingEdge T → Bit) (hz : HasEvenInterfaces T z)
    (i : Fin (k+1)) : z (interfaceEdge T i false)=z (interfaceEdge T i true) := by
  cases i using Fin.lastCases
  · simpa only [interfaceEdge_last] using bit_eq_of_add_eq_zero hz.2
  · rename_i j
    simpa only [interfaceEdge_castSucc] using bit_eq_of_add_eq_zero (hz.1 j)

/-- A selected threshold crossing uses the corresponding physical interface. -/
theorem crossing_is_interface_at (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (c i : Fin (k+1))
    (hcut : ∀ b,z (interfaceEdge T c b)=0)
    (e : RingEdge T) (he : z e≠0)
    (hc : (ring T hk twist).crosses
      (fun v => tileLevel c v.1≤tileLevel c i) e) :
    ∃ b,e=interfaceEdge T i b := by
  rcases e with (⟨j,e⟩ | ⟨j,b⟩) | b
  · change ¬(tileLevel c j≤tileLevel c i ↔ tileLevel c j≤tileLevel c i) at hc
    exact False.elim (hc Iff.rfl)
  · have hj : j.castSucc≠c := by
      intro h
      apply he
      have hh := hcut b
      rw [←h,interfaceEdge_castSucc] at hh
      exact hh
    have hnext := tileLevel_link c j hj
    change ¬(tileLevel c j.castSucc≤tileLevel c i ↔
      tileLevel c j.succ≤tileLevel c i) at hc
    have heq : tileLevel c j.castSucc=tileLevel c i := by omega
    have hi := tileLevel_injective c heq
    refine ⟨b,?_⟩
    rw [←hi,interfaceEdge_castSucc]
    rfl
  · have hj : c≠Fin.last k := by
      intro h
      apply he
      have hh := hcut b
      rw [h,interfaceEdge_last] at hh
      exact hh
    have hnext := tileLevel_close c hj
    change ¬(tileLevel c (Fin.last k)≤tileLevel c i ↔
      tileLevel c 0≤tileLevel c i) at hc
    have heq : tileLevel c (Fin.last k)=tileLevel c i := by omega
    have hi := tileLevel_injective c heq
    refine ⟨b,?_⟩
    rw [←hi,interfaceEdge_last]

/-- Each interface between occupied extreme levels has both labels selected. -/
theorem selected_interface_between (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z)
    (heven : HasEvenInterfaces T z) (c : Fin (k+1))
    (hcut : ∀ b,z (interfaceEdge T c b)=0)
    (u v : Vertex T) (hu : 0<(ring T hk twist).deg z u)
    (hv : 0<(ring T hk twist).deg z v) (i : Fin (k+1))
    (hui : tileLevel c u.1≤tileLevel c i) (hiv : tileLevel c i<tileLevel c v.1) :
    ∀ b,z (interfaceEdge T i b)=1 := by
  classical
  have hcard := CycleLayerSpan.two_le_crossing_card (ring T hk twist)
    (fun w => (tileLevel c w.1 : ℤ)) z hz u v hu hv (tileLevel c i)
    (Int.ofNat_le.mpr hui) (Int.ofNat_lt.mpr hiv)
  dsimp only at hcard
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<((ring T hk twist).crossSet
    (fun w => (tileLevel c w.1 : ℤ)≤(tileLevel c i : ℤ)) z).card by omega)
  have hm := (ring T hk twist).mem_crossSet.mp he
  have hcross : (ring T hk twist).crosses
      (fun w => tileLevel c w.1≤tileLevel c i) e := by
    simpa only [Network.crosses,Int.ofNat_le] using hm.1
  obtain ⟨b,rfl⟩ := crossing_is_interface_at T hk twist z c i hcut e hm.2 hcross
  have heq := even_interface_equal T z heven i
  have hfalse : z (interfaceEdge T i false)≠0 := by
    cases b
    · exact hm.2
    · rw [heq]
      exact hm.2
  have hone : z (interfaceEdge T i false)=1 := (bit_cases _).resolve_left hfalse
  intro b
  cases b
  · exact hone
  · exact heq.symm.trans hone

/-- An even cycle has exactly the interval interface pattern given by its support extrema. -/
theorem interface_pattern_of_extrema (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z)
    (heven : HasEvenInterfaces T z) (c : Fin (k+1))
    (hcut : ∀ b,z (interfaceEdge T c b)=0)
    (u v : Vertex T) (hu : 0<(ring T hk twist).deg z u)
    (hv : 0<(ring T hk twist).deg z v)
    (hbound : ∀ w,0<(ring T hk twist).deg z w →
      tileLevel c u.1≤tileLevel c w.1 ∧ tileLevel c w.1≤tileLevel c v.1)
    (i : Fin (k+1)) (hi : i≠c) :
    (∀ b,z (interfaceEdge T i b)=1) ↔
      tileLevel c u.1≤tileLevel c i ∧ tileLevel c i<tileLevel c v.1 := by
  constructor
  · intro h
    have he : z (interfaceEdge T i false)≠0 := by rw [h]; exact one_ne_zero
    have hs := hbound _ ((ring T hk twist).deg_src_pos he)
    have ht := hbound _ ((ring T hk twist).deg_dst_pos he)
    rw [interface_src_tile] at hs
    rw [interface_dst_level T hk twist c i hi false] at ht
    omega
  · intro h
    exact selected_interface_between T hk twist z hz heven c hcut u v hu hv i h.1 h.2

/-- No local tile labels occur outside the occupied level interval. -/
theorem within_tiles_of_extrema (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (c : Fin (k+1)) (a b : ℕ)
    (hbound : ∀ w,0<(ring T hk twist).deg z w →
      a≤tileLevel c w.1 ∧ tileLevel c w.1≤b) :
    WithinTiles T (Finset.univ.filter fun i => a≤tileLevel c i ∧ tileLevel c i≤b) z := by
  classical
  intro i hi
  funext e
  by_contra he
  have he' : z (Sum.inl (inner T i e))≠0 := he
  have hh := hbound _ ((ring T hk twist).deg_src_pos he')
  have hb : a≤tileLevel c i ∧ tileLevel c i≤b := hh
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)

end Erdos1016.ExactMaximumSupport.MixedTiles

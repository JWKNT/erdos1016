import Erdos1016.ExactMaximumSupport.TileRailProduct

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Rail transport of an all-interface cycle

Local matchings transport two distinct colors around the physical ring.
Identity total transport would preserve both colors on selected edges.
The actual cycle connectivity excludes that case.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Extend the actual local rail permutations by identity beyond the tile sequence. -/
def tileRail (z : RingEdge T → Bit) (n : ℕ) : Equiv.Perm Bool :=
  if h : n<k+1 then Kind.railPermutation (T ⟨n,h⟩) (ringTileWord T z ⟨n,h⟩) else 1

@[simp] theorem tileRail_at (z : RingEdge T → Bit) (i : Fin (k+1)) :
    tileRail T z i.val=Kind.railPermutation (T i) (ringTileWord T z i) := by
  simp only [tileRail,dif_pos i.isLt]

/-- Pull a vertex color back through all preceding local matchings. -/
def ringColor (z : RingEdge T → Bit) (v : Vertex T) : Bool :=
  Kind.railColor (T v.1) (railPrefix (tileRail T z) v.1.val)
    (railPrefix (tileRail T z) (v.1.val+1)) v.2

theorem ringColor_left (z : RingEdge T → Bit) (i : Fin (k+1)) (b : Bool) :
    ringColor T z (left T i b)=(railPrefix (tileRail T z) i.val).symm b :=
  Kind.railColor_left _ _ _ _

theorem ringColor_right (z : RingEdge T → Bit) (i : Fin (k+1)) (b : Bool) :
    ringColor T z (right T i b)=(railPrefix (tileRail T z) (i.val+1)).symm b := by
  change Kind.railColor (T i) (railPrefix (tileRail T z) i.val)
    (railPrefix (tileRail T z) (i.val+1)) ((T i).right b)=
    (railPrefix (tileRail T z) (i.val+1)).symm b
  simp only [railPrefix_succ,tileRail_at]
  exact Kind.railColor_right _ _ _ _

/-- When total transport is identity, every selected physical edge preserves its color. -/
theorem selected_edge_preserves_ringColor (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).boundary z=0)
    (hfull : ∀ q b,z (interfaceEdge T q b)=1)
    (hprod : twist*railPrefix (tileRail T z) (k+1)=1)
    (e : RingEdge T) (he : z e≠0) :
    ringColor T z ((ring T hk twist).src e)=ringColor T z ((ring T hk twist).dst e) := by
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
  · change Kind.railColor (T i) (railPrefix (tileRail T z) i.val)
      (railPrefix (tileRail T z) (i.val+1)) ((T i).src e)=
      Kind.railColor (T i) (railPrefix (tileRail T z) i.val)
      (railPrefix (tileRail T z) (i.val+1)) ((T i).dst e)
    simp only [railPrefix_succ,tileRail_at]
    exact Kind.selected_edge_preserves_color (T i) (ringTileWord T z i)
      (full_ring_tile_boundary T hk twist z hz hfull i) _ e he
  · change ringColor T z (right T i.castSucc b)=ringColor T z (left T i.succ b)
    rw [ringColor_right,ringColor_left]
    rfl
  · change ringColor T z (right T (Fin.last k) b)=ringColor T z (left T 0 (twist b))
    rw [ringColor_right,ringColor_left]
    change (railPrefix (tileRail T z) (k+1)).symm b=twist b
    have hh := congrArg (fun p : Equiv.Perm Bool =>
      p ((railPrefix (tileRail T z) (k+1)).symm b)) hprod
    simpa only [Equiv.Perm.mul_apply,Equiv.apply_symm_apply,Equiv.Perm.one_apply] using hh.symm

/-- An actual all-interface cycle has nonidentity total rail transport. -/
theorem full_cycle_transport_ne_one (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z)
    (hfull : ∀ q b,z (interfaceEdge T q b)=1) :
    twist*railPrefix (tileRail T z) (k+1)≠1 := by
  intro hprod
  have hecolor := selected_edge_preserves_ringColor T hk twist z hz.boundary_eq_zero hfull hprod
  have hadj (u v : Vertex T) (h : ((ring T hk twist).selectedGraph z).Adj u v) :
      ringColor T z u=ringColor T z v := by
    obtain ⟨e,he,h | h⟩ := h
    · simpa only [h.1,h.2] using hecolor e he
    · simpa only [h.1,h.2] using (hecolor e he).symm
  have hwalk {u v : Vertex T} (p : ((ring T hk twist).selectedGraph z).Walk u v) :
      ringColor T z u=ringColor T z v := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  have hpos (b : Bool) : 0<(ring T hk twist).deg z (left T 0 b) := by
    have hclose : z (Sum.inr (twist.symm b))=1 := by
      simpa only [interfaceEdge_last] using hfull (Fin.last k) (twist.symm b)
    have he : z (Sum.inr (twist.symm b))≠0 := by rw [hclose]; exact one_ne_zero
    have hh := (ring T hk twist).deg_dst_pos he
    simpa only [ring,ringDst,Equiv.apply_symm_apply] using hh
  obtain ⟨p⟩ := hz.2.2 (left T 0 false) (left T 0 true) (hpos false) (hpos true)
  have hh := hwalk p
  rw [ringColor_left,ringColor_left] at hh
  change false=true at hh
  cases hh

end Erdos1016.ExactMaximumSupport.MixedTiles

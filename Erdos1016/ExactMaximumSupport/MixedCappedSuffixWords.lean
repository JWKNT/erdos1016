import Erdos1016.ExactMaximumSupport.MixedCappedSuffix
import Erdos1016.ExactMaximumSupport.MixedRingLocalCycles

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSuffix
open BoundaryTrace BoundaryTrace.Network MixedTiles
variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Restriction to the original physical labels of one suffix tile. -/
def tileWord (z : (network T).Word) (i : Fin (k+1)) : (T i).network.Word :=
  fun e => z (Sum.inl (inner T i e))

/-- An even subword of an odd two-label state takes neither label. -/
theorem pair_subword_zero (x₀ x₁ z₀ z₁ : Bit)
    (hx : x₀+x₁=1) (hz : z₀+z₁=0)
    (h₀ : z₀≠0 → x₀≠0) (h₁ : z₁≠0 → x₁≠0) : z₀=0 ∧ z₁=0 := by
  rcases bit_cases z₀ with h | h
  · rw [h,zero_add] at hz
    exact ⟨h,hz⟩
  · have he : z₁=z₀ := (bit_eq_of_add_eq_zero hz).symm
    rw [h] at he
    have x0 : x₀=1 := (bit_cases x₀).resolve_left (h₀ (by rw [h]; exact one_ne_zero))
    have x1 : x₁=1 := (bit_cases x₁).resolve_left (h₁ (by rw [he]; exact one_ne_zero))
    rw [x0,x1,bit_add_self] at hx
    exact (zero_ne_one hx).elim

/-- Every even subword of a terminal join vanishes on all physical interfaces. -/
theorem subword_interfaces_zero (b : Bool) {x z : (network T).Word}
    (hx : (network T).boundary x=(network T).pathDemand (entry T b) (cap T))
    (hz : (network T).boundary z=0) (hsub : (network T).IsSubword z x) :
    ∀ i c,z (interface T i c)=0 := by
  intro i c
  have hh := pair_subword_zero _ _ _ _ (join_interface_odd T b x hx i)
    (even_interface_zero T z hz i) (hsub _) (hsub _)
  cases c
  · exact hh.1
  · exact hh.2

private theorem sum_at_tile (f : (i : Fin (k+1)) → (T i).Edge → Bit)
    (ends : (i : Fin (k+1)) → (T i).Edge → (T i).Vertex)
    (i : Fin (k+1)) (v : (T i).Vertex) :
    (∑ e : InnerEdge T, if (⟨e.1,ends e.1 e.2⟩ : MixedTiles.Vertex T)=⟨i,v⟩ then f e.1 e.2 else 0) =
      ∑ e : (T i).Edge, if ends i e=v then f i e else 0 := by
  classical
  rw [Fintype.sum_sigma,Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro e _
    apply if_neg
    intro h
    exact hji (congrArg Sigma.fst h)
  · simp

/-- Zero interface labels make the actual boundary local to each tile. -/
theorem boundary_at_tile (z : (network T).Word)
    (hzero : ∀ i c,z (interface T i c)=0) (i : Fin (k+1)) (v : (T i).Vertex) :
    (network T).boundary z (Sum.inl ⟨i,v⟩)=(T i).network.boundary (tileWord T z i) v := by
  classical
  have hl (j : Fin k) (b : Bool) : z (Sum.inl (Sum.inr (j,b)))=0 := by
    simpa only [interface_cast,link] using hzero j.castSucc b
  have hc (b : Bool) : z (Sum.inr b)=0 := by
    simpa only [interface_last] using hzero (Fin.last k) b
  rw [Network.boundary_apply,Network.boundary_apply]
  simp only [network,src,dst,chain,chainSrc,chainDst,
    Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [hl,hc,ite_self,Finset.sum_const_zero,add_zero,Sum.inl.injEq]
  have hs := sum_at_tile T (fun i e => z (Sum.inl (Sum.inl ⟨i,e⟩)))
      (fun i => (T i).src) i v
  have hd := sum_at_tile T (fun i e => z (Sum.inl (Sum.inl ⟨i,e⟩)))
      (fun i => (T i).dst) i v
  simp only [Sigma.eta] at hs hd
  simp only [Kind.network,tileWord,MixedTiles.inner]
  exact congrArg₂ (·+·) hs hd

/-- An even global word with zero interfaces restricts to an even local tile word. -/
theorem tile_even (z : (network T).Word) (hz : (network T).boundary z=0)
    (hzero : ∀ i c,z (interface T i c)=0) (i : Fin (k+1)) :
    (T i).network.boundary (tileWord T z i)=0 := by
  funext v
  have hh := boundary_at_tile T z hzero i v
  rw [hz,Pi.zero_apply] at hh
  exact hh.symm

/-- The unique nonzero even square word selects all four of its physical labels. -/
theorem square_even_eq_one (z : Kind.square.network.Word)
    (hz : Kind.square.network.boundary z=0) (hne : z≠0) : z=fun _ => 1 := by
  have hone : Kind.square.network.boundary (fun _ => 1)=0 := by
    funext v
    rcases v with ⟨side,b⟩
    cases side
    · rw [square_boundary_left]; exact bit_add_self 1
    · rw [square_boundary_right]; exact bit_add_self 1
  apply nonzero_even_tile_unique Kind.square hz hone hne
  intro he
  have hh := congrFun he (false,false)
  exact (one_ne_zero : (1:Bit)≠0) hh

end Erdos1016.ExactMaximumSupport.MixedCappedSuffix

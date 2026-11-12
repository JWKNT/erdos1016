import Erdos1016.ExactMaximumSupport.ThirdPortReduction

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Bridge reduction with the third port retained

Every subnetwork keeps its original physical labels. Above half capacity for
both tested pairs, a bridge lies after the third port: the first shore is
again a full three-pole, and both path counts have the same full second factor.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortBridges
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance thirdPortBridgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The actual bridge cut and the connections in both physical shores. -/
theorem bridge_cut {s t : V} (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t)
    (hmany : 2 ^ networkRank N < 2 * N.numPaths s t) {e : E}
    (hbr : ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0) :
    ∃ (S : V → Prop) (x y : V), N.Joins e x y ∧ S x ∧ ¬ S y ∧
      (∀ g, N.crosses S g → g = e) ∧ S s ∧ ¬ S t ∧ x ≠ s ∧ y ≠ t ∧
      (∀ z, S z → 0 < N.deg (fun _ => 1) z →
        (N.sub (N.inside S)).graph.Reachable s z) ∧
      (∀ z, ¬ S z → 0 < N.deg (fun _ => 1) z →
        (N.sub (N.outside S)).graph.Reachable t z) := by
  have hdeg := hN.deg_zero_or_two_le
  have hone : (fun _ : E => (1 : Bit)) e ≠ 0 := one_ne_zero
  have hspos : 0 < N.deg (fun _ => 1) s := by change _ = 2 at hs; omega
  have htpos : 0 < N.deg (fun _ => 1) t := by change _ = 2 at ht; omega
  let S := N.sideOf e s
  have hC : ∀ g, N.crosses S g → g = e := fun _ h => N.eq_of_crosses_sideOf e s h
  have hSs : S s := N.sideOf_self e s
  have hends : ∃ x y : V, N.Joins e x y ∧ S x ∧ ¬ S y := by
    have he0 : N.Joins e (N.src e) (N.dst e) := Or.inl ⟨rfl,rfl⟩
    have hnot : ¬ (S (N.src e) ∧ S (N.dst e)) := by
      rintro ⟨h1,h2⟩
      exact N.not_reachable_of_bridge hbr he0 (h1.symm.trans h2)
    by_cases h1 : S (N.src e)
    · exact ⟨N.src e,N.dst e,he0,h1,fun h2 => hnot ⟨h1,h2⟩⟩
    · by_cases h2 : S (N.dst e)
      · exact ⟨N.dst e,N.src e,he0.symm,h2,h1⟩
      · exfalso
        have hclosed : ∀ g, S (N.src g) ↔ S (N.dst g) := by
          intro g
          by_cases hg : g = e
          · rw [hg]
            exact ⟨fun h => (h1 h).elim,fun h => (h2 h).elim⟩
          · exact N.sideOf_iff_of_ne e s hg
        exact h1 (N.mem_of_reachable_of_closed S hclosed
          (hN.2 s (N.src e) hspos (N.deg_src_pos hone)) hSs)
  obtain ⟨x,y,he,hx,hy⟩ := hends
  have hSt : ¬ S t := by
    intro hSt
    have hh := N.two_mul_numPaths_le_of_same_side hdeg S he hx hy hC hSs hSt
    omega
  have hC' : ∀ g, N.crosses (fun z => ¬ S z) g → g = e :=
    fun g hg => hC g ((N.crosses_not_iff S g).1 hg)
  have hxs : x ≠ s := by
    intro h
    have hh := N.two_mul_numPaths_le_of_bridge_at hdeg S (h ▸ he) hSs hy hC
      (le_of_eq hs) hSt
    omega
  have hyt : y ≠ t := by
    intro h
    have hh := N.two_mul_numPaths_le_of_bridge_at hdeg (fun z => ¬ S z)
      (h ▸ he.symm) hSt (not_not.mpr hx) hC' (le_of_eq ht) (not_not.mpr hSs)
    rw [ExactMaximum.numPaths_symm N t s] at hh
    omega
  have hin : ∀ z, S z → 0 < N.deg (fun _ => 1) z →
      (N.sub (N.inside S)).graph.Reachable s z :=
    fun z hz _ => N.reachable_inside_sideOf e s hz
  have houtside : ∀ g, N.inside (N.sideOf e y) g → N.outside S g := by
    intro g hg
    have hno : ∀ z, N.sideOf e y z → ¬ S z := by
      intro z hz hSz
      exact hy (hSz.trans hz.symm)
    exact ⟨hno _ hg.1,hno _ hg.2⟩
  have hout_y : ∀ z, ¬ S z → 0 < N.deg (fun _ => 1) z →
      (N.sub (N.outside S)).graph.Reachable y z := by
    intro z hz hzpos
    rcases N.sideOf_or_sideOf he s hx (hN.2 s z hspos hzpos) with h | h
    · exact (hz h).elim
    · exact N.reachable_sub_mono houtside (N.reachable_inside_sideOf e y h)
  exact ⟨S,x,y,he,hx,hy,hC,hSs,hSt,hxs,hyt,hin,
    fun z hz hzpos => (hout_y t hSt htpos).symm.trans (hout_y z hz hzpos)⟩

omit [Fintype V] in
/-- Cutting at a cubic bridge end creates precisely one new port in that shore. -/
theorem weak_pole_side (hN : N.IsWeakPole) (S : V → Prop) {e : E} {x y a : V}
    (he : N.Joins e x y) (hx : S x) (hy : ¬ S y)
    (hC : ∀ g, N.crosses S g → g = e) (hx3 : N.deg (fun _ => 1) x = 3)
    (hin : ∀ z, S z → 0 < N.deg (fun _ => 1) z →
      (N.sub (N.inside S)).graph.Reachable a z) :
    (N.sub (N.inside S)).IsWeakPole ∧
      ∀ z, (N.sub (N.inside S)).IsPort z ↔ z = x ∨ S z ∧ N.IsPort z := by
  have hdx : (N.sub (N.inside S)).deg (fun _ => 1) x = 2 := by
    have hh := N.deg_inside_of_one_crossing S he hx hy hC hx
    rw [if_pos rfl,hx3] at hh
    omega
  have heq : ∀ z, S z → z ≠ x →
      (N.sub (N.inside S)).deg (fun _ => 1) z = N.deg (fun _ => 1) z := by
    intro z hz hzx
    have hh := N.deg_inside_of_one_crossing S he hx hy hC hz
    simpa only [if_neg hzx,add_zero] using hh
  have hmem : ∀ z, 0 < (N.sub (N.inside S)).deg (fun _ => 1) z → S z := by
    intro z hz
    by_contra h
    rw [N.deg_inside_of_not_mem S h] at hz
    omega
  have hle : ∀ z, (N.sub (N.inside S)).deg (fun _ => 1) z ≤ N.deg (fun _ => 1) z := by
    intro z
    by_cases hz : S z
    · have hh := N.deg_inside_of_one_crossing S he hx hy hC hz
      omega
    · rw [N.deg_inside_of_not_mem S hz]
      exact Nat.zero_le _
  constructor
  · constructor
    · intro z
      by_cases hz : S z
      · by_cases hzx : z = x
        · exact Or.inr (Or.inl (hzx ▸ hdx))
        · rw [heq z hz hzx]
          exact hN.1 z
      · exact Or.inl (N.deg_inside_of_not_mem S hz)
    · intro u w hu hw
      exact (hin u (hmem u hu) (lt_of_lt_of_le hu (hle u))).symm.trans
        (hin w (hmem w hw) (lt_of_lt_of_le hw (hle w)))
  · intro z
    constructor
    · intro hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · have hSz := hmem z (by change _ = 2 at hz; omega)
        exact Or.inr ⟨hSz,by change _ = 2 at hz ⊢; rwa [heq z hSz hzx] at hz⟩
    · rintro (rfl | ⟨hz,hport⟩)
      · exact hdx
      · by_cases hzx : z = x
        · exact hzx ▸ hdx
        · change _ = 2
          rw [heq z hz hzx]
          exact hport

/-- Fullness of a product forces fullness in each positive-capacity factor. -/
theorem full_factors (p q A B : ℕ) (hp : p ≤ A) (hq : q ≤ B)
    (hA : 0 < A) (hB : 0 < B) (heq : p*q = A*B) : p = A ∧ q = B := by
  constructor
  · have hh := Nat.mul_le_mul_left p hq
    nlinarith
  · have hh := Nat.mul_le_mul_right q hp
    nlinarith

/-- The exact data of a bridge step on the original three-pole. -/
structure BridgeStep (s t v : V) (e : E) (S : V → Prop) (x y : V) : Prop where
  joins : N.Joins e x y
  left_end : S x
  right_end : ¬ S y
  only_cross : ∀ g, N.crosses S g → g = e
  left_s : S s
  left_v : S v
  right_t : ¬ S t
  sx_ne : s ≠ x
  xv_ne : x ≠ v
  yt_ne : y ≠ t
  left_pole : (N.sub (N.inside S)).IsWeakPole
  left_port_s : (N.sub (N.inside S)).IsPort s
  left_port_x : (N.sub (N.inside S)).IsPort x
  left_port_v : (N.sub (N.inside S)).IsPort v
  left_only : ∀ z, (N.sub (N.inside S)).IsPort z → z = s ∨ z = x ∨ z = v
  right_pole : (N.sub (N.outside S)).IsWeakTwoPole y t
  left_full : (N.sub (N.inside S)).IsFullPair s x
  right_full : (N.sub (N.outside S)).IsFullPair y t
  rank_eq : networkRank N = networkRank (N.sub (N.inside S)) +
    networkRank (N.sub (N.outside S))
  left_rank_pos : 0 < networkRank (N.sub (N.inside S))
  right_rank_pos : 0 < networkRank (N.sub (N.outside S))
  paths_st : N.numPaths s t = (N.sub (N.inside S)).numPaths s x *
    (N.sub (N.outside S)).numPaths y t
  paths_vt : N.numPaths v t = (N.sub (N.inside S)).numPaths v x *
    (N.sub (N.outside S)).numPaths y t

/-- Either the third tested pair already loses one half, or the bridge gives
an actual smaller three-pole and a common full factor for both path counts. -/
theorem bridge_step_or_half (s t v : V) (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t) (hv : N.IsPort v)
    (honly : ∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v)
    (hfull : N.IsFullPair s t) {e : E}
    (hbr : ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0) :
    2 * N.numPaths v t ≤ 2 ^ networkRank N ∨
      ∃ (S : V → Prop) (x y : V), BridgeStep N s t v e S x y := by
  by_cases hhalf : 2 * N.numPaths v t ≤ 2 ^ networkRank N
  · exact Or.inl hhalf
  right
  have hpos := Nat.two_pow_pos (networkRank N)
  have hfull' : N.numPaths s t = 2 ^ networkRank N := hfull
  have hmany : 2 ^ networkRank N < 2 * N.numPaths s t := by omega
  obtain ⟨S,x,y,he,hx,hy,hC,hSs,hSt,hxs,hyt,hin,hout⟩ :=
    bridge_cut N hN hs ht hmany hbr
  have hdeg := hN.deg_zero_or_two_le
  have hC' : ∀ g, N.crosses (fun z => ¬ S z) g → g = e :=
    fun g hg => hC g ((N.crosses_not_iff S g).1 hg)
  have hSv : S v := by
    by_contra hv'
    exact hhalf (N.two_mul_numPaths_le_of_same_side hdeg (fun z => ¬ S z)
      he.symm hy (not_not.mpr hx) hC' hv' hSt)
  have hxv : x ≠ v := by
    intro h
    exact hhalf (N.two_mul_numPaths_le_of_bridge_at hdeg S (h ▸ he) hSv hy hC
      (le_of_eq hv) hSt)
  have hx3 : N.deg (fun _ => 1) x = 3 := by
    rcases hN.1 x with h | h | h
    · have hp := N.isPathWord_unitWord he
      have hxpos := hp.2.1
      have hle := (show N.IsSubword (unitWord e) (fun _ => 1) from fun _ _ => one_ne_zero).deg_le x
      omega
    · rcases honly x h with h | h | h
      · exact (hxs h).elim
      · exact (hSt (h ▸ hx)).elim
      · exact (hxv h).elim
    · exact h
  have hy3 : N.deg (fun _ => 1) y = 3 := by
    rcases hN.1 y with h | h | h
    · have hp := N.isPathWord_unitWord he
      have hypos := hp.2.2.1
      have hle := (show N.IsSubword (unitWord e) (fun _ => 1) from fun _ _ => one_ne_zero).deg_le y
      omega
    · rcases honly y h with h | h | h
      · exact (hy (h ▸ hSs)).elim
      · exact (hyt h).elim
      · exact (hy (h ▸ hSv)).elim
    · exact h
  obtain ⟨hL,hportsL⟩ := weak_pole_side N hN S he hx hy hC hx3 hin
  obtain ⟨hR,hportsR⟩ := weak_pole_side N hN (fun z => ¬ S z) he.symm hy
    (not_not.mpr hx) hC' hy3 hout
  have hLs : (N.sub (N.inside S)).IsPort s := (hportsL s).2 (Or.inr ⟨hSs,hs⟩)
  have hLx : (N.sub (N.inside S)).IsPort x := (hportsL x).2 (Or.inl rfl)
  have hLv : (N.sub (N.inside S)).IsPort v := (hportsL v).2 (Or.inr ⟨hSv,hv⟩)
  have hLonly : ∀ z, (N.sub (N.inside S)).IsPort z → z = s ∨ z = x ∨ z = v := by
    intro z hz
    rcases (hportsL z).1 hz with h | ⟨hSz,hport⟩
    · exact Or.inr (Or.inl h)
    · rcases honly z hport with h | h | h
      · exact Or.inl h
      · exact (hSt (h ▸ hSz)).elim
      · exact Or.inr (Or.inr h)
  have hRpole : (N.sub (N.outside S)).IsWeakTwoPole y t := by
    refine ⟨hR,(hportsR y).2 (Or.inl rfl),(hportsR t).2 (Or.inr ⟨hSt,ht⟩),hyt,?_⟩
    intro z hz
    rcases (hportsR z).1 hz with h | ⟨hSz,hport⟩
    · exact Or.inl h
    · rcases honly z hport with h | h | h
      · exact (hSz (h ▸ hSs)).elim
      · exact Or.inr h
      · exact (hSz (h ▸ hSv)).elim
  have hce := N.crosses_of_joins he hx hy
  have hr := N.networkRank_of_one_crossing S hC hce
  have hpst := N.numPaths_of_one_crossing S he hx hy hC hSs hSt hxs.symm hyt
  have hpvt := N.numPaths_of_one_crossing S he hx hy hC hSv hSt hxv.symm hyt
  have hfactors := full_factors _ _ _ _ ((N.sub (N.inside S)).numPaths_le_two_pow s x)
    ((N.sub (N.outside S)).numPaths_le_two_pow y t) (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    (by rw [← hpst,← pow_add,← hr]; exact hfull')
  exact ⟨S,x,y,⟨he,hx,hy,hC,hSs,hSv,hSt,hxs.symm,hxv,hyt,hL,hLs,hLx,hLv,hLonly,
    hRpole,hfactors.1,hfactors.2,hr,
    N.rank_side_pos_of_one_crossing hdeg S he hx hy hC,
    N.rank_side_pos_of_one_crossing hdeg (fun z => ¬ S z) he.symm hy
      (not_not.mpr hx) hC',hpst,hpvt⟩⟩

end Erdos1016.ExactMaximumSupport.ThirdPortBridges

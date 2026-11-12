import Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCapArithmetic
import Erdos1016.ExactMaximumSupport.Shortening.TreeCapShares
import Erdos1016.ExactMaximum.Remaining
import Erdos1016.ExactMaximumSupport.GapInput

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! An alternate actual four-cut theorem. The three tree-cap bounds replace
all low-state, rank-one and 9/16 pole-cycle estimates. Only the structural,
counting and renumbering helpers of the frozen FourCut module are reused;
its four-cut theorem and four-case arithmetic endpoint are not used. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap
open ExactMaximum FourCutArithmeticProof
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual normalized cap inequality, with a uniform rank threshold. -/
def CapWith (B : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B≤networkRank N →
    ∀ (p : Fin 4 → V) (α : Fin 3),
      (N.numCycles : ℝ)/2^networkRank N+pathSum (pathShare N p)+
        forestSum (pairShare N p)-pairShare N p α≤4001/1000

/-- The first shore is large; the opposite cyclic shore is allowed bounded rank. -/
theorem numCycles_le_inside (hgap : GapStatement) {K B R : ℕ}
    (hK : 1≤K) (hF : FewCyclesWith K) (hcap : CapWith B) (hring : RingCaseWith R)
    {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop,N.IsCyclicCut S → 4≤N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S=4) (hcyc : N.IsCyclicCut S) (hR : R≤networkRank N)
    (hk : max B (4000000*K)≤networkRank (N.sub (N.inside S))) :
    N.numCycles≤horakKim (networkRank N) := by
  obtain ⟨e,x,y,hfc⟩ := N.exists_isFourCut hN hcubic hmin S hS hcyc
  obtain ⟨n01,n02,n03,n12,n13,n23⟩ := fin4_distinct
  have hr := hfc.rank
  have hpow : 4*(2^networkRank (N.sub (N.outside S))*
      2^networkRank (N.sub (N.inside S)))=2^(networkRank N-1) := by
    have hh : networkRank N-1=2+(networkRank (N.sub (N.outside S))+
        networkRank (N.sub (N.inside S))) := by omega
    rw [hh,pow_add,pow_add]
    norm_num
  by_cases hlt : N.numCycles<2^(networkRank N-1)
  · exact hlt.le.trans (two_pow_le_horakKim (networkRank N) (by omega))
  have hkpow : 4000000*K≤2^networkRank (N.sub (N.inside S)) :=
    le_trans (le_trans (le_max_right _ _) hk) Nat.lt_two_pow_self.le
  have hB : B≤networkRank (N.sub (N.inside S)) := (le_max_left _ _).trans hk
  have hXpos : 1≤networkRank (N.sub (N.outside S)) := by
    have h1 := (N.sub (N.outside S)).numCycles_lt_two_pow
    have h2 := hcyc.2
    refine Nat.le_of_not_lt fun h0 => ?_
    have h3 : networkRank (N.sub (N.outside S))=0 := by omega
    rw [h3,pow_zero] at h1
    omega
  have hX := fourState_of_pole hgap (N.sub (N.outside S)) hfc.pole_out y hfc.inj_y hfc.port_out
  have hY := largeState_of_pole hgap hF (N.sub (N.inside S)) hfc.pole_in x hfc.inj_x
    hfc.port_in hkpow
  have hDX : (0 : ℝ)<2^networkRank (N.sub (N.outside S)) := by positivity
  have hDY : (0 : ℝ)<2^networkRank (N.sub (N.inside S)) := by positivity
  have h2X : (2 : ℝ)≤2^networkRank (N.sub (N.outside S)) := by
    have h : 2≤2^networkRank (N.sub (N.outside S)) := Nat.le_self_pow (by omega) 2
    exact_mod_cast h
  have h1000 : (1000 : ℝ)≤2^networkRank (N.sub (N.inside S)) := by
    have h : 1000≤2^networkRank (N.sub (N.inside S)) := by omega
    exact_mod_cast h
  have hcX1 : ((N.sub (N.outside S)).numCycles : ℝ)/
      2^networkRank (N.sub (N.outside S))<1 := by
    rw [div_lt_one hDX]
    exact_mod_cast (N.sub (N.outside S)).numCycles_lt_two_pow
  have he : ((N.sub (N.outside S)).numCycles : ℝ)/
      2^networkRank (N.sub (N.outside S))/2^networkRank (N.sub (N.inside S))≤1/1000 := by
    apply (div_le_iff₀ hDY).mpr
    linarith
  have hz : 0≤((N.sub (N.inside S)).numCycles : ℝ)/
      2^networkRank (N.sub (N.inside S)) := div_nonneg (Nat.cast_nonneg _) hDY.le
  have hq : ((N.sub (N.inside S)).numCycles : ℝ)/
      2^networkRank (N.sub (N.inside S))/2^networkRank (N.sub (N.outside S))≤
      (((N.sub (N.inside S)).numCycles : ℝ)/2^networkRank (N.sub (N.inside S)))/2 := by
    apply (div_le_iff₀ hDX).mpr
    have hh := mul_le_mul_of_nonneg_left h2X (div_nonneg hz (by norm_num : (0 : ℝ)≤2))
    linarith
  have hC' : ∀ g,N.crosses S g → g=e 0 ∨ g=e 1 ∨ g=e 2 ∨ g=e 3 := by
    intro g hg
    obtain ⟨m,rfl⟩ := hfc.crosses g hg
    fin_cases m
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hcount := N.numCycles_of_four_crossing S hC' (hfc.joins 0) (hfc.joins 1) (hfc.joins 2)
    (hfc.joins 3) (hfc.mem 0) (hfc.mem 1) (hfc.mem 2) (hfc.mem 3) (hfc.not_mem 0)
    (hfc.not_mem 1) (hfc.not_mem 2) (hfc.not_mem 3) (hfc.inj_x.ne n01) (hfc.inj_x.ne n02)
    (hfc.inj_x.ne n03) (hfc.inj_x.ne n12) (hfc.inj_x.ne n13) (hfc.inj_x.ne n23)
    (hfc.inj_y.ne n01) (hfc.inj_y.ne n02) (hfc.inj_y.ne n03) (hfc.inj_y.ne n12)
    (hfc.inj_y.ne n13) (hfc.inj_y.ne n23)
  have hreal := four_cut_count (N.sub (N.outside S)) (N.sub (N.inside S)) x y N.numCycles hcount
  have htotal : 4≤((N.sub (N.outside S)).numCycles : ℝ)/
      2^networkRank (N.sub (N.outside S))/2^networkRank (N.sub (N.inside S))+
      ((N.sub (N.inside S)).numCycles : ℝ)/2^networkRank (N.sub (N.inside S))/
        2^networkRank (N.sub (N.outside S))+
      (pairSum (pathShare (N.sub (N.outside S)) y) (pathShare (N.sub (N.inside S)) x)+
        pairingSum (pairShare (N.sub (N.outside S)) y) (pairShare (N.sub (N.inside S)) x)) := by
    have hn : 4*(2^networkRank (N.sub (N.outside S))*
        2^networkRank (N.sub (N.inside S)))≤N.numCycles := by
      rw [hpow]
      exact le_of_not_gt hlt
    have hh : (4 : ℝ)*(2^networkRank (N.sub (N.outside S))*
        2^networkRank (N.sub (N.inside S)))≤N.numCycles := by exact_mod_cast hn
    rw [hreal] at hh
    exact (mul_le_mul_right (mul_pos hDX hDY)).mp hh
  obtain ⟨i,j,k,l,hd,hx1,hx2,hx3,hx4,ha1,ha2,ha3,ha4⟩ :=
    FourCutTreeCapArithmetic.common_full_cross_of_tree_caps hX hY _ _ _ he hq
      (hcap V _ (N.sub (N.inside S)) hB x) htotal
  obtain ⟨hij,hik,hil,hjk,hjl,hkl⟩ := hd
  have hσ := renumber_injective i j k l hij hik hil hjk hjl hkl
  refine hring V E N hN hcubic hmin hR S (e ∘ renumber i j k l) (x ∘ renumber i j k l)
    (y ∘ renumber i j k l) ?_ (fun m => hfc.joins _) (fun m => hfc.mem _)
    (fun m => hfc.not_mem _) (hfc.inj_x.comp hσ) (hfc.inj_y.comp hσ) hfc.pole_in hfc.pole_out ?_
  · intro g hg
    obtain ⟨m₀,hm₀⟩ := hfc.crosses g hg
    obtain ⟨n,rfl⟩ := renumber_surjective i j k l hij hik hil hjk hjl hkl m₀
    exact ⟨n,hm₀⟩
  · intro m n hm hn
    show (N.sub (N.inside S)).IsFullPair (x (renumber i j k l m)) (x (renumber i j k l n)) ∧
      (N.sub (N.outside S)).IsFullPair (y (renumber i j k l m)) (y (renumber i j k l n))
    rcases renumber_low i j k l m hm with h1|h1 <;>
      rcases renumber_high i j k l n hn with h2|h2 <;> rw [h1,h2]
    · exact ⟨isFullPair_of_pathShare_eq_one _ x ha1,isFullPair_of_pathShare_eq_one _ y hx1⟩
    · exact ⟨isFullPair_of_pathShare_eq_one _ x ha2,isFullPair_of_pathShare_eq_one _ y hx2⟩
    · exact ⟨isFullPair_of_pathShare_eq_one _ x ha3,isFullPair_of_pathShare_eq_one _ y hx3⟩
    · exact ⟨isFullPair_of_pathShare_eq_one _ x ha4,isFullPair_of_pathShare_eq_one _ y hx4⟩

/-- Choose the large side of the actual four-cut. -/
theorem numCycles_le (hgap : GapStatement) {K B R : ℕ}
    (hK : 1≤K) (hF : FewCyclesWith K) (hcap : CapWith B) (hring : RingCaseWith R)
    {V E : Type} [Fintype V] [Fintype E] (N : Network V E)
    (hN : N.graph.Connected) (hcubic : N.IsCubic)
    (hmin : ∀ S : V → Prop,N.IsCyclicCut S → 4≤N.cutSize S) (S : V → Prop)
    (hS : N.cutSize S=4) (hcyc : N.IsCyclicCut S)
    (hR : max R (2*max B (4000000*K)+3)≤networkRank N) :
    N.numCycles≤horakKim (networkRank N) := by
  obtain ⟨e,x,y,hfc⟩ := N.exists_isFourCut hN hcubic hmin S hS hcyc
  have hr := hfc.rank
  have hR1 : R≤networkRank N := (le_max_left _ _).trans hR
  have hR2 : 2*max B (4000000*K)+3≤networkRank N := (le_max_right _ _).trans hR
  by_cases hk : max B (4000000*K)≤networkRank (N.sub (N.inside S))
  · exact numCycles_le_inside hgap hK hF hcap hring N hN hcubic hmin S hS hcyc hR1 hk
  · have hk' : max B (4000000*K)≤networkRank (N.sub (N.outside S)) := by
      generalize max B (4000000*K)=m at hk hR2
      omega
    have hS' : N.cutSize (fun v => ¬S v)=4 := by rw [N.cutSize_not S]; exact hS
    exact numCycles_le_inside hgap hK hF hcap hring N hN hcubic hmin
      (fun v => ¬S v) hS' hcyc.not hR1 hk'

/-- Actual multigraph four-cut statement from the gap, ring and fixed FewCycles inputs.
There is no pole-cycle-density or old four-cut arithmetic hypothesis. -/
theorem fourCutStatement_of_parts (hgap : GapStatement) (hring : RingCaseStatement)
    (hF : FewCyclesStatement) : FourCutStatement := by
  obtain ⟨K,hK,hF⟩ := hF
  obtain ⟨B,hcap⟩ := TreeCapShares.exists_bound
  obtain ⟨R,hring⟩ := ringCaseStatement_iff.mp hring
  refine ⟨max R (2*max B (4000000*K)+3),?_⟩
  rintro M hconn hcubic hloop hR hno3 ⟨U, hU, hcard⟩
  have hl : M.IsLoopless := M.isLoopless_iff_not_hasLoop.2 hloop
  have hN : M.looplessNetwork.graph.Connected := M.connected_iff_looplessNetwork.1 hconn
  have hcub : M.looplessNetwork.IsCubic := by
    intro v
    rw [← M.degree_eq_deg hl v]
    exact hcubic v
  -- the cut edges of a vertex set are the crossing edges
  have hcutcard : ∀ W : Finset M.Vertex,
      (M.cutEdges W).card = M.looplessNetwork.cutSize (fun v => v ∈ W) := by
    intro W
    have h2 : Nat.card {e : M.Edge // e ∈ M.cutEdges W} = (M.cutEdges W).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have h3 : M.looplessNetwork.cutSize (fun v => v ∈ W) =
        Nat.card {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} := rfl
    obtain ⟨f, hf⟩ : ∃ f : {e : M.NonloopEdge // M.looplessNetwork.crosses (fun v => v ∈ W) e} →
        {e : M.Edge // e ∈ M.cutEdges W}, ∀ a, (f a).1 = a.1.1 :=
      ⟨fun e => ⟨e.1.1, (M.mem_cutEdges_iff_crosses W e.1).2 e.2⟩, fun _ => rfl⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        have h1 : a.1.1 = b.1.1 := by rw [← hf a, ← hf b, hab]
        exact Subtype.ext (Subtype.ext h1)
      · intro b
        refine ⟨⟨⟨b.1, hl b.1⟩, (M.mem_cutEdges_iff_crosses W ⟨b.1, hl b.1⟩).1 b.2⟩, ?_⟩
        apply Subtype.ext
        rw [hf]
    have h1 := Nat.card_eq_of_bijective f hbij
    omega
  -- every cyclic cut of the network has at least four crossing edges
  have hmin : ∀ S : M.Vertex → Prop, M.looplessNetwork.IsCyclicCut S →
      4 ≤ M.looplessNetwork.cutSize S := by
    intro S hS
    obtain ⟨W, hW⟩ : ∃ W : Finset M.Vertex, (fun v => v ∈ W) = S :=
      ⟨Finset.univ.filter S, funext fun v => propext (by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩)⟩
    subst hW
    refine Nat.le_of_not_lt fun hlt => ?_
    apply hno3
    refine ⟨W, ⟨?_, ?_⟩, ?_⟩
    · have h := hS.1
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl W).2 ⟨z, hz, hw⟩
    · have h := hS.2
      rw [numCycles_sub] at h
      obtain ⟨⟨z, hz, hw⟩⟩ := Finite.card_pos_iff.1 h
      exact (M.hasCycleIn_iff_looplessNetwork hl Wᶜ).2 ⟨z, hz, fun g hg =>
        ⟨Finset.mem_compl.2 (hw g hg).1, Finset.mem_compl.2 (hw g hg).2⟩⟩
    · rw [hcutcard W]
      omega
  -- the given cut
  have hcyc : M.looplessNetwork.IsCyclicCut (fun v => v ∈ U) := by
    constructor
    · obtain ⟨z, hz, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl U).1 hU.1
      exact numCycles_sub_pos _ _ hz hw
    · obtain ⟨z, hz, hw⟩ := (M.hasCycleIn_iff_looplessNetwork hl Uᶜ).1 hU.2
      exact numCycles_sub_pos _ _ hz
        (fun g hg => ⟨Finset.mem_compl.1 (hw g hg).1, Finset.mem_compl.1 (hw g hg).2⟩)
  have hsize : M.looplessNetwork.cutSize (fun v => v ∈ U) = 4 := by
    have h1 := hmin _ hcyc
    have h2 := hcutcard U
    omega
  have h := numCycles_le hgap hK hF hcap hring M.looplessNetwork hN hcub hmin
    (fun v => v ∈ U) hsize hcyc (by rw [← M.cycleRank_eq_networkRank hl]; exact hR)
  rw [M.numCycles_eq_looplessNetwork hl, M.cycleRank_eq_networkRank hl]
  exact h


/-- Complete alternate four-cut theorem on the original finite multigraph model. -/
theorem fourCutStatement : ExactMaximum.FourCutStatement :=
  fourCutStatement_of_parts ExactMaximumSupport.gapStatement
    ExactMaximumSupport.ringCaseStatement ExactMaximum.fewCyclesStatement

end Erdos1016.ExactMaximumSupport.Shortening.FourCutTreeCap

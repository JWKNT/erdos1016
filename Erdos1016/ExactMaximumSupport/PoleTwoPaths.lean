import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximum.ThirdPair
import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximumSupport.BridgelessLayers
import Erdos1016.ExactMaximumSupport.DistanceFourLayers

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Two actual terminal paths in a bridgeless pole

The construction uses physical edge words throughout. Parallel labels remain distinct.
A cycle through both ports splits into two edge-disjoint terminal paths.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleTwoPaths
open BoundaryTrace BoundaryTrace.Network

local instance twoPathsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
theorem subword_add_complement_disjoint {x y : N.Word} (h : N.IsSubword y x) :
    ∀ e, y e ≠ 0 → (x+y) e = 0 := by
  intro e he
  have hx := h e he
  rcases bit_cases (y e) with hy | hy
  · exact (he hy).elim
  rcases bit_cases (x e) with hx' | hx'
  · exact (hx hx').elim
  show x e+y e=0
  rw [hx',hy]
  decide

/-- Removing one arc of a physical cycle gives its other arc. -/
theorem complementary_arc {s t : V} {z p : N.Word}
    (hz : N.IsCycleWord z) (hp : N.IsPathWord s t p) (hsub : N.IsSubword p z) :
    N.IsPathWord s t (z+p) := by
  apply N.isPathWord_of_minimal hp.1
  · rw [map_add,hz.boundary_eq_zero,hp.boundary_eq,zero_add]
  · intro y hy hy0
    have hyz : N.IsSubword y z := fun e he => hsub.add_self e (hy e he)
    by_cases hyzero : y=0
    · exact hyzero
    · have h := hz.eq_of_even_subword hyz hy0 hyzero
      obtain ⟨e,he,_⟩ := N.exists_edge_of_deg_pos (by rw [hp.2.1]; decide : 0<N.deg p s)
      have hze := hsub e he
      have hy' := hy e (by simpa only [h] using hze)
      exact False.elim (hy' (subword_add_complement_disjoint N hsub e he))

/-- Two vertices on a physical cycle determine two disjoint actual arcs. -/
theorem exists_cycle_arcs {s t : V} {z : N.Word} (hz : N.IsCycleWord z)
    (hst : s ≠ t) (hs : 0<N.deg z s) (ht : 0<N.deg z t) :
    ∃ p q : N.Word, N.IsPathWord s t p ∧ N.IsPathWord s t q ∧
      (∀ e,p e≠0 → q e=0) ∧ p+q=z ∧ N.IsSubword p z ∧ N.IsSubword q z := by
  have hreach : (N.sub fun e => z e≠0).graph.Reachable s t := by
    rw [N.sub_support_graph]
    exact hz.2.2 s t hs ht
  obtain ⟨p,hp,hw⟩ := N.exists_isPathWord_of_reachable (fun e => z e≠0) hst hreach
  have hsub : N.IsSubword p z := hw
  refine ⟨p,z+p,hp,complementary_arc N hz hp hsub,
    subword_add_complement_disjoint N hsub,?_,hsub,hsub.add_self⟩
  funext e
  change p e+(z e+p e)=z e
  rw [add_left_comm,bit_add_self,add_zero]

omit [Fintype V] in
/-- Internally disjoint actual paths with disjoint labels form a physical cycle. -/
theorem cycle_of_two_paths {s t : V} {p q : N.Word}
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0)
    (hvertex : ∀ v,v≠s → v≠t → N.deg p v=0 ∨ N.deg q v=0) :
    N.IsCycleWord (p+q) := by
  have hqedge : ∀ e,q e≠0 → p e=0 := by
    intro e he
    by_contra hn
    exact he (hedge e hn)
  have hpsub : N.IsSubword p (p+q) := by
    intro e he
    change p e+q e≠0
    simpa only [hedge e he,add_zero] using he
  have hqsub : N.IsSubword q (p+q) := by
    intro e he
    change p e+q e≠0
    simpa only [hqedge e he,zero_add] using he
  have hdeg (v : V) := N.deg_add_of_disjoint hedge v
  have hs : N.deg (p+q) s=2 := by rw [hdeg,hp.2.1,hq.2.1]
  have hconn (v : V) (hv : 0<N.deg (p+q) v) :
      (N.selectedGraph (p+q)).Reachable s v := by
    have hor : 0<N.deg p v ∨ 0<N.deg q v := by rw [hdeg] at hv; omega
    rcases hor with h | h
    · exact (hp.2.2.2.2 v h).mono hpsub.selectedGraph_le
    · exact (hq.2.2.2.2 v h).mono hqsub.selectedGraph_le
  refine ⟨?_,?_,?_⟩
  · intro hz
    have hh : N.deg (p+q) s=0 := by rw [hz]; simp [Network.deg]
    omega
  · intro v
    rw [hdeg]
    by_cases hvs : v=s
    · subst v; rw [hp.2.1,hq.2.1]; exact Or.inr rfl
    by_cases hvt : v=t
    · subst v; rw [hp.2.2.1,hq.2.2.1]; exact Or.inr rfl
    have hpv := hp.2.2.2.1 v hvs hvt
    have hqv := hq.2.2.2.1 v hvs hvt
    have hv := hvertex v hvs hvt
    omega
  · intro u v hu hv
    exact (hconn u hu).symm.trans (hconn v hv)

omit [Fintype V] in
/-- The physical subcubic degree bound makes edge-disjoint paths internally disjoint. -/
theorem internal_disjoint_of_edge_disjoint {s t : V} {p q : N.Word}
    (hdegree : ∀ v,N.deg (fun _ => 1) v≤3)
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) :
    ∀ v,v≠s → v≠t → N.deg p v=0 ∨ N.deg q v=0 := by
  intro v hvs hvt
  have hle : N.deg (p+q) v≤N.deg (fun _ => 1) v :=
    (show N.IsSubword (p+q) (fun _ => 1) from fun _ _ => one_ne_zero).deg_le v
  rw [N.deg_add_of_disjoint hedge] at hle
  have hpv := hp.2.2.2.1 v hvs hvt
  have hqv := hq.2.2.2.1 v hvs hvt
  have hd := hdegree v
  omega

/-- An ear can replace one arc while retaining a prescribed vertex of the old cycle. -/
theorem cycle_of_ear_preserving {s u w : V} {z p : N.Word}
    (hz : N.IsCycleWord z) (hs : 0<N.deg z s) (hu : 0<N.deg z u) (hw : 0<N.deg z w)
    (hp : N.IsPathWord u w p) (hedge : ∀ e,p e≠0 → z e=0)
    (hinter : ∀ v,0<N.deg p v → 0<N.deg z v → v=u ∨ v=w) :
    ∃ z' : N.Word,N.IsCycleWord z' ∧ 0<N.deg z' s ∧
      ∀ v,0<N.deg p v → 0<N.deg z' v := by
  obtain ⟨a,b,ha,hb,hab,hsum,haz,hbz⟩ := exists_cycle_arcs N hz hp.1 hu hw
  have hs' : 0<N.deg a s ∨ 0<N.deg b s := by
    rw [← hsum,N.deg_add_of_disjoint hab] at hs
    omega
  have build (q : N.Word) (hq : N.IsPathWord u w q) (hqz : N.IsSubword q z)
      (hqs : 0<N.deg q s) :
      ∃ z' : N.Word,N.IsCycleWord z' ∧ 0<N.deg z' s ∧
        ∀ v,0<N.deg p v → 0<N.deg z' v := by
    have hdis : ∀ e,q e≠0 → p e=0 := by
      intro e he
      by_contra hn
      exact hqz e he (hedge e hn)
    have hint : ∀ v,v≠u → v≠w → N.deg q v=0 ∨ N.deg p v=0 := by
      intro v hvu hvw
      by_contra hn
      have hqv : 0<N.deg q v := by omega
      have hpv : 0<N.deg p v := by omega
      exact (hinter v hpv (hqv.trans_le (hqz.deg_le v))).elim hvu hvw
    refine ⟨q+p,cycle_of_two_paths N hq hp hdis hint,?_,?_⟩
    · rw [N.deg_add_of_disjoint hdis]
      omega
    · intro v hv
      rw [N.deg_add_of_disjoint hdis]
      omega
  exact hs'.elim (build a ha haz) (build b hb hbz)

omit [Fintype V] in
theorem deg_word_complement (z : N.Word) (v : V) :
    N.deg z v+N.deg ((fun _ => 1)+z) v=N.deg (fun _ => 1) v := by
  have hd : ∀ e,z e≠0 → ((fun _ => 1)+z : N.Word) e=0 := by
    intro e he
    rcases bit_cases (z e) with h | h
    · exact (he h).elim
    · change 1+z e=0
      rw [h]
      decide
  rw [← N.deg_add_of_disjoint hd]
  congr 1
  funext e
  change z e+(1+z e)=1
  rw [add_left_comm,bit_add_self,add_zero]

omit [Fintype V] in
/-- At a subcubic cycle vertex, at most one physical label lies outside the cycle. -/
theorem outside_cycle_edge_unique {z : N.Word} (hz : N.IsCycleWord z) {u : V}
    (hu : 0<N.deg z u) (hd : N.deg (fun _ => 1) u≤3) {e f : E}
    (he : z e=0) (hf : z f=0)
    (heu : N.src e=u ∨ N.dst e=u) (hfu : N.src f=u ∨ N.dst f=u) : e=f := by
  have hzdeg : N.deg z u=2 := (hz.2.1 u).resolve_left (by omega)
  have hc := deg_word_complement N z u
  have hcard : (Finset.univ.filter fun g =>
      ((fun _ => 1)+z : N.Word) g≠0 ∧ (N.src g=u ∨ N.dst g=u)).card≤1 := by
    change N.deg ((fun _ => 1)+z) u≤1
    omega
  apply Finset.card_le_one.mp hcard e _ f _
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [Pi.add_apply,he],heu⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [Pi.add_apply,hf],hfu⟩

/-- An outside component has a second attachment to a cycle, at a distinct cycle vertex. -/
theorem second_cycle_attachment (hconn : N.graph.Connected) (hbridge : N.IsBridgeless)
    (hdegree : ∀ v,N.deg (fun _ => 1) v≤3) {z : N.Word} (hz : N.IsCycleWord z)
    {u v : V} {e : E} (he : N.Joins e u v) (hu : 0<N.deg z u) (hv : N.deg z v=0) :
    ∃ (y w : V) (f : E),N.Joins f y w ∧ u≠w ∧ 0<N.deg z w ∧ N.deg z y=0 ∧
      (N.sub fun g => N.deg z (N.src g)=0 ∧ N.deg z (N.dst g)=0).graph.Reachable v y := by
  let outside : E → Prop := fun g => N.deg z (N.src g)=0 ∧ N.deg z (N.dst g)=0
  let S : V → Prop := fun x => (N.sub outside).graph.Reachable v x
  have hsv : S v := SimpleGraph.Reachable.refl v
  have hzero (x : V) (hx : S x) : N.deg z x=0 := by
    apply (N.sub outside).mem_of_reachable_of_closed (fun q => N.deg z q=0) _ hx hv
    intro g
    exact ⟨fun _ => g.property.2,fun _ => g.property.1⟩
  have hsu : ¬S u := fun h => (by have := hzero u h; omega)
  have hcut := BridgelessLayers.cutSize_ge_two N hconn hbridge S v u hsv hsu
  have hcard : 1<(Finset.univ.filter fun g => N.crosses S g).card := by
    have hc : 2≤(Finset.univ.filter fun g => N.crosses S g).card := by
      simpa only [Network.cutSize,Nat.card_eq_fintype_card,Fintype.card_subtype] using hcut
    omega
  obtain ⟨f₁,f₂,hf₁,hf₂,hne⟩ := Finset.one_lt_card_iff.mp hcard
  obtain ⟨f,hcross,hfe⟩ : ∃ f,N.crosses S f ∧ f≠e := by
    by_cases h : f₁=e
    · exact ⟨f₂,(Finset.mem_filter.mp hf₂).2,fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨f₁,(Finset.mem_filter.mp hf₁).2,h⟩
  obtain ⟨y,w,hf,hy,hw⟩ := ExactMaximum.exists_joins_of_crosses N hcross
  have hyzero := hzero y hy
  have hwpos : 0<N.deg z w := by
    by_contra hn
    have hwzero : N.deg z w=0 := by omega
    have hfo : outside f := by
      rcases hf with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        simp only [outside,h1,h2,hyzero,hwzero,and_self]
    have hadj : (N.sub outside).graph.Adj y w := ⟨⟨f,hfo⟩,hf⟩
    exact hw (hy.trans hadj.reachable)
  have hezero : z e=0 := N.eq_zero_of_deg_eq_zero hv he.at_right
  have hfzero : z f=0 := N.eq_zero_of_deg_eq_zero hyzero hf.at_left
  have huw : u≠w := by
    intro h
    have hf_at_u : N.src f=u ∨ N.dst f=u := by simpa only [h] using hf.at_right
    exact hfe (outside_cycle_edge_unique N hz hu (hdegree u) hezero hfzero he.at_left hf_at_u).symm
  exact ⟨y,w,f,hf,huw,hwpos,hyzero,hy⟩

omit [Fintype V] [Fintype E] in
theorem incident_eq_endpoints {e : E} {u v x : V} (he : N.Joins e u v)
    (hx : N.src e=x ∨ N.dst e=x) : x=u ∨ x=v := by
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hx with h | h
  · exact Or.inl (h.symm.trans h1)
  · exact Or.inr (h.symm.trans h2)
  · exact Or.inr (h.symm.trans h1)
  · exact Or.inl (h.symm.trans h2)

/-- The two attachments give an actual ear containing the prescribed outside neighbor. -/
theorem exists_cycle_ear (hconn : N.graph.Connected) (hbridge : N.IsBridgeless)
    (hdegree : ∀ v,N.deg (fun _ => 1) v≤3) {z : N.Word} (hz : N.IsCycleWord z)
    {u v : V} {e : E} (he : N.Joins e u v) (hu : 0<N.deg z u) (hv : N.deg z v=0) :
    ∃ (w : V) (p : N.Word),N.IsPathWord u w p ∧ 0<N.deg z w ∧ 0<N.deg p v ∧
      (∀ g,p g≠0 → z g=0) ∧
      (∀ x,0<N.deg p x → 0<N.deg z x → x=u ∨ x=w) := by
  obtain ⟨y,w,f,hf,huw,hw,hy,hreach⟩ := second_cycle_attachment N hconn hbridge hdegree hz he hu hv
  let outside : E → Prop := fun g => N.deg z (N.src g)=0 ∧ N.deg z (N.dst g)=0
  let part : E → Prop := fun g => outside g ∨ g=e ∨ g=f
  have hout : (N.sub outside).graph ≤ (N.sub part).graph := by
    rintro a b ⟨g,hg⟩
    exact ⟨⟨g.val,Or.inl g.property⟩,hg⟩
  have hadje : (N.sub part).graph.Adj u v := ⟨⟨e,Or.inr (Or.inl rfl)⟩,he⟩
  have hadjf : (N.sub part).graph.Adj y w := ⟨⟨f,Or.inr (Or.inr rfl)⟩,hf⟩
  have hr : (N.sub part).graph.Reachable u w :=
    hadje.reachable.trans ((hreach.mono hout).trans hadjf.reachable)
  obtain ⟨p,hp,hpwithin⟩ := N.exists_isPathWord_of_reachable part huw hr
  have hzero_out (g : E) (hg : outside g) : z g=0 :=
    N.eq_zero_of_deg_eq_zero hg.1 (Or.inl rfl)
  have hezero : z e=0 := N.eq_zero_of_deg_eq_zero hv he.at_right
  have hfzero : z f=0 := N.eq_zero_of_deg_eq_zero hy hf.at_left
  have hpz : ∀g,p g≠0 → z g=0 := by
    intro g hg
    rcases hpwithin g hg with h | rfl | rfl
    · exact hzero_out g h
    · exact hezero
    · exact hfzero
  have hpe : p e≠0 := by
    obtain ⟨g,hpg,hgu⟩ := N.exists_edge_of_deg_pos hp.deg_left_pos
    have hge : g=e := by
      rcases hpwithin g hpg with h | h | h
      · have hh : N.deg z u=0 := hgu.elim (fun h' => h' ▸ h.1) (fun h' => h' ▸ h.2)
        omega
      · exact h
      · subst g
        rcases incident_eq_endpoints N hf hgu with h | h
        · rw [h] at hu
          omega
        · exact (huw h).elim
    simpa only [hge] using hpg
  have hpv : 0<N.deg p v := by
    rcases he.at_right with h | h
    · rw [← h]; exact N.deg_src_pos hpe
    · rw [← h]; exact N.deg_dst_pos hpe
  refine ⟨w,p,hp,hw,hpv,hpz,?_⟩
  intro x hpx hzx
  obtain ⟨g,hpg,hgx⟩ := N.exists_edge_of_deg_pos hpx
  rcases hpwithin g hpg with h | rfl | rfl
  · have hh : N.deg z x=0 := hgx.elim (fun h' => h' ▸ h.1) (fun h' => h' ▸ h.2)
    omega
  · rcases incident_eq_endpoints N he hgx with h | h
    · exact Or.inl h
    · rw [h] at hzx
      omega
  · rcases incident_eq_endpoints N hf hgx with h | h
    · rw [h] at hzx
      omega
    · exact Or.inr h

/-- A cycle can advance to any adjacent outside vertex while retaining a designated vertex. -/
theorem extend_cycle_to_neighbor (hconn : N.graph.Connected) (hbridge : N.IsBridgeless)
    (hdegree : ∀ v,N.deg (fun _ => 1) v≤3) {z : N.Word} (hz : N.IsCycleWord z)
    {s u v : V} (hs : 0<N.deg z s) (hu : 0<N.deg z u) (hv : N.deg z v=0)
    (huv : N.graph.Adj u v) :
    ∃ z' : N.Word,N.IsCycleWord z' ∧ 0<N.deg z' s ∧ 0<N.deg z' v := by
  obtain ⟨e,he⟩ := huv
  obtain ⟨w,p,hp,hw,hpv,hedge,hinter⟩ := exists_cycle_ear N hconn hbridge hdegree hz he hu hv
  obtain ⟨z',hz',hs',hcontains⟩ := cycle_of_ear_preserving N hz hs hu hw hp hedge hinter
  exact ⟨z',hz',hs',hcontains v hpv⟩

/-- In a connected bridgeless subcubic network, a cycle through one vertex can reach any other. -/
theorem exists_cycle_through_pair (hconn : N.graph.Connected) (hbridge : N.IsBridgeless)
    (hdegree : ∀ v,N.deg (fun _ => 1) v≤3) (s t : V)
    (hs : 0<N.deg (fun _ => 1) s) :
    ∃ z : N.Word,N.IsCycleWord z ∧ 0<N.deg z s ∧ 0<N.deg z t := by
  obtain ⟨e,_,hes⟩ := N.exists_edge_of_deg_pos hs
  obtain ⟨z,hz,hze⟩ := hbridge e
  have hzs : 0<N.deg z s := by
    rcases hes with h | h
    · rw [← h]; exact N.deg_src_pos hze
    · rw [← h]; exact N.deg_dst_pos hze
  let D : ℕ → Prop := fun n => ∃ (z : N.Word) (u : V),
    N.IsCycleWord z ∧ 0<N.deg z s ∧ 0<N.deg z u ∧ N.graph.dist t u=n
  have hex : ∃ n,D n := ⟨N.graph.dist t s,z,s,hz,hzs,hzs,rfl⟩
  obtain ⟨z,u,hz,hsz,huz,hdu⟩ := Nat.find_spec hex
  by_cases hut : u=t
  · exact ⟨z,hz,hsz,by simpa only [hut] using huz⟩
  have hdist : 0<N.graph.dist t u := by
    have hne : N.graph.dist t u≠0 := by
      intro h0
      exact hut (hconn.dist_eq_zero_iff.mp h0).symm
    omega
  obtain ⟨v,hvu,hdv⟩ := DistanceFourLayers.exists_predecessor N.graph t hconn u hdist
  have hvzero : N.deg z v=0 := by
    by_contra hn
    have hvpos : 0<N.deg z v := Nat.pos_of_ne_zero hn
    have hmin := Nat.find_min' hex (show D (N.graph.dist t v) from ⟨z,v,hz,hsz,hvpos,rfl⟩)
    omega
  obtain ⟨z',hz',hs',hv'⟩ := extend_cycle_to_neighbor N hconn hbridge hdegree hz hsz huz hvzero hvu.symm
  have hmin := Nat.find_min' hex (show D (N.graph.dist t v) from ⟨z',v,hz',hs',hv',rfl⟩)
  omega

/-- A bridgeless two-pole has two actual terminal paths with disjoint physical labels. -/
theorem exists_two_paths (s t : V) (hN : N.IsBridgelessTwoPole s t) :
    ∃ p q : N.Word,N.IsPathWord s t p ∧ N.IsPathWord s t q ∧
      (∀ e,p e≠0 → q e=0) ∧
      (∀ v,v≠s → v≠t → N.deg p v=0 ∨ N.deg q v=0) ∧ N.IsCycleWord (p+q) := by
  have hdegree (v : V) : N.deg (fun _ => 1) v≤3 := by
    by_cases hvs : v=s
    · subst v; exact hN.deg_s.le.trans (by decide)
    by_cases hvt : v=t
    · subst v; exact hN.deg_t.le.trans (by decide)
    exact (hN.deg_other v hvs hvt).le
  obtain ⟨z,hz,hs,ht⟩ := exists_cycle_through_pair N hN.connected hN.bridgeless hdegree s t
    (by rw [hN.deg_s]; decide)
  obtain ⟨p,q,hp,hq,hdis,hsum,_,_⟩ := exists_cycle_arcs N hz hN.ne hs ht
  exact ⟨p,q,hp,hq,hdis,internal_disjoint_of_edge_disjoint N hdegree hp hq hdis,hsum.symm ▸ hz⟩

end Erdos1016.ExactMaximumSupport.PoleTwoPaths

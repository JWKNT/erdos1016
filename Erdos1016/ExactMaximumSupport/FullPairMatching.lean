import Erdos1016.ExactMaximumSupport.PoleTwoPaths
import Erdos1016.ExactMaximum.NetBridgeCut

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The actual matching between two full-pair rails

The words retain every physical edge label. Fullness excludes cycles in either
rail's edge complement. The residual components therefore meet each rail at most once.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.FullPairMatching
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance fullPairMatchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- In a two-pole, edge-disjointness from a terminal path implies vertex-disjointness. -/
theorem cycle_vertexDisjoint_of_edge_disjoint {s t : V}
    (hN : N.IsBridgelessTwoPole s t) {p z : N.Word}
    (hp : N.IsPathWord s t p) (hz : N.IsCycleWord z)
    (hedge : ∀ e,p e≠0 → z e=0) : N.VertexDisjoint p z := by
  intro v
  have hle : N.deg (p+z) v≤N.deg (fun _ => 1) v :=
    (show N.IsSubword (p+z) (fun _ => 1) from fun _ _ => one_ne_zero).deg_le v
  rw [N.deg_add_of_disjoint hedge] at hle
  have hzv := hz.2.1 v
  by_cases hvs : v=s
  · subst v; rw [hp.2.1,hN.deg_s] at hle; omega
  by_cases hvt : v=t
  · subst v; rw [hp.2.2.1,hN.deg_t] at hle; omega
  rw [hN.deg_other v hvs hvt] at hle
  have hpv := hp.2.2.2.1 v hvs hvt
  omega

/-- Fullness excludes an actual cycle from a terminal path's edge complement. -/
theorem not_cycle_of_edge_disjoint {s t : V}
    (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
    {p z : N.Word} (hp : N.IsPathWord s t p)
    (hedge : ∀ e,p e≠0 → z e=0) : ¬N.IsCycleWord z := by
  intro hz
  obtain ⟨v,hpv,hzv⟩ := hfull.cycle_meets_path hp hz
  have hd := cycle_vertexDisjoint_of_edge_disjoint N hN hp hz hedge v
  omega

/-- The physical labels outside both rails. -/
def residual (p q : N.Word) : N.Word := (fun _ => 1)+(p+q)

omit [Fintype V] [Fintype E] in
/-- A selected residual label belongs to neither rail. -/
theorem residual_selected_iff {p q : N.Word} (hedge : ∀ e,p e≠0 → q e=0) (e : E) :
    residual N p q e≠0 ↔ p e=0 ∧ q e=0 := by
  change (1:Bit)+(p e+q e)≠0 ↔ _
  rcases bit_cases (p e) with hp | hp <;> rcases bit_cases (q e) with hq | hq
  · simp [hp,hq]
  · simp [hp,hq]
  · simp [hp,hq]
  · have := hedge e (by rw [hp]; exact one_ne_zero)
    simp [hq] at this

omit [Fintype V] in
/-- The residual degree is the unused part of the actual cubic degree. -/
theorem residual_degree {p q : N.Word} (hedge : ∀ e,p e≠0 → q e=0) (v : V) :
    N.deg (residual N p q) v+N.deg p v+N.deg q v=N.deg (fun _ => 1) v := by
  have h := PoleTwoPaths.deg_word_complement N (p+q) v
  rw [N.deg_add_of_disjoint hedge] at h
  change _ + N.deg ((fun _ => 1)+(p+q)) v=_ at h
  unfold residual
  omega

/-- Every residual subnetwork has rank zero. -/
theorem residual_rank_zero {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {p q : N.Word} (hp : N.IsPathWord s t p)
    (hedge : ∀ e,p e≠0 → q e=0) (T : E → Prop) [Fintype {e : E // T e}]
    (hT : ∀ e,T e → residual N p q e≠0) : networkRank (N.sub T)=0 := by
  by_contra hn
  obtain ⟨z,hz⟩ := (N.sub T).exists_isCycleWord_of_rank_pos (Nat.pos_of_ne_zero hn)
  have hz' := (N.isCycleWord_extend_iff T z).2 hz
  apply not_cycle_of_edge_disjoint N hN hfull hp (z:=extend T z) _ hz'
  intro e he
  by_contra hne
  have hr := hT e (within_extend T z e hne)
  exact he ((residual_selected_iff N hedge e).1 hr).1

/-- Distinct vertices of a path have an actual subpath between them. -/
theorem exists_subpath {s t u v : V} {p : N.Word} (hp : N.IsPathWord s t p)
    (hu : 0<N.deg p u) (hv : 0<N.deg p v) (huv : u≠v) :
    ∃ a : N.Word,N.IsPathWord u v a ∧ N.IsSubword a p := by
  have hreach : (N.sub fun e=>p e≠0).graph.Reachable u v := by
    rw [N.sub_support_graph]
    exact (hp.2.2.2.2 u hu).symm.trans (hp.2.2.2.2 v hv)
  exact N.exists_isPathWord_of_reachable (fun e=>p e≠0) huv hreach

/-- A residual component meets a fixed rail at most once. -/
theorem residual_reachable_rail_unique {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {p q : N.Word}
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) {u v : V}
    (hu : 0<N.deg p u) (hv : 0<N.deg p v)
    (hreach : (N.sub fun e=>residual N p q e≠0).graph.Reachable u v) : u=v := by
  by_contra huv
  obtain ⟨r,hr,hrsub⟩ := N.exists_isPathWord_of_reachable
    (fun e=>residual N p q e≠0) huv hreach
  obtain ⟨a,ha,hasub⟩ := exists_subpath N hp hu hv huv
  have har : ∀ e,a e≠0 → r e=0 := by
    intro e he
    by_contra hn
    exact hasub e he ((residual_selected_iff N hedge e).1 (hrsub e hn)).1
  have hdegree (w : V) : N.deg (fun _=>1) w≤3 := by
    by_cases hws:w=s
    · subst w; rw [hN.deg_s]; decide
    by_cases hwt:w=t
    · subst w; rw [hN.deg_t]; decide
    rw [hN.deg_other w hws hwt]
  have hz := PoleTwoPaths.cycle_of_two_paths N ha hr har
    (PoleTwoPaths.internal_disjoint_of_edge_disjoint N hdegree ha hr har)
  apply not_cycle_of_edge_disjoint N hN hfull hq (z:=a+r) _ hz
  intro e he
  have ha0 : a e=0 := by
    by_contra hn
    exact he (hedge e (hasub e hn))
  have hr0 : r e=0 := by
    by_contra hn
    exact he ((residual_selected_iff N hedge e).1 (hrsub e hn)).2
  change a e+r e=0
  rw [ha0,hr0,add_zero]

omit [Fintype V] [Fintype E] in
@[simp] theorem residual_comm (p q : N.Word) : residual N p q=residual N q p := by
  unfold residual
  rw [add_comm p q]

omit [Fintype V] in
/-- A vertex with no selected incidence is isolated in the actual selected subnetwork. -/
theorem eq_of_reachable_of_degree_zero {x : N.Word} {u v : V} (hu : N.deg x u=0)
    (hreach : (N.sub fun e=>x e≠0).graph.Reachable u v) : u=v := by
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨e,he⟩ := hadj
    have hat : N.src e.1=u ∨ N.dst e.1=u := he.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.2)
    exact (e.2 (N.eq_zero_of_deg_eq_zero hu hat)).elim

omit [Fintype V] in
/-- Neither port has a residual incidence. -/
theorem residual_ports {s t : V} (hN : N.IsBridgelessTwoPole s t)
    {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) :
    N.deg (residual N p q) s=0 ∧ N.deg (residual N p q) t=0 := by
  have hs := residual_degree N hedge s
  have ht := residual_degree N hedge t
  rw [hp.2.1,hq.2.1,hN.deg_s] at hs
  rw [hp.2.2.1,hq.2.2.1,hN.deg_t] at ht
  omega

/-- Every residual component has at most two vertices, hence at most one physical edge. -/
theorem residual_degree_le_one {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {p q : N.Word}
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) (v : V) : N.deg (residual N p q) v≤1 := by
  classical
  let R := residual N p q
  by_cases hvzero : N.deg R v=0
  · exact hvzero.le.trans (by decide)
  let S : V → Prop := fun w=>(N.sub fun e=>R e≠0).graph.Reachable v w
  let T : E → Prop := fun e=>R e≠0 ∧ S (N.src e) ∧ S (N.dst e)
  let M := N.sub T
  have hvS : S v := SimpleGraph.Reachable.refl _
  have hclosure (e : E) (he : R e≠0) : S (N.src e) ↔ S (N.dst e) := by
    have ha : (N.sub fun e=>R e≠0).graph.Adj (N.src e) (N.dst e) :=
      ⟨⟨e,he⟩,Or.inl ⟨rfl,rfl⟩⟩
    exact ⟨fun h=>h.trans ha.reachable,fun h=>h.trans ha.symm.reachable⟩
  have hdeg_in (w : V) (hw : S w) : M.deg (fun _=>1) w=N.deg R w := by
    rw [N.deg_sub_ones T]
    apply N.deg_congr
    intro e he
    rw [restrict_ne_zero_iff]
    constructor
    · exact fun h=>h.1.1
    · intro hr
      have hboth : S (N.src e) ∧ S (N.dst e) := by
        rcases he with h | h
        · exact ⟨h ▸ hw,(hclosure e hr).mp (h ▸ hw)⟩
        · exact ⟨(hclosure e hr).mpr (h ▸ hw),h ▸ hw⟩
      exact ⟨⟨hr,hboth⟩,one_ne_zero⟩
  have hdeg_out (w : V) (hw : ¬S w) : M.deg (fun _=>1) w=0 := by
    rw [N.deg_sub_ones T]
    apply N.deg_eq_zero_of_forall
    intro e he
    apply restrict_apply_of_neg
    intro ht
    rcases he with h | h
    · exact hw (h ▸ ht.2.1)
    · exact hw (h ▸ ht.2.2)
  have hports := residual_ports N hN hp hq hedge
  have hnotport (w : V) (hw : S w) : w≠s ∧ w≠t := by
    constructor
    · intro h
      subst w
      have hsv := eq_of_reachable_of_degree_zero N hports.1 hw.symm
      exact hvzero (hsv ▸ hports.1)
    · intro h
      subst w
      have htv := eq_of_reachable_of_degree_zero N hports.2 hw.symm
      exact hvzero (htv ▸ hports.2)
  have hqedge : ∀ e,q e≠0 → p e=0 := by
    intro e he
    by_contra hn
    exact he (hedge e hn)
  let A : Finset V := Finset.univ.filter fun w=>S w ∧ 0<N.deg p w
  let B : Finset V := Finset.univ.filter fun w=>S w ∧ 0<N.deg q w
  have hA : A.card≤1 := by
    apply Finset.card_le_one.mpr
    intro u hu w hw
    have hu' := (Finset.mem_filter.mp hu).2
    have hw' := (Finset.mem_filter.mp hw).2
    exact residual_reachable_rail_unique N hN hfull hp hq hedge hu'.2 hw'.2
      (hu'.1.symm.trans hw'.1)
  have hB : B.card≤1 := by
    apply Finset.card_le_one.mpr
    intro u hu w hw
    have hu' := (Finset.mem_filter.mp hu).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply residual_reachable_rail_unique N hN hfull hq hp hqedge hu'.2 hw'.2
    rw [residual_comm N q p]
    exact hu'.1.symm.trans hw'.1
  have hpoint (w : V) : (if S w then 3 else 0)=M.deg (fun _=>1) w+
      (if S w ∧ 0<N.deg p w then 2 else 0)+(if S w ∧ 0<N.deg q w then 2 else 0) := by
    by_cases hw : S w
    · obtain ⟨hws,hwt⟩ := hnotport w hw
      rw [if_pos hw,hdeg_in w hw]
      have hd := residual_degree N hedge w
      rw [hN.deg_other w hws hwt] at hd
      change N.deg R w+N.deg p w+N.deg q w=3 at hd
      have hpd := hp.2.2.2.1 w hws hwt
      have hqd := hq.2.2.2.1 w hws hwt
      simp only [hw,true_and]
      split_ifs <;> omega
    · rw [if_neg hw,hdeg_out w hw,if_neg (fun h=>hw h.1),if_neg (fun h=>hw h.1)]
  have hsum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun w _=>hpoint w)
  have hhand : (∑ w : V,M.deg (fun _=>1) w)=2*Nat.card {e:E//T e} := by
    have hh := M.sum_deg_eq (fun _=>True)
    simpa [Nat.card_eq_fintype_card,Nat.mul_comm] using hh
  have hcount (U : V → Prop) [DecidablePred U] (n : ℕ) :
      (∑ w:V,if U w then n else 0)=n*(Finset.univ.filter U).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hhand] at hsum
  have hsum' : 3*(Finset.univ.filter S).card=
      2*Nat.card {e:E//T e}+2*A.card+2*B.card := by
    calc
      _ = (∑ w:V,if S w then 3 else 0) := (hcount S 3).symm
      _ = 2*Nat.card {e:E//T e}+(∑ w:V,if S w ∧ 0<N.deg p w then 2 else 0)+
          (∑ w:V,if S w ∧ 0<N.deg q w then 2 else 0) := by
        convert hsum using 1
      _ = _ := by rw [hcount,hcount]
  have hrank : networkRank M=0 := residual_rank_zero N hN hfull hp hedge T (fun _ h=>h.1)
  have heuler : Nat.card {e:E//T e}+1≤Nat.card {w:V//S w} := by
    have hEuler := network_rank_euler M
    simp only [← Nat.card_eq_fintype_card,hrank,zero_add] at hEuler
    have hcomponents := natCard_component_ge M S hvS (fun e=>e.2.2)
    have hV : Nat.card V=Nat.card {w:V//S w}+Nat.card {w:V//¬S w} := by
      rw [← natCard_or_of_disjoint (fun w:V=>S w) (fun w=>¬S w) (fun w h hn=>hn h)]
      exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun w=>Classical.em (S w)))).symm
    omega
  have hScard : Nat.card {w:V//S w}=(Finset.univ.filter S).card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hScard] at heuler
  have hedges : Nat.card {e:E//T e}≤1 := by omega
  have hdeg_bound : M.deg (fun _=>1) v≤Nat.card {e:E//T e} := by
    unfold Network.deg
    rw [Nat.card_eq_fintype_card]
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)
  rw [hdeg_in v hvS] at hdeg_bound
  exact hdeg_bound.trans hedges

/-- The residual is an actual matching, and the two rails cover all vertices. -/
theorem residual_matching_degrees {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {p q : N.Word}
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) :
    (∀ v,0<N.deg p v ∨ 0<N.deg q v) ∧
    (∀ v,N.deg (residual N p q) v=if v=s ∨ v=t then 0 else 1) := by
  constructor
  · intro v
    have hle := residual_degree_le_one N hN hfull hp hq hedge v
    have hd := residual_degree N hedge v
    by_cases hvs:v=s
    · subst v; exact Or.inl hp.deg_left_pos
    by_cases hvt:v=t
    · subst v; exact Or.inl hp.deg_right_pos
    rw [hN.deg_other v hvs hvt] at hd
    omega
  · intro v
    obtain ⟨hs,ht⟩ := residual_ports N hN hp hq hedge
    by_cases hvs:v=s
    · subst v; rw [if_pos (Or.inl rfl)]; exact hs
    by_cases hvt:v=t
    · subst v; rw [if_pos (Or.inr rfl)]; exact ht
    rw [if_neg (fun h=>h.elim hvs hvt)]
    have hle := residual_degree_le_one N hN hfull hp hq hedge v
    have hd := residual_degree N hedge v
    rw [hN.deg_other v hvs hvt] at hd
    have hpd := hp.2.2.2.1 v hvs hvt
    have hqd := hq.2.2.2.1 v hvs hvt
    omega

/-- Every residual physical label joins the two different rails. -/
theorem residual_joins_rails {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {p q : N.Word}
    (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
    (hedge : ∀ e,p e≠0 → q e=0) {e : E} (he : residual N p q e≠0) :
    (0<N.deg p (N.src e) ∧ 0<N.deg q (N.dst e)) ∨
      (0<N.deg q (N.src e) ∧ 0<N.deg p (N.dst e)) := by
  have hcover := (residual_matching_degrees N hN hfull hp hq hedge).1
  have hreach : (N.sub fun e=>residual N p q e≠0).graph.Reachable (N.src e) (N.dst e) :=
    (show (N.sub fun e=>residual N p q e≠0).graph.Adj (N.src e) (N.dst e) from
      ⟨⟨e,he⟩,Or.inl ⟨rfl,rfl⟩⟩).reachable
  rcases hcover (N.src e) with hs | hs <;> rcases hcover (N.dst e) with ht | ht
  · exact (N.noLoops e (residual_reachable_rail_unique N hN hfull hp hq hedge hs ht hreach)).elim
  · exact Or.inl ⟨hs,ht⟩
  · exact Or.inr ⟨hs,ht⟩
  · have hqedge : ∀ f,q f≠0 → p f=0 := by
      intro f hf
      by_contra hn
      exact hf (hedge f hn)
    have hreach' : (N.sub fun e=>residual N q p e≠0).graph.Reachable (N.src e) (N.dst e) := by
      rw [residual_comm N q p]
      exact hreach
    exact (N.noLoops e (residual_reachable_rail_unique N hN hfull hq hp hqedge hs ht hreach')).elim

/-- Fullness supplies the actual two rails and their complete residual perfect matching. -/
theorem exists_full_pair_matching (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) :
    ∃ p q : N.Word,N.IsPathWord s t p ∧ N.IsPathWord s t q ∧
      (∀ e,p e≠0 → q e=0) ∧
      (∀ v,v≠s → v≠t →
        (N.deg p v=2 ∧ N.deg q v=0) ∨ (N.deg p v=0 ∧ N.deg q v=2)) ∧
      (∀ v,N.deg (residual N p q) v=if v=s ∨ v=t then 0 else 1) ∧
      (∀ e,residual N p q e≠0 →
        (0<N.deg p (N.src e) ∧ 0<N.deg q (N.dst e)) ∨
        (0<N.deg q (N.src e) ∧ 0<N.deg p (N.dst e))) := by
  obtain ⟨p,q,hp,hq,hedge,hinner,_⟩ := PoleTwoPaths.exists_two_paths N s t hN
  obtain ⟨hcover,hdegrees⟩ := residual_matching_degrees N hN hfull hp hq hedge
  refine ⟨p,q,hp,hq,hedge,?_,hdegrees,fun e he=>residual_joins_rails N hN hfull hp hq hedge he⟩
  intro v hvs hvt
  have hpv := hp.2.2.2.1 v hvs hvt
  have hqv := hq.2.2.2.1 v hvs hvt
  have hv := hinner v hvs hvt
  have hc := hcover v
  omega

end Erdos1016.ExactMaximumSupport.FullPairMatching

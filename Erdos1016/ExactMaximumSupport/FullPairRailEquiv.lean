import Erdos1016.ExactMaximumSupport.FullPairMatching
import Erdos1016.ExactMaximumSupport.NetworkMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The matching as an actual rail equivalence

Each inner rail vertex has one residual physical label. Its other end determines
an equivalence of the two inner vertex sets, with every matching label retained.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairRailEquiv
open BoundaryTrace BoundaryTrace.Network FullPairMatching
local instance railEquivDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The actual inner vertices of a path word. -/
def Inner (p : N.Word) := {v : V // N.deg p v=2}

variable {s t : V} (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
  {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
  (hedge : ∀ e,p e≠0 → q e=0)
include hN hfull hp hq hedge

/-- An inner vertex has exactly one residual incidence and belongs to only its rail. -/
theorem inner_degrees (u : Inner N p) :
    N.deg (residual N p q) u.1=1 ∧ N.deg q u.1=0 := by
  have hne_s : u.1≠s := by intro h; have := u.2; rw [h,hp.2.1] at this; omega
  have hne_t : u.1≠t := by intro h; have := u.2; rw [h,hp.2.2.1] at this; omega
  have hd := (residual_matching_degrees N hN hfull hp hq hedge).2 u.1
  rw [if_neg (fun h=>h.elim hne_s hne_t)] at hd
  have hsum := residual_degree N hedge u.1
  rw [hN.deg_other u.1 hne_s hne_t,u.2,hd] at hsum
  exact ⟨hd,by omega⟩

omit hN hfull hp hq hedge [Fintype V] in
/-- A selected degree-one vertex has a unique physical incident label. -/
theorem incident_label_unique {x : N.Word} {u : V} (hu : N.deg x u=1)
    {e f : E} (he : x e≠0) (hf : x f≠0)
    (heu : N.src e=u ∨ N.dst e=u) (hfu : N.src f=u ∨ N.dst f=u) : e=f := by
  have hc : (Finset.univ.filter fun g=>x g≠0 ∧ (N.src g=u ∨ N.dst g=u)).card≤1 := hu.le
  exact Finset.card_le_one.mp hc e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,heu⟩)
    f (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf,hfu⟩)

/-- A residual label out of an inner vertex reaches an inner vertex of the other rail. -/
theorem other_inner (u : Inner N p) {e : E} {v : V}
    (he : residual N p q e≠0) (hjoin : N.Joins e u.1 v) : N.deg q v=2 := by
  have hdu := inner_degrees N hN hfull hp hq hedge u
  have hcross := residual_joins_rails N hN hfull hp hq hedge he
  have hqv : 0<N.deg q v := by
    rcases hjoin with ⟨hsrc,hdst⟩ | ⟨hsrc,hdst⟩
    · rw [hsrc,hdst] at hcross
      rcases hcross with h | h
      · exact h.2
      · omega
    · rw [hsrc,hdst] at hcross
      rcases hcross with h | h
      · omega
      · exact h.1
  have hrpos : 0<N.deg (residual N p q) v := by
    rcases hjoin.at_right with h | h
    · simpa only [h] using N.deg_src_pos he
    · simpa only [h] using N.deg_dst_pos he
  have hports := residual_ports N hN hp hq hedge
  have hvs : v≠s := by intro h; rw [h,hports.1] at hrpos; omega
  have hvt : v≠t := by intro h; rw [h,hports.2] at hrpos; omega
  have hv := hq.2.2.2.1 v hvs hvt
  omega

/-- Every inner vertex has an actual matching partner. -/
theorem exists_partner (u : Inner N p) :
    ∃ v : Inner N q,∃ e:E,residual N p q e≠0 ∧ N.Joins e u.1 v.1 := by
  obtain ⟨e,he,hinc⟩ := N.exists_edge_of_deg_pos
    (by rw [(inner_degrees N hN hfull hp hq hedge u).1]; decide :
      0<N.deg (residual N p q) u.1)
  rcases hinc with h | h
  · have hj : N.Joins e u.1 (N.dst e) := Or.inl ⟨h,rfl⟩
    exact ⟨⟨N.dst e,other_inner N hN hfull hp hq hedge u he hj⟩,e,he,hj⟩
  · have hj : N.Joins e u.1 (N.src e) := Or.inr ⟨rfl,h⟩
    exact ⟨⟨N.src e,other_inner N hN hfull hp hq hedge u he hj⟩,e,he,hj⟩

/-- The unique partner, selected from the actual residual matching. -/
def partner (u : Inner N p) : Inner N q :=
  Classical.choose (exists_partner N hN hfull hp hq hedge u)

theorem partner_spec (u : Inner N p) :
    ∃ e:E,residual N p q e≠0 ∧ N.Joins e u.1 (partner N hN hfull hp hq hedge u).1 :=
  Classical.choose_spec (exists_partner N hN hfull hp hq hedge u)

/-- Two residual labels at the same inner vertex have the same other endpoint. -/
theorem partner_unique (u : Inner N p) {v w : V} {e f : E}
    (he : residual N p q e≠0) (hf : residual N p q f≠0)
    (hj : N.Joins e u.1 v) (hk : N.Joins f u.1 w) : v=w := by
  have hef := incident_label_unique N (inner_degrees N hN hfull hp hq hedge u).1
    he hf hj.at_left hk.at_left
  subst f
  exact NetworkMultiplicity.joins_other_unique N hj hk

/-- The partner map is a bijection between the actual inner vertex sets. -/
theorem partner_bijective : Function.Bijective (partner N hN hfull hp hq hedge) := by
  have hqedge : ∀ e,q e≠0 → p e=0 := by
    intro e he
    by_contra hn
    exact he (hedge e hn)
  constructor
  · intro u v huv
    obtain ⟨e,he,hj⟩ := partner_spec N hN hfull hp hq hedge u
    obtain ⟨f,hf,hk⟩ := partner_spec N hN hfull hp hq hedge v
    rw [huv] at hj
    apply Subtype.ext
    apply partner_unique N hN hfull hq hp hqedge (partner N hN hfull hp hq hedge v)
      (e:=e) (f:=f) _ _ hj.symm hk.symm
    · simpa only [residual_comm N q p] using he
    · simpa only [residual_comm N q p] using hf
  · intro v
    obtain ⟨u,e,he,hj⟩ := exists_partner N hN hfull hq hp hqedge v
    obtain ⟨f,hf,hk⟩ := partner_spec N hN hfull hp hq hedge u
    refine ⟨u,Subtype.ext ?_⟩
    apply partner_unique N hN hfull hp hq hedge u hf _ hk hj.symm
    simpa only [residual_comm N q p] using he

/-- The matching equivalence retains the actual vertices on both rails. -/
def matchingEquiv : Inner N p ≃ Inner N q :=
  Equiv.ofBijective (partner N hN hfull hp hq hedge) (partner_bijective N hN hfull hp hq hedge)

/-- The physical label used by the matching equivalence. -/
def matchingLabel (u : Inner N p) : E :=
  Classical.choose (partner_spec N hN hfull hp hq hedge u)

theorem matchingLabel_spec (u : Inner N p) :
    residual N p q (matchingLabel N hN hfull hp hq hedge u)≠0 ∧
    N.Joins (matchingLabel N hN hfull hp hq hedge u) u.1
      (matchingEquiv N hN hfull hp hq hedge u).1 :=
  Classical.choose_spec (partner_spec N hN hfull hp hq hedge u)

/-- Distinct inner vertices use distinct physical matching labels. -/
theorem matchingLabel_injective : Function.Injective (matchingLabel N hN hfull hp hq hedge) := by
  intro u v huv
  have hu := matchingLabel_spec N hN hfull hp hq hedge u
  have hv := matchingLabel_spec N hN hfull hp hq hedge v
  rw [huv] at hu
  have hh : u.1=v.1 ∨ u.1=(matchingEquiv N hN hfull hp hq hedge v).1 :=
    PoleTwoPaths.incident_eq_endpoints N hv.2 hu.2.at_left
  rcases hh with h | h
  · exact Subtype.ext h
  · have hd := (inner_degrees N hN hfull hp hq hedge u).2
    have hd' := (matchingEquiv N hN hfull hp hq hedge v).2
    rw [h] at hd
    omega

omit hfull [Fintype V] in
/-- A rail vertex incident with a residual label is an inner vertex. -/
theorem inner_of_residual_positive {u : V}
    (hu : 0<N.deg p u) (hr : 0<N.deg (residual N p q) u) : N.deg p u=2 := by
  have hports := residual_ports N hN hp hq hedge
  have hus : u≠s := by intro h; rw [h,hports.1] at hr; omega
  have hut : u≠t := by intro h; rw [h,hports.2] at hr; omega
  have hd := hp.2.2.2.1 u hus hut
  omega

/-- Every residual physical label occurs in the matching-label map. -/
theorem matchingLabel_coverage {e : E} (he : residual N p q e≠0) :
    ∃ u : Inner N p,matchingLabel N hN hfull hp hq hedge u=e := by
  have hcross := residual_joins_rails N hN hfull hp hq hedge he
  rcases hcross with h | h
  · let u : Inner N p := ⟨N.src e,inner_of_residual_positive N hN hp hq hedge h.1 (N.deg_src_pos he)⟩
    have hu := matchingLabel_spec N hN hfull hp hq hedge u
    exact ⟨u,incident_label_unique N (inner_degrees N hN hfull hp hq hedge u).1
      hu.1 he hu.2.at_left (Or.inl rfl)⟩
  · let u : Inner N p := ⟨N.dst e,inner_of_residual_positive N hN hp hq hedge h.2 (N.deg_dst_pos he)⟩
    have hu := matchingLabel_spec N hN hfull hp hq hedge u
    exact ⟨u,incident_label_unique N (inner_degrees N hN hfull hp hq hedge u).1
      hu.1 he hu.2.at_left (Or.inr rfl)⟩

/-- The residual edge labels are in bijection with either inner rail. -/
def matchingEdgeEquiv : Inner N p ≃ {e:E//residual N p q e≠0} :=
  Equiv.ofBijective
    (fun u=>⟨matchingLabel N hN hfull hp hq hedge u,(matchingLabel_spec N hN hfull hp hq hedge u).1⟩)
    ⟨fun u v h=>matchingLabel_injective N hN hfull hp hq hedge (congrArg Subtype.val h),
      fun e=>by
        obtain ⟨u,hu⟩ := matchingLabel_coverage N hN hfull hp hq hedge e.2
        exact ⟨u,Subtype.ext hu⟩⟩

end Erdos1016.ExactMaximumSupport.FullPairRailEquiv

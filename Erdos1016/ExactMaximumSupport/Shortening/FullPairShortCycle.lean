import Erdos1016.ExactMaximumSupport.FullPairCappedLadder
import Erdos1016.ExactMaximumSupport.NetworkFourCycle
import Erdos1016.ExactMaximum.ShortestCycle

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A full bridgeless two-pole has a short physical cycle

The rank-one parallel pair gives a digon. In a concrete capped ladder, the
first rung gives a triangle and a square tile gives a quadrilateral. The
actual full-pair classification supplies the model, with no certificate premise.
This is only a local ingredient for the proposed bounded-port girth-five bound.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FullPairShortCycle
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles

local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E V' E' : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']

omit [Fintype V] [Fintype V'] in
/-- An undirected physical-label isomorphism preserves the exact word size. -/
theorem size_push {N : Network V E} {M : Network V' E'} (R : NetworkIso N M)
    (x : N.Word) : size (R.push x)=size x := by
  classical
  let φ : {e : E // x e≠0} ≃ {e : E' // R.push x e≠0} :=
    { toFun := fun e => ⟨R.edges e.val,by simpa only [R.push_apply] using e.property⟩
      invFun := fun e => ⟨R.edges.symm e.val,e.property⟩
      left_inv := fun e => by apply Subtype.ext; exact R.edges.symm_apply_apply e.val
      right_inv := fun e => by apply Subtype.ext; exact R.edges.apply_symm_apply e.val }
  have h := Nat.card_congr φ.symm
  simpa only [size,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

omit [Fintype V'] [Fintype E'] in
/-- Three distinct cyclically adjacent vertices give an actual cycle of size at most three. -/
theorem triangle (N : Network V E) {a b c : V}
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (h₁ : N.graph.Adj a b) (h₂ : N.graph.Adj b c) (h₃ : N.graph.Adj c a) :
    ∃ z : N.Word,N.IsCycleWord z ∧ size z≤3 := by
  obtain ⟨e,he⟩ := h₁
  obtain ⟨f,hf⟩ := h₂
  obtain ⟨g,hg⟩ := h₃
  have hP := (N.isPathWord_unitWord he).add_pendant hf
    (N.deg_unitWord_of_joins he hac.symm hbc.symm)
  have heg := NetworkFourCycle.edges_ne_of_fresh N he hg hac.symm hbc.symm
  have hfg := NetworkFourCycle.edges_ne_of_fresh N hf hg.symm hab hac
  have hz := hP.add_closing hg.symm (by simp [unitWord_apply,heg,hfg])
  refine ⟨unitWord e+unitWord f+unitWord g,hz,?_⟩
  have h1 := size_add_le (unitWord e : N.Word) (unitWord f)
  have h2 := size_add_le (unitWord e+unitWord f : N.Word) (unitWord g)
  simp only [size_unitWord] at h1 h2
  omega

variable {k : ℕ}

/-- An actual local-tile adjacency remains an adjacency of the capped network. -/
theorem tile_adj (T : Fin (k+1) → Kind) (i : Fin (k+1))
    {a b : (T i).Vertex} (h : (T i).network.graph.Adj a b) :
    (capped T).graph.Adj (Sum.inl ⟨i,a⟩) (Sum.inl ⟨i,b⟩) := by
  obtain ⟨e,he⟩ := h
  refine ⟨Sum.inl (inner T i e),?_⟩
  rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨congrArg (fun v => Sum.inl (Sigma.mk i v)) ha,
      congrArg (fun v => Sum.inl (Sigma.mk i v)) hb⟩
  · exact Or.inr ⟨congrArg (fun v => Sum.inl (Sigma.mk i v)) ha,
      congrArg (fun v => Sum.inl (Sigma.mk i v)) hb⟩

/-- Every concrete capped ladder contains an actual triangle or quadrilateral. -/
theorem capped_short_cycle (T : Fin (k+1) → Kind) :
    ∃ z : (capped T).Word,(capped T).IsCycleWord z ∧ size z≤4 := by
  have hleft (b : Bool) : (capped T).graph.Adj (Sum.inr false) (Sum.inl (left T 0 b)) :=
    ⟨Sum.inr (Sum.inl b),Or.inl ⟨rfl,rfl⟩⟩
  cases hkind : T 0 with
  | rung =>
    have hr : (T 0).network.graph.Adj ((T 0).left false) ((T 0).left true) := by
      rw [hkind]
      exact ⟨(),Or.inl ⟨rfl,rfl⟩⟩
    have hne : (Sum.inl (left T 0 false) : CappedVertex T)≠Sum.inl (left T 0 true) := by
      intro h
      have hh := (T 0).left_injective (by simpa only [Sum.inl.injEq,left,Sigma.mk.inj_iff,
        heq_eq_eq,true_and] using h)
      exact Bool.false_ne_true hh
    obtain ⟨z,hz,hlen⟩ := triangle (capped T) (by simp) (by simp) hne
      (hleft false) (tile_adj T 0 hr) ((hleft true).symm)
    exact ⟨z,hz,by omega⟩
  | square =>
    have hinj : Function.Injective (fun v : (T 0).Vertex =>
        (Sum.inl (Sigma.mk 0 v) : CappedVertex T)) := by
      intro a b h
      simpa only [Sum.inl.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
    have hadj (b c : Bool) : (capped T).graph.Adj
        (Sum.inl (left T 0 b)) (Sum.inl (right T 0 c)) := by
      apply tile_adj T 0
      rw [hkind]
      exact ⟨(b,c),Or.inl ⟨rfl,rfl⟩⟩
    obtain ⟨z,hz,hlen,_⟩ := NetworkFourCycle.exists_cycle_of_four_adj (capped T)
      (Sum.inl (left T 0 false)) (Sum.inl (right T 0 false))
      (Sum.inl (left T 0 true)) (Sum.inl (right T 0 true))
      (hinj.ne (by rw [hkind]; decide))
      (hinj.ne (by rw [hkind]; decide))
      (hinj.ne (by rw [hkind]; decide))
      (hinj.ne (by rw [hkind]; decide))
      (hinj.ne (by rw [hkind]; decide))
      (hinj.ne (by rw [hkind]; decide))
      (hadj false false) (hadj true false).symm (hadj true true) (hadj false true).symm
    exact ⟨z,hz,hlen⟩

omit [Fintype V'] [Fintype E'] in
/-- The rank-one pole contains the actual parallel-label digon. -/
theorem rank_one_short_cycle (N : Network V E) (s t : V)
    (hN : N.IsBridgelessTwoPole s t) (hr : networkRank N=1) :
    ∃ z : N.Word,N.IsCycleWord z ∧ size z≤4 := by
  obtain ⟨e,f,u,w,hef,he,hf,_⟩ := N.exists_two_edges_of_deg_two hN.deg_s
  have hu : u=t := (PoleSmallRank.vertex_eq_port_of_rank_one N s t hN hr u).resolve_left he.ne
  have hw : w=t := (PoleSmallRank.vertex_eq_port_of_rank_one N s t hN hr w).resolve_left hf.ne.symm
  subst u
  subst w
  have hz := (N.isPathWord_unitWord he.symm).add_closing hf
    (by simp [unitWord_apply,hef])
  refine ⟨unitWord e+unitWord f,hz,?_⟩
  have h := size_add_le (unitWord e : N.Word) (unitWord f)
  simp only [size_unitWord] at h
  omega

omit [Fintype V'] [Fintype E'] in
/-- Every actual full bridgeless two-pole has a cycle using at most four physical labels. -/
theorem exists_short_cycle (N : Network V E) (s t : V)
    (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t) :
    ∃ z : N.Word,N.IsCycleWord z ∧ size z≤4 := by
  rcases FullPairCappedLadder.rank_one_or_capped N hN hfull with hr | ⟨k,T,R,_,_,_⟩
  · exact rank_one_short_cycle N s t hN hr
  · obtain ⟨z,hz,hlen⟩ := capped_short_cycle T
    exact ⟨R.push z,R.isCycleWord_push hz,by rw [size_push]; exact hlen⟩

omit [Fintype V'] [Fintype E'] in
/-- Girth at least five excludes fullness in an actual bridgeless two-pole. -/
theorem not_full_of_no_short_cycle (N : Network V E) (s t : V)
    (hN : N.IsBridgelessTwoPole s t)
    (hg : ∀ z : N.Word,N.IsCycleWord z → 5≤size z) : ¬N.IsFullPair s t := by
  intro hfull
  obtain ⟨z,hz,hsize⟩ := exists_short_cycle N s t hN hfull
  have := hg z hz
  omega

end Erdos1016.ExactMaximumSupport.Shortening.FullPairShortCycle

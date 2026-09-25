import Erdos1016.CycleSpace.Graphical.ExceptionalPartners
import Erdos1016.CycleSpace.ForcedRegionCylinder

set_option autoImplicit false

/-!
# Exact cut correlations from graph deletion

This module derives the component ledger used in the exact link-correlation
formula. The graph definitions retain disconnected exteriors and empty
two-vertex deletions.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.LinkCorrelation

open ExceptionalPartners

variable {V : Type*} [Fintype V]

local instance linkCorrelationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

local instance componentFintype (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

def deletionHom (G : SimpleGraph V) (w : V) : deleted G w →g G :=
  (SimpleGraph.Embedding.induce (G := G) {v | v ≠ w}).toHom

/-- A deleted component is attached to the deleted vertex precisely when
its image is the original component of that vertex. -/
def Attached (G : SimpleGraph V) (w : V) (c : (deleted G w).ConnectedComponent) : Prop :=
  c.map (deletionHom G w) = G.connectedComponentMk w

omit [Fintype V] in
theorem attached_iff (G : SimpleGraph V) (w : V)
    (c : (deleted G w).ConnectedComponent) :
    Attached G w c ↔ ∃ u : DeletedVertex w,
      G.Adj w u.1 ∧ (deleted G w).connectedComponentMk u = c := by
  obtain ⟨t, ht⟩ := c.exists_rep
  have hmap : c.map (deletionHom G w) = G.connectedComponentMk t.1 := by
    rw [← ht]
    rfl
  constructor
  · intro hc
    have hr : G.Reachable w t.1 :=
      SimpleGraph.ConnectedComponent.exact ((hmap.symm.trans hc).symm)
    have hbranch : ∃ t' : DeletedVertex w, t'.1 ∈ ({t.1} : Finset V) ∧
        (deleted G w).connectedComponentMk t' = c ∧ G.Reachable w t'.1 :=
      ⟨t, by simp, ht, hr⟩
    exact ((terminalBranch_condition_iff G {t.1} w c).mp hbranch).2
  · rintro ⟨u, hu, huc⟩
    change c.map (deletionHom G w) = G.connectedComponentMk w
    rw [← huc]
    exact SimpleGraph.ConnectedComponent.sound hu.reachable.symm

/-- Outside the original component of the deleted vertex, deletion changes
neither connectivity nor component identities. -/
def unaffectedComponentMap (G : SimpleGraph V) (w : V) :
    {c : (deleted G w).ConnectedComponent // ¬ Attached G w c} →
      {c : G.ConnectedComponent // c ≠ G.connectedComponentMk w} :=
  fun c => ⟨c.1.map (deletionHom G w), c.2⟩

omit [Fintype V] in
theorem unaffectedComponentMap_injective (G : SimpleGraph V) (w : V) :
    Function.Injective (unaffectedComponentMap G w) := by
  intro c d heq
  obtain ⟨u, hu⟩ := c.1.exists_rep
  obtain ⟨v, hv⟩ := d.1.exists_rep
  have hmapc : c.1.map (deletionHom G w) = G.connectedComponentMk u.1 := by
    rw [← hu]
    rfl
  have hmapd : d.1.map (deletionHom G w) = G.connectedComponentMk v.1 := by
    rw [← hv]
    rfl
  have heq' : G.connectedComponentMk u.1 = G.connectedComponentMk v.1 := by
    rw [← hmapc, ← hmapd]
    exact congrArg Subtype.val heq
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact heq'
  have hsupport : ∀ x ∈ p.support, x ≠ w := by
    intro x hx heq
    subst x
    apply c.2
    change c.1.map (deletionHom G w) = G.connectedComponentMk w
    exact hmapc.trans (SimpleGraph.ConnectedComponent.sound (p.takeUntil w hx).reachable)
  let q := restrictWalk G {x | x ≠ w} p u.2 v.2 hsupport
  apply Subtype.ext
  exact hu.symm.trans ((SimpleGraph.ConnectedComponent.sound q.reachable).trans hv)

omit [Fintype V] in
theorem unaffectedComponentMap_surjective (G : SimpleGraph V) (w : V) :
    Function.Surjective (unaffectedComponentMap G w) := by
  intro c
  obtain ⟨v, hv⟩ := c.1.exists_rep
  have hvw : v ≠ w := by
    intro h
    exact c.2 (hv.symm.trans (congrArg G.connectedComponentMk h))
  let d := (deleted G w).connectedComponentMk ⟨v, hvw⟩
  have hd : d.map (deletionHom G w) = c.1 := hv
  refine ⟨⟨d, ?_⟩, ?_⟩
  · intro h
    exact c.2 (hd.symm.trans h)
  · exact Subtype.ext hd

/-- Exact component bijection away from the component of the deleted vertex. -/
def unaffectedComponentEquiv (G : SimpleGraph V) (w : V) :
    {c : (deleted G w).ConnectedComponent // ¬ Attached G w c} ≃
      {c : G.ConnectedComponent // c ≠ G.connectedComponentMk w} :=
  Equiv.ofBijective (unaffectedComponentMap G w)
    ⟨unaffectedComponentMap_injective G w, unaffectedComponentMap_surjective G w⟩

/-- The component containing `w`, plus precisely the unattached components
of `G-w`, account for every original component. -/
theorem component_card_eq_unattached_add_one (G : SimpleGraph V) (w : V) :
    Nat.card G.ConnectedComponent =
      Nat.card {c : (deleted G w).ConnectedComponent // ¬ Attached G w c} + 1 := by
  have he := Nat.card_congr (unaffectedComponentEquiv G w)
  rw [he]
  have hsplit := Fintype.card_subtype_compl (fun c : G.ConnectedComponent =>
    c = G.connectedComponentMk w)
  have hone := Fintype.card_subtype_eq (G.connectedComponentMk w)
  have hpos : 1 ≤ Fintype.card G.ConnectedComponent := by
    haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk w⟩
    exact Fintype.card_pos
  simp only [← Nat.card_eq_fintype_card] at hsplit hone hpos
  change Nat.card {c : G.ConnectedComponent // c ≠ G.connectedComponentMk w} =
    Nat.card G.ConnectedComponent - Nat.card {c : G.ConnectedComponent //
      c = G.connectedComponentMk w} at hsplit
  rw [hone] at hsplit
  omega

/-- Exchange the order in which two distinct vertices are deleted. -/
def swapDeletions (G : SimpleGraph V) (v : V) (w : DeletedVertex v) :
    deleted (deleted G v) w ≃g
      deleted (deleted G w.1) (⟨v, w.2.symm⟩ : DeletedVertex w.1) where
  toFun x := ⟨⟨x.1.1, fun h => x.2 (Subtype.ext h)⟩,
    fun h => x.1.2 (congrArg Subtype.val h)⟩
  invFun x := ⟨⟨x.1.1, fun h => x.2 (Subtype.ext h)⟩,
    fun h => x.1.2 (congrArg Subtype.val h)⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := Iff.rfl

def AttachedFirst (G : SimpleGraph V) (v : V) (w : DeletedVertex v)
    (c : (deleted (deleted G v) w).ConnectedComponent) : Prop :=
  Attached (deleted G w.1) ⟨v, w.2.symm⟩ ((swapDeletions G v w).connectedComponentEquiv c)

def AttachedSecond (G : SimpleGraph V) (v : V) (w : DeletedVertex v)
    (c : (deleted (deleted G v) w).ConnectedComponent) : Prop :=
  Attached (deleted G v) w c

theorem attachedFirst_iff (G : SimpleGraph V) (v : V) (w : DeletedVertex v)
    (c : (deleted (deleted G v) w).ConnectedComponent) :
    AttachedFirst G v w c ↔ ∃ x : DeletedVertex w,
      G.Adj v x.1.1 ∧ (deleted (deleted G v) w).connectedComponentMk x = c := by
  let e := swapDeletions G v w
  change Attached (deleted G w.1) ⟨v, w.2.symm⟩ (e.connectedComponentEquiv c) ↔ _
  rw [attached_iff]
  constructor
  · rintro ⟨x, hx, hc⟩
    refine ⟨e.symm x, hx, ?_⟩
    apply e.connectedComponentEquiv.injective
    simpa [SimpleGraph.Iso.connectedComponentEquiv] using hc
  · rintro ⟨x, hx, hc⟩
    refine ⟨e x, hx, ?_⟩
    simpa [SimpleGraph.Iso.connectedComponentEquiv] using congrArg e.connectedComponentEquiv hc

theorem attachedSecond_iff (G : SimpleGraph V) (v : V) (w : DeletedVertex v)
    (c : (deleted (deleted G v) w).ConnectedComponent) :
    AttachedSecond G v w c ↔ ∃ x : DeletedVertex w,
      G.Adj w.1 x.1.1 ∧ (deleted (deleted G v) w).connectedComponentMk x = c :=
  attached_iff (deleted G v) w c

omit [Fintype V] in
private theorem walk_boundary_adjacency {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (S : Set V) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ S
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

/-- Every component after two vertices are deleted from a connected graph
has an actual edge to at least one of those vertices. -/
theorem attachedFirst_or_second (G : SimpleGraph V) (hG : G.Connected)
    (v : V) (w : DeletedVertex v)
    (c : (deleted (deleted G v) w).ConnectedComponent) :
    AttachedFirst G v w c ∨ AttachedSecond G v w c := by
  obtain ⟨x, hx⟩ := c.exists_rep
  let S : Set V := {a | ∃ z : DeletedVertex w,
    z.1.1 = a ∧ (deleted (deleted G v) w).connectedComponentMk z = c}
  have hxin : x.1.1 ∈ S := ⟨x, rfl, hx⟩
  have hvout : v ∉ S := by
    rintro ⟨z, hz, _⟩
    exact z.1.2 hz
  obtain ⟨p⟩ := hG x.1.1 v
  obtain ⟨a, b, ha, hb, hab⟩ := walk_boundary_adjacency p S hxin hvout
  obtain ⟨z, hza, hzc⟩ := ha
  have hbends : b = v ∨ b = w.1 := by
    by_contra hn
    push_neg at hn
    let y : DeletedVertex w := ⟨⟨b, hn.1⟩, fun h => hn.2 (congrArg Subtype.val h)⟩
    have hzy : (deleted (deleted G v) w).Adj z y := by
      change G.Adj z.1.1 b
      simpa only [hza] using hab
    have hyc : (deleted (deleted G v) w).connectedComponentMk y = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hzy).symm.trans hzc
    exact hb ⟨y, rfl, hyc⟩
  rcases hbends with hbend | hbend
  · apply Or.inl
    apply (attachedFirst_iff G v w c).2
    exact ⟨z, by simpa only [hza, hbend] using hab.symm, hzc⟩
  · apply Or.inr
    apply (attachedSecond_iff G v w c).2
    exact ⟨z, by simpa only [hza, hbend] using hab.symm, hzc⟩

/-- Exact component ledger. The final summand counts only the components
incident to both deleted vertices; direct edges are added separately in the
cycle-rank ledger. -/
theorem double_deletion_component_ledger (G : SimpleGraph V) (hG : G.Connected)
    (v : V) (w : DeletedVertex v) :
    Nat.card (deleted G v).ConnectedComponent +
        Nat.card (deleted G w.1).ConnectedComponent +
        Nat.card {c : (deleted (deleted G v) w).ConnectedComponent //
          AttachedFirst G v w c ∧ AttachedSecond G v w c} =
      Nat.card (deleted (deleted G v) w).ConnectedComponent + 2 := by
  let D := (deleted (deleted G v) w).ConnectedComponent
  let A : D → Prop := AttachedFirst G v w
  let B : D → Prop := AttachedSecond G v w
  have hfirst := component_card_eq_unattached_add_one (deleted G v) w
  have hsecond := component_card_eq_unattached_add_one (deleted G w.1)
    (⟨v, w.2.symm⟩ : DeletedVertex w.1)
  let e := (swapDeletions G v w).connectedComponentEquiv
  let ea : {c : D // ¬ A c} ≃
      {c : (deleted (deleted G w.1) ⟨v, w.2.symm⟩).ConnectedComponent //
        ¬ Attached (deleted G w.1) ⟨v, w.2.symm⟩ c} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have ha := Nat.card_congr ea
  have hpartition : Nat.card {c : D // ¬ A c} + Nat.card {c : D // ¬ B c} +
      Nat.card {c : D // A c ∧ B c} = Nat.card D := by
    have hpoint (c : D) :
        (if ¬ A c then 1 else 0) + (if ¬ B c then 1 else 0) +
          (if A c ∧ B c then 1 else 0) = (1 : ℕ) := by
      have h : A c ∨ B c := attachedFirst_or_second G hG v w c
      by_cases ha : A c <;> by_cases hb : B c <;> simp [ha, hb]
      exact (h.elim ha hb).elim
    have hsum := congrArg (fun f : D → ℕ => ∑ c, f c) (funext hpoint)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.sum_add_distrib, ← Finset.card_filter, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using hsum
  change Nat.card (deleted G v).ConnectedComponent = Nat.card {c : D // ¬ B c} + 1 at hfirst
  rw [← ha] at hsecond
  change Nat.card (deleted G v).ConnectedComponent +
      Nat.card (deleted G w.1).ConnectedComponent + Nat.card {c : D // A c ∧ B c} =
    Nat.card D + 2
  omega

section Network

open BoundaryTrace BoundaryDecay
open Network

variable {E : Type*} [Fintype E]

local instance outsideVertexFintype (S : Finset V) : Fintype (Shore.OutsideVertex S) :=
  inferInstanceAs (Fintype {v : V // v ∉ S})

local instance outsideEdgeFintype (N : Network V E) (S : Finset V) :
    Fintype (Shore.OutsideEdge N S) :=
  inferInstanceAs (Fintype {e : E // N.src e ∉ S ∧ N.dst e ∉ S})

def DirectEdge (N : Network V E) (v w : V) :=
  {e : E // (N.src e = v ∧ N.dst e = w) ∨ (N.src e = w ∧ N.dst e = v)}

instance directEdgeFintype (N : Network V E) (v w : V) : Fintype (DirectEdge N v w) :=
  inferInstanceAs (Fintype {e : E //
    (N.src e = v ∧ N.dst e = w) ∨ (N.src e = w ∧ N.dst e = v)})

theorem outside_vertex_card_int (S : Finset V) :
    (Nat.card (Shore.OutsideVertex S) : ℤ) = (Nat.card V : ℤ) - S.card := by
  have h := Fintype.card_congr (Shore.verticesEquiv S)
  simp only [Fintype.card_sum, Fintype.card_coe] at h
  simp only [← Nat.card_eq_fintype_card] at h
  change S.card + Nat.card (Shore.OutsideVertex S) = Nat.card V at h
  omega

theorem outside_component_single (N : Network V E) (v : V) :
    Nat.card (Shore.outside N {v}).Component = Nat.card (deleted N.graph v).ConnectedComponent := by
  let e : (Shore.outside N {v}).graph ≃g deleted N.graph v := {
    toFun x := ⟨x.1, by simpa using x.2⟩
    invFun x := ⟨x.1, by simpa using x.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_rel_iff' := by
      intro x y
      change N.graph.Adj x.1 y.1 ↔ (Shore.outside N {v}).graph.Adj x y
      rw [Shore.outside_graph_eq_induce]
      rfl }
  exact Nat.card_congr e.connectedComponentEquiv

def outsidePairIso (N : Network V E) (v : V) (w : DeletedVertex v) :
    (Shore.outside N {v, w.1}).graph ≃g deleted (deleted N.graph v) w where
  toFun x := ⟨⟨x.1, by
      have h := x.2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact h.1⟩, by
    intro h
    have hx : x.1 = w.1 := congrArg Subtype.val h
    exact x.2 (by simp [hx])⟩
  invFun x := ⟨x.1.1, by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨x.1.2, fun h => x.2 (Subtype.ext h)⟩⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_rel_iff' := by
    intro x y
    change N.graph.Adj x.1 y.1 ↔ (Shore.outside N {v, w.1}).graph.Adj x y
    rw [Shore.outside_graph_eq_induce]
    rfl

theorem outside_component_pair (N : Network V E) (v : V) (w : DeletedVertex v) :
    Nat.card (Shore.outside N {v, w.1}).Component =
      Nat.card (deleted (deleted N.graph v) w).ConnectedComponent :=
  Nat.card_congr (outsidePairIso N v w).connectedComponentEquiv

omit [Fintype V] in
/-- Inclusion-exclusion on physical edge labels. Parallel direct edges are
counted separately. The no-loop field rules out the only degenerate cases. -/
theorem outside_edge_pair_ledger (N : Network V E) (v : V) (w : DeletedVertex v) :
    Nat.card (Shore.OutsideEdge N {v}) + Nat.card (Shore.OutsideEdge N {w.1}) +
        Nat.card (DirectEdge N v w.1) =
      Nat.card E + Nat.card (Shore.OutsideEdge N {v, w.1}) := by
  have hpoint (e : E) :
      (if N.src e ∉ ({v} : Finset V) ∧ N.dst e ∉ ({v} : Finset V) then 1 else 0) +
      (if N.src e ∉ ({w.1} : Finset V) ∧ N.dst e ∉ ({w.1} : Finset V) then 1 else 0) +
      (if (N.src e = v ∧ N.dst e = w.1) ∨ (N.src e = w.1 ∧ N.dst e = v) then 1 else 0) =
      (1 : ℕ) + (if N.src e ∉ ({v, w.1} : Finset V) ∧
        N.dst e ∉ ({v, w.1} : Finset V) then 1 else 0) := by
    have hvw := w.2
    have hloop := N.noLoops e
    by_cases hsv : N.src e = v <;> by_cases hdv : N.dst e = v <;>
      by_cases hsw : N.src e = w.1 <;> by_cases hdw : N.dst e = w.1 <;>
      simp_all
  have hsum := congrArg (fun f : E → ℕ => ∑ e, f e) (funext hpoint)
  simpa only [Shore.OutsideEdge, DirectEdge, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.sum_add_distrib, ← Finset.card_filter,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using hsum

/-- The exact rank combination underlying a pair of vertex-cut cylinders. -/
theorem outside_rank_pair_ledger (N : Network V E) (hN : N.graph.Connected)
    (v : V) (w : DeletedVertex v) :
    (networkRank N : ℤ) + networkRank (Shore.outside N {v, w.1}) -
        networkRank (Shore.outside N {v}) - networkRank (Shore.outside N {w.1}) =
      (Nat.card (DirectEdge N v w.1) : ℤ) +
        Nat.card {c : (deleted (deleted N.graph v) w).ConnectedComponent //
          AttachedFirst N.graph v w c ∧ AttachedSecond N.graph v w c} - 1 := by
  have hroot := connected_network_rank_int N hN
  have hleft := network_rank_int (Shore.outside N {v})
  have hright := network_rank_int (Shore.outside N {w.1})
  have hboth := network_rank_int (Shore.outside N {v, w.1})
  simp only [← Nat.card_eq_fintype_card] at hroot hleft hright hboth
  rw [outside_vertex_card_int {v}, outside_component_single N v] at hleft
  rw [outside_vertex_card_int {w.1}, outside_component_single N w.1] at hright
  rw [outside_vertex_card_int {v, w.1}, outside_component_pair N v w] at hboth
  have hvertices : ({v, w.1} : Finset V).card = 2 := by simp [w.2.symm]
  simp only [Finset.card_singleton, hvertices] at hleft hright hboth
  have hedges := outside_edge_pair_ledger N v w
  have hcomponents := double_deletion_component_ledger N.graph hN v w
  omega

def NetworkLink (N : Network V E) (v : V) (w : DeletedVertex v) :=
  DirectEdge N v w.1 ⊕
    {c : (deleted (deleted N.graph v) w).ConnectedComponent //
      AttachedFirst N.graph v w c ∧ AttachedSecond N.graph v w c}

def ZeroAt (N : Network V E) (v : V) (x : N.CycleSpace) : Prop :=
  ∀ e, N.src e = v ∨ N.dst e = v → x.1 e = 0

/-- Exact vertex-cut correlation for a connected labelled network. No
independence assertion or rank identity is assumed. -/
theorem network_zeroCut_pair (N : Network V E) (hN : N.graph.Connected)
    (v : V) (w : DeletedVertex v) :
    Finite.density (fun x : N.CycleSpace => ZeroAt N v x ∧ ZeroAt N w.1 x) =
      dyadic ((Nat.card (NetworkLink N v w) : ℤ) - 1) *
        Finite.density (ZeroAt N v) * Finite.density (ZeroAt N w.1) := by
  have hsingle (u : V) : (ZeroAt N u) =
      (fun x : N.CycleSpace => ForcedRegion N {u} (0 : N.CycleSpace).1 x.1) := by
    funext x
    simp only [ZeroAt, ForcedRegion, Finset.mem_singleton, ZeroMemClass.coe_zero,
      Pi.zero_apply]
  have hpair : (fun x : N.CycleSpace => ZeroAt N v x ∧ ZeroAt N w.1 x) =
      (fun x : N.CycleSpace => ForcedRegion N {v, w.1} (0 : N.CycleSpace).1 x.1) := by
    funext x
    simp only [ZeroAt, ForcedRegion, Finset.mem_insert, Finset.mem_singleton,
      ZeroMemClass.coe_zero, Pi.zero_apply]
    aesop
  rw [hpair, hsingle v, hsingle w.1]
  rw [forced_region_probability_dyadic, forced_region_probability_dyadic,
    forced_region_probability_dyadic, ← dyadic_add, ← dyadic_add]
  apply congrArg dyadic
  have hledger := outside_rank_pair_ledger N hN v w
  have hcard : Nat.card (NetworkLink N v w) = Nat.card (DirectEdge N v w.1) +
      Nat.card {c : (deleted (deleted N.graph v) w).ConnectedComponent //
        AttachedFirst N.graph v w c ∧ AttachedSecond N.graph v w c} := Nat.card_sum
  omega

end Network

end Erdos1016.LinkCorrelation

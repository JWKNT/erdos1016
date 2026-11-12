import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximumSupport.BridgelessLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Delete a tested port in the gap induction

The deleted vertex stays isolated and every surviving edge retains its
original physical label. Paths are split by their first physical edge.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleTerminalDeletion
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance terminalDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Delete the edges incident with `s`, retaining `s` as an isolated vertex. -/
def deleted (s : V) := N.sub (N.outside fun v => v = s)

omit [Fintype V] in
private theorem first_edge_unique {s t : V} {P : N.Word} (hP : N.IsPathWord s t P)
    {e g : E} (he : N.src e = s ∨ N.dst e = s) (hPe : P e ≠ 0)
    (hg : N.src g = s ∨ N.dst g = s) (hPg : P g ≠ 0) : g = e := by
  have hc : (Finset.univ.filter fun q => P q ≠ 0 ∧ (N.src q = s ∨ N.dst q = s)).card ≤ 1 :=
    hP.2.1.le
  exact Finset.card_le_one.mp hc g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPg, hg⟩)
    e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPe, he⟩)

omit [Fintype V] in
private theorem erase_first_subword {P : N.Word}
    {e : E} (hPe : P e ≠ 0) : N.IsSubword (P + unitWord e) P := by
  intro g hg
  by_cases hge : g = e
  · subst g
    exact hPe
  · have hval : (P + unitWord e) g = P g := by
      simp only [Pi.add_apply, unitWord_apply, if_neg (Ne.symm hge), add_zero]
    rwa [hval] at hg

/-- Removing the first physical edge gives a path entirely outside the tested port. -/
theorem erase_first {s t x : V} {P : N.Word} (hP : N.IsPathWord s t P)
    {e : E} (he : N.Joins e s x) (hxt : x ≠ t) (hPe : P e ≠ 0) :
    N.IsPathWord x t (P + unitWord e) ∧
      Within (P + unitWord e) (N.outside fun v => v = s) := by
  have hsub := erase_first_subword N hPe
  constructor
  · apply N.isPathWord_of_minimal hxt
    · rw [map_add, hP.boundary_eq, N.boundary_unitWord_of_joins he]
      change (unitWord s + unitWord t) + (unitWord s + unitWord x) =
        unitWord x + unitWord t
      calc
        _ = (unitWord s + unitWord s) + (unitWord x + unitWord t) := by abel
        _ = _ := by rw [word_add_self, zero_add]
    · intro z hz hz0
      exact hP.minimal z (fun g hg => hsub g (hz g hg)) hz0
  · intro g hg
    have hPs : P g ≠ 0 := hsub g hg
    have hnot : ¬ (N.src g = s ∨ N.dst g = s) := by
      intro hgs
      have hge := first_edge_unique N hP he.at_left hPe hgs hPs
      subst g
      apply hg
      simp only [Pi.add_apply, unitWord_apply, if_pos rfl, bit_eq_one_of_ne_zero hPe]
      exact bit_add_self 1
    exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

omit [Fintype V] in
private theorem degree_zero_outside {s : V} {P : N.Word}
    (hw : Within P (N.outside fun v => v = s)) : N.deg P s = 0 := by
  apply N.deg_eq_zero_of_forall
  intro g hg
  by_contra hp
  have hh := hw g hp
  rcases hg with h | h
  · exact hh.1 h
  · exact hh.2 h

/-- Add the first physical edge to a path in the deleted network. -/
theorem add_first {s t x : V} {P : N.Word} (hP : N.IsPathWord x t P)
    (hw : Within P (N.outside fun v => v = s)) {e : E} (he : N.Joins e s x) :
    N.IsPathWord s t (P + unitWord e) ∧ (P + unitWord e) e ≠ 0 := by
  have hs := degree_zero_outside N hw
  refine ⟨(hP.symm.add_pendant he.symm hs).symm, ?_⟩
  have hPe := N.eq_zero_of_deg_eq_zero hs he.at_left
  simp only [Pi.add_apply, hPe, unitWord_apply, if_pos rfl, zero_add]
  exact one_ne_zero

/-- Paths using a fixed first label correspond exactly to paths after deleting the port. -/
def firstEdgeEquiv {s t x : V} {e : E} (he : N.Joins e s x) (hxt : x ≠ t) :
    {P : N.Word // N.IsPathWord s t P ∧ P e ≠ 0} ≃
      {Q : N.Word // N.IsPathWord x t Q ∧ Within Q (N.outside fun v => v = s)} where
  toFun P := ⟨P.1 + unitWord e, erase_first N P.2.1 he hxt P.2.2⟩
  invFun Q := ⟨Q.1 + unitWord e, add_first N Q.2.1 Q.2.2 he⟩
  left_inv P := by
    apply Subtype.ext
    change P.1 + unitWord e + unitWord e = P.1
    rw [add_assoc, word_add_self, add_zero]
  right_inv Q := by
    apply Subtype.ext
    change Q.1 + unitWord e + unitWord e = Q.1
    rw [add_assoc, word_add_self, add_zero]

/-- The exact first-label path count, preserving all parallel labels. -/
theorem card_first_edge {s t x : V} {e : E} (he : N.Joins e s x) (hxt : x ≠ t) :
    Nat.card {P : N.Word // N.IsPathWord s t P ∧ P e ≠ 0} =
      (deleted N s).numPaths x t := by
  rw [deleted, N.numPaths_sub]
  exact Nat.card_congr (firstEdgeEquiv N he hxt)

/-- The two branches at a degree-two tested port give the exact path-count sum. -/
theorem numPaths_deleted_sum {s t x y : V} {e f : E}
    (T : N.Thread e f x s y) (hxt : x ≠ t) (hyt : y ≠ t) :
    N.numPaths s t = (deleted N s).numPaths x t + (deleted N s).numPaths y t := by
  have hparts : ∀ P : N.Word, N.IsPathWord s t P → P e ≠ 0 ∨ P f ≠ 0 := by
    intro P hP
    have hpos : 0 < (Finset.univ.filter fun g => P g ≠ 0 ∧
        (N.src g = s ∨ N.dst g = s)).card := by
      change 0 < N.deg P s
      rw [hP.2.1]
      decide
    obtain ⟨g, hg⟩ := Finset.card_pos.mp hpos
    have hg' := (Finset.mem_filter.mp hg).2
    rcases T.only g hg'.2 with h | h
    · exact Or.inl (h ▸ hg'.1)
    · exact Or.inr (h ▸ hg'.1)
  have hdisj : ∀ P : N.Word, ¬ ((N.IsPathWord s t P ∧ P e ≠ 0) ∧
      (N.IsPathWord s t P ∧ P f ≠ 0)) := by
    intro P h
    exact T.hef (first_edge_unique N h.1.1 T.hf.at_left h.2.2 T.he.at_right h.1.2)
  have hsplit : N.numPaths s t =
      Nat.card {P : N.Word // (N.IsPathWord s t P ∧ P e ≠ 0) ∨
        (N.IsPathWord s t P ∧ P f ≠ 0)} := by
    unfold Network.numPaths
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun P =>
      ⟨fun h => (hparts P h).elim (fun he => Or.inl ⟨h, he⟩)
        (fun hf => Or.inr ⟨h, hf⟩), fun h => h.elim And.left And.left⟩
  rw [hsplit, natCard_or_of_disjoint _ _ (fun P he hf => hdisj P ⟨he, hf⟩)]
  rw [card_first_edge N T.he.symm hxt, card_first_edge N T.hf hyt]

omit [Fintype V] [Fintype E] in
private theorem deleted_reachable_from {s v : V}
    (h : (deleted N s).graph.Reachable s v) : s = v := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨e, he⟩ := hadj
    rcases he with ⟨h, _⟩ | ⟨_, h⟩
    · exact (e.2.1 h).elim
    · exact (e.2.2 h).elim

/-- In a bridgeless connected network, deletion of a degree-two vertex
leaves all other vertices connected. The two neighbor labels may coincide here. -/
theorem reachable_deleted (s x y : V) (e f : E) (hconn : N.graph.Connected)
    (hbridge : N.IsBridgeless) (he : N.Joins e x s) (hf : N.Joins f s y)
    (honly : ∀ g, N.src g = s ∨ N.dst g = s → g = e ∨ g = f) :
    ∀ v, v ≠ s → (deleted N s).graph.Reachable x v := by
  let S : V → Prop := (deleted N s).graph.Reachable x
  have hx : S x := SimpleGraph.Reachable.refl _
  have hs : ¬ S s := by
    intro h
    exact he.ne (deleted_reachable_from N h.symm).symm
  have hxy : S y := by
    by_contra hy
    have hcut := BridgelessLayers.cutSize_ge_two N hconn hbridge S x s hx hs
    have hcross : ∀ g, N.crosses S g → g = e := by
      intro g hg
      have hat : N.src g = s ∨ N.dst g = s := by
        by_contra hnot
        have hh : N.src g ≠ s ∧ N.dst g ≠ s := not_or.mp hnot
        have ha : (deleted N s).graph.Adj (N.src g) (N.dst g) :=
          ⟨⟨g, hh⟩, Or.inl ⟨rfl, rfl⟩⟩
        exact hg ⟨fun h => h.trans ha.reachable, fun h => h.trans ha.symm.reachable⟩
      rcases honly g hat with h | h
      · exact h
      · subst g
        exfalso
        apply hg
        rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₁, h₂]
          exact iff_of_false hs hy
        · rw [h₁, h₂]
          exact iff_of_false hy hs
    have hle : N.cutSize S ≤ 1 := by
      unfold Network.cutSize
      rw [natCard_subtype_eq_card_filter]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact (hcross a (Finset.mem_filter.mp ha).2).trans
        (hcross b (Finset.mem_filter.mp hb).2).symm
    omega
  apply N.reachable_outside_of_connected (fun v => v = s) hconn
  intro g hg
  have hat : N.src g = s ∨ N.dst g = s := by
    by_contra hn
    exact hg (iff_of_false (not_or.mp hn).1 (not_or.mp hn).2)
  rcases honly g hat with h | h
  · subst g
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
      exact ⟨fun _ => hx, fun h => (h rfl).elim⟩
    · rw [h₁, h₂]
      exact ⟨fun h => (h rfl).elim, fun _ => hx⟩
  · subst g
    rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂]
      exact ⟨fun h => (h rfl).elim, fun _ => hxy⟩
    · rw [h₁, h₂]
      exact ⟨fun _ => hxy, fun h => (h rfl).elim⟩

omit [Fintype V] in
/-- The deleted vertex is literally isolated. -/
theorem degree_deleted_self (s : V) : (deleted N s).deg (fun _ => 1) s = 0 := by
  rw [deleted, N.deg_sub_ones]
  apply N.deg_eq_zero_of_forall
  intro g hg
  apply restrict_apply_of_neg
  intro h
  rcases hg with hg | hg
  · exact h.1 hg
  · exact h.2 hg

omit [Fintype V] in
/-- Deleting the two labels gives the exact physical degree ledger. -/
theorem degree_deleted_add {s x y : V} {e f : E} (hef : e ≠ f)
    (he : N.Joins e x s) (hf : N.Joins f s y)
    (honly : ∀ g, N.src g = s ∨ N.dst g = s → g = e ∨ g = f) (v : V) :
    (deleted N s).deg (fun _ => 1) v + N.deg (unitWord e) v + N.deg (unitWord f) v =
      N.deg (fun _ => 1) v := by
  let R : N.Word := restrict (fun _ => 1) (N.outside fun v => v = s)
  have hzero (g : E) (hg : N.src g = s ∨ N.dst g = s) : R g = 0 := by
    apply restrict_apply_of_neg
    intro h
    rcases hg with hg | hg
    · exact h.1 hg
    · exact h.2 hg
  have hones : R + unitWord e + unitWord f = (fun _ => (1 : Bit)) := by
    funext g
    by_cases hge : g = e
    · subst g
      simp [hzero e he.at_right, unitWord_apply, Ne.symm hef]
    by_cases hgf : g = f
    · subst g
      simp [hzero f hf.at_left, unitWord_apply, hef]
    have houtside : N.outside (fun v => v = s) g := by
      constructor <;> intro h
      · exact (honly g (Or.inl h)).elim hge hgf
      · exact (honly g (Or.inr h)).elim hge hgf
    simp [R, restrict_apply_of_pos _ houtside, unitWord_apply, Ne.symm hge, Ne.symm hgf]
  have hdisj₁ : ∀ g, R g ≠ 0 → (unitWord e : N.Word) g = 0 := by
    intro g hg
    have hne : e ≠ g := by intro h; subst g; exact hg (hzero e he.at_right)
    simp [unitWord_apply, hne]
  have hdisj₂ : ∀ g, (R + unitWord e) g ≠ 0 → (unitWord f : N.Word) g = 0 := by
    intro g hg
    have hne : f ≠ g := by
      intro h
      subst g
      apply hg
      simp [hzero f hf.at_left, unitWord_apply, hef]
    simp [unitWord_apply, hne]
  rw [deleted, N.deg_sub_ones]
  change N.deg R v + N.deg (unitWord e) v + N.deg (unitWord f) v = _
  rw [← N.deg_add_of_disjoint hdisj₁, ← N.deg_add_of_disjoint hdisj₂, hones]

omit [Fintype V] in
/-- Off the deleted port, exactly one incidence is removed at each distinct neighbor. -/
theorem degree_deleted_of_ne {s x y : V} {e f : E} (T : N.Thread e f x s y)
    {v : V} (hvs : v ≠ s) :
    (deleted N s).deg (fun _ => 1) v + (if v = x then 1 else 0) +
      (if v = y then 1 else 0) = N.deg (fun _ => 1) v := by
  have he : N.deg (unitWord e) v = if v = x then 1 else 0 := by
    by_cases h : v = x
    · subst v
      rw [if_pos rfl]
      exact N.deg_unitWord_eq_one T.he.at_left
    · rw [if_neg h]
      exact N.deg_unitWord_of_joins T.he h hvs
  have hf : N.deg (unitWord f) v = if v = y then 1 else 0 := by
    by_cases h : v = y
    · subst v
      rw [if_pos rfl]
      exact N.deg_unitWord_eq_one T.hf.at_right
    · rw [if_neg h]
      exact N.deg_unitWord_of_joins T.hf hvs h
  simpa only [he, hf] using degree_deleted_add N T.hef T.he T.hf T.only v

/-- Coincident neighbors would make the digon have only one physical way out,
contrary to bridgelessness. Nonadjacency keeps the other port outside that digon. -/
theorem neighbors_ne {s t x y : V} {e f : E} (hN : N.IsBridgelessTwoPole s t)
    (hnonadj : ¬ N.graph.Adj s t) (hef : e ≠ f)
    (he : N.Joins e x s) (hf : N.Joins f s y)
    (honly : ∀ g, N.src g = s ∨ N.dst g = s → g = e ∨ g = f) : x ≠ y := by
  intro hxy
  subst y
  have hxt : x ≠ t := by intro h; exact hnonadj ⟨e, h ▸ he.symm⟩
  let S : V → Prop := fun v => v = s ∨ v = x
  have hcut := BridgelessLayers.cutSize_ge_two N hN.connected hN.bridgeless S s t
    (Or.inl rfl) (fun h => h.elim hN.ne.symm hxt.symm)
  have heinside : N.inside S e := by
    rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      exact ⟨by simp [S, h₁], by simp [S, h₂]⟩
  have hfinside : N.inside S f := by
    rcases hf with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      exact ⟨by simp [S, h₁], by simp [S, h₂]⟩
  have hle : N.cutSize S ≤ (deleted N s).deg (fun _ => 1) x := by
    unfold Network.cutSize
    rw [natCard_subtype_eq_card_filter, deleted, N.deg_sub_ones]
    apply Finset.card_le_card
    intro g hg
    have hc := (Finset.mem_filter.mp hg).2
    have hs : N.src g ≠ s ∧ N.dst g ≠ s := by
      have hnot : ¬ (N.src g = s ∨ N.dst g = s) := by
        intro hat
        rcases honly g hat with h | h
        · exact N.not_crosses_of_inside heinside (h ▸ hc)
        · exact N.not_crosses_of_inside hfinside (h ▸ hc)
      exact not_or.mp hnot
    have hx : N.src g = x ∨ N.dst g = x := by
      by_contra hnot
      have hh := not_or.mp hnot
      exact hc (iff_of_false (fun h => h.elim hs.1 hh.1) (fun h => h.elim hs.2 hh.2))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, hx⟩
    exact (restrict_ne_zero_iff _ _ _).mpr ⟨hs, one_ne_zero⟩
  have hdegree := degree_deleted_add N hef he hf honly x
  rw [N.deg_unitWord_eq_one he.at_left, N.deg_unitWord_eq_one hf.at_right,
    hN.deg_other x he.ne hxt] at hdegree
  omega

/-- The rank drops by one when a degree-two vertex is deleted and its exterior stays connected. -/
theorem rank_deleted_add_one {s x y : V} {e f : E} (T : N.Thread e f x s y)
    (hconn : N.graph.Connected) (hbridge : N.IsBridgeless) :
    networkRank (deleted N s) + 1 = networkRank N := by
  let S : V → Prop := fun v => v = s
  have hin : ∀ v, S v → (N.sub (N.inside S)).graph.Reachable s v := by
    intro v hv
    exact hv ▸ SimpleGraph.Reachable.refl _
  have hout : ∀ v, ¬ S v → (N.sub (N.outside S)).graph.Reachable x v :=
    reachable_deleted N s x y e f hconn hbridge T.he T.hf T.only
  have hcut := N.networkRank_add_one_of_cut S (s₀ := s) (t₀ := x) rfl T.he.ne hconn hin hout
  have hcross : ∀ g, N.crosses S g ↔ g = e ∨ g = f := by
    intro g
    constructor
    · intro hc
      apply T.only
      by_contra hn
      exact hc (iff_of_false (not_or.mp hn).1 (not_or.mp hn).2)
    · rintro (rfl | rfl)
      · exact N.crosses_of_joins T.he.symm rfl T.he.ne
      · exact N.crosses_of_joins T.hf rfl T.hf.ne.symm
  have hcard : Nat.card {g : E // N.crosses S g} = 2 := by
    rw [natCard_subtype_eq_card_filter]
    have hset : (Finset.univ.filter (N.crosses S)) = {e, f} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcross,
        Finset.mem_insert, Finset.mem_singleton]
    rw [hset, Finset.card_pair T.hef]
  have hzero : networkRank (N.sub (N.inside S)) = 0 := by
    have hnocyc : (N.sub (N.inside S)).numCycles = 0 := by
      by_contra hp
      obtain ⟨Z, hZ⟩ := (N.sub (N.inside S)).exists_isCycleWord_of_rank_pos
        ((N.sub (N.inside S)).networkRank_pos_of_numCycles_pos (Nat.pos_of_ne_zero hp))
      apply hZ.1
      funext g
      have hs : N.src g.1 = s := g.2.1
      have hd : N.dst g.1 = s := g.2.2
      exact (N.noLoops g.1 (hs.trans hd.symm)).elim
    by_contra hr
    have hp := (N.sub (N.inside S)).numCycles_pos_of_rank_pos (Nat.pos_of_ne_zero hr)
    omega
  change networkRank (N.sub (N.outside S)) + 1 = networkRank N
  omega

omit [Fintype V] in
/-- The complete degree function of the deleted pole. -/
theorem deleted_degrees {s t x y : V} {e f : E} (hN : N.IsBridgelessTwoPole s t)
    (T : N.Thread e f x s y) (hxt : x ≠ t) (hyt : y ≠ t) (v : V) :
    (deleted N s).deg (fun _ => 1) v =
      if v = s then 0 else if v = x ∨ v = y ∨ v = t then 2 else 3 := by
  by_cases hvs : v = s
  · subst v
    rw [if_pos rfl, degree_deleted_self]
  rw [if_neg hvs]
  have hd := degree_deleted_of_ne N T hvs
  by_cases hvx : v = x
  · subst v
    rw [if_pos rfl, if_neg T.huw, hN.deg_other x T.he.ne hxt] at hd
    rw [if_pos (Or.inl rfl)]
    omega
  by_cases hvy : v = y
  · subst v
    rw [if_neg T.huw.symm, if_pos rfl, hN.deg_other y T.hf.ne.symm hyt] at hd
    rw [if_pos (Or.inr (Or.inl rfl))]
    omega
  rw [if_neg hvx, if_neg hvy, add_zero, add_zero] at hd
  by_cases hvt : v = t
  · subst v
    rw [hN.deg_t] at hd
    rw [if_pos (Or.inr (Or.inr rfl))]
    exact hd
  · rw [if_neg (fun h => h.elim hvx (fun h => h.elim hvy hvt))]
    exact hd.trans (hN.deg_other v hvs hvt)

/-- Deleting the nonadjacent tested port produces an actual weak three-pole,
lowers the rank by one, and splits the path count into the two neighbor paths.
The distinct-neighbor assertion includes the physical digon exclusion. -/
theorem exists_three_pole_deletion (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (hnonadj : ¬ N.graph.Adj s t) :
    ∃ (e f : E) (x y : V), N.Thread e f x s y ∧ x ≠ t ∧ y ≠ t ∧
      (deleted N s).IsWeakPole ∧
      (∀ v, (deleted N s).IsPort v ↔ v = x ∨ v = y ∨ v = t) ∧
      (deleted N s).deg (fun _ => 1) s = 0 ∧
      networkRank (deleted N s) + 1 = networkRank N ∧
      N.numPaths s t = (deleted N s).numPaths x t + (deleted N s).numPaths y t := by
  obtain ⟨e, f, x, y, hef, he, hf, honly⟩ := N.exists_two_edges_of_deg_two hN.deg_s
  have hxy : x ≠ y := neighbors_ne N hN hnonadj hef he hf honly
  have hxt : x ≠ t := by intro h; exact hnonadj ⟨e, h ▸ he.symm⟩
  have hyt : y ≠ t := by intro h; exact hnonadj ⟨f, h ▸ hf⟩
  let T : N.Thread e f x s y := ⟨he, hf, hef, hxy, honly⟩
  have hd := deleted_degrees N hN T hxt hyt
  have hports (v : V) : (deleted N s).IsPort v ↔ v = x ∨ v = y ∨ v = t := by
    change (deleted N s).deg (fun _ => 1) v = 2 ↔ _
    rw [hd]
    by_cases hvs : v = s
    · subst v
      simp only [if_pos rfl]
      constructor
      · intro h
        norm_num at h
      · intro h
        exact (h.elim he.ne.symm (fun h => h.elim hf.ne hN.ne)).elim
    · rw [if_neg hvs]
      split_ifs with h <;> simp [h]
  have hpole : (deleted N s).IsWeakPole := by
    constructor
    · intro v
      rw [hd]
      split_ifs <;> omega
    · intro u v hu hv
      have hus : u ≠ s := by intro h; subst u; rw [degree_deleted_self] at hu; omega
      have hvs : v ≠ s := by intro h; subst v; rw [degree_deleted_self] at hv; omega
      have hr := reachable_deleted N s x y e f hN.connected hN.bridgeless he hf honly
      exact (hr u hus).symm.trans (hr v hvs)
  exact ⟨e, f, x, y, T, hxt, hyt, hpole, hports, degree_deleted_self N s,
    rank_deleted_add_one N T hN.connected hN.bridgeless, numPaths_deleted_sum N T hxt hyt⟩

end Erdos1016.ExactMaximumSupport.PoleTerminalDeletion

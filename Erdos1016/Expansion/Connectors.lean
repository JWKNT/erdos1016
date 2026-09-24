import Erdos1016.Expansion.SmallComponents

set_option autoImplicit false

/-!
# Explicit connected protectors in an expanding subcubic graph

This supplies manuscript Lemma 3.2 by finite ball growth. The output consists
of actual owner vertices and retains every prescribed vertex. No diameter or
connector oracle is assumed. The numerical radius is a ceiling of a log ratio.
The high-degree apex is never used in this subcubic ball argument.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyConnectorsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- An actual walk with an explicit number of edges, used only to build
connected vertex sets. Repeated vertices are allowed. -/
inductive InSteps (G : PhysicalGraph) : ℕ → G.Vertex → G.Vertex → Prop
  | refl (v : G.Vertex) : InSteps G 0 v v
  | step {n : ℕ} {u v w : G.Vertex} (p : InSteps G n u v)
      (edge : G.toSimpleGraph.Adj v w) : InSteps G (n + 1) u w

namespace InSteps
variable {G : PhysicalGraph} {u v w : G.Vertex} {n m : ℕ}

theorem trans (p : InSteps G n u v) (q : InSteps G m v w) :
    InSteps G (n + m) u w := by
  induction q with
  | refl => simpa using p
  | step q he ih => simpa only [Nat.add_assoc] using InSteps.step (ih p) he

theorem symm (p : InSteps G n u v) : InSteps G n v u := by
  induction p with
  | refl => exact InSteps.refl _
  | @step n u v w p he ih =>
      have hfirst : InSteps G 1 w v := InSteps.step (InSteps.refl w) he.symm
      simpa only [Nat.add_comm 1 n] using hfirst.trans ih

/-- A walk supplies a connected support with at most length + 1 vertices.
This statement does not assert that the induced support is a path. -/
theorem connected_support (p : InSteps G n u v) :
    ∃ S : Finset G.Vertex, ConnectedRegion G S ∧ u ∈ S ∧ v ∈ S ∧ S.card ≤ n + 1 := by
  induction p with
  | refl v =>
      exact ⟨{v}, connectedRegion_singleton G v,
        Finset.mem_singleton_self _, Finset.mem_singleton_self _, by simp⟩
  | @step n u v w p he ih =>
      obtain ⟨S, hS, hu, hv, hsize⟩ := ih
      have hedge : (crossing G S {w}).Nonempty :=
        (crossing_nonempty_iff G S {w}).2
          ⟨v, hv, w, Finset.mem_singleton_self _, he⟩
      refine ⟨S ∪ {w}, connected_union_of_edge G hS (connectedRegion_singleton G w) hedge,
        Finset.mem_union_left _ hu,
        Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      have hc := Finset.card_union_le S {w}
      simp only [Finset.card_singleton] at hc
      omega

end InSteps

variable (G : PhysicalGraph)

def ball (r : ℕ) (u : G.Vertex) : Finset G.Vertex :=
  Finset.univ.filter fun v => ∃ k ≤ r, InSteps G k u v

@[simp] theorem mem_ball (r : ℕ) (u v : G.Vertex) :
    v ∈ ball G r u ↔ ∃ k ≤ r, InSteps G k u v := by simp [ball]

theorem self_mem_ball (r : ℕ) (u : G.Vertex) : u ∈ ball G r u :=
  (mem_ball G r u u).2 ⟨0, Nat.zero_le _, InSteps.refl u⟩

theorem ball_mono {r s : ℕ} (hrs : r ≤ s) (u : G.Vertex) : ball G r u ⊆ ball G s u := by
  intro v hv
  obtain ⟨k, hk, hp⟩ := (mem_ball G r u v).1 hv
  exact (mem_ball G s u v).2 ⟨k, hk.trans hrs, hp⟩

/-- The next layer is the actual outside-neighbor set, with no contraction. -/
theorem ball_succ (r : ℕ) (u : G.Vertex) :
    ball G (r + 1) u = ball G r u ∪ outsideNeighbors G (ball G r u) := by
  ext v
  constructor
  · intro hv
    by_cases hold : v ∈ ball G r u
    · exact Finset.mem_union_left _ hold
    · obtain ⟨k, hk, hp⟩ := (mem_ball G (r + 1) u v).1 hv
      cases hp with
      | refl => exact False.elim (hold (self_mem_ball G r u))
      | @step k u x v hp hxy =>
          have hx : x ∈ ball G r u := (mem_ball G r u x).2 ⟨k, by omega, hp⟩
          exact Finset.mem_union_right _
            ((mem_outsideNeighbors G _ _).2 ⟨hold, x, hx, hxy⟩)
  · intro hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ball_mono G (Nat.le_succ r) u hv
    · obtain ⟨_, x, hx, hxy⟩ := (mem_outsideNeighbors G _ _).1 hv
      obtain ⟨k, hk, hp⟩ := (mem_ball G r u x).1 hx
      exact (mem_ball G (r + 1) u v).2 ⟨k + 1, by omega, InSteps.step hp hxy⟩

theorem outsideNeighbors_disjoint (S : Finset G.Vertex) :
    Disjoint S (outsideNeighbors G S) := by
  apply Finset.disjoint_left.2
  intro v hv hn
  exact ((mem_outsideNeighbors G S v).1 hn).1 hv

theorem cut_eq_cross_outsideNeighbors (S : Finset G.Vertex) :
    ownerCut G S = crossing G S (outsideNeighbors G S) := by
  ext e
  constructor
  · intro he
    rcases (mem_ownerCut G S e).1 he with hs | hs
    · exact (mem_crossing G S _ e).2 (Or.inl ⟨hs.1,
        (mem_outsideNeighbors G S _).2 ⟨hs.2, G.src e, hs.1,
          e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩⟩)
    · exact (mem_crossing G S _ e).2 (Or.inr ⟨
        (mem_outsideNeighbors G S _).2 ⟨hs.1, G.dst e, hs.2,
          e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩, hs.2⟩)
  · intro he
    rcases (mem_crossing G S _ e).1 he with hs | hs
    · exact (mem_ownerCut G S e).2
        (Or.inl ⟨hs.1, ((mem_outsideNeighbors G S _).1 hs.2).1⟩)
    · exact (mem_ownerCut G S e).2
        (Or.inr ⟨((mem_outsideNeighbors G S _).1 hs.1).1, hs.2⟩)

/-- Each new layer vertex receives at most three old cut edges. -/
theorem cut_le_three_outsideNeighbors (hdeg : ∀ v, G.degree v ≤ 3)
    (S : Finset G.Vertex) : cutSize G S ≤ 3 * (outsideNeighbors G S).card := by
  let T := outsideNeighbors G S
  have hsub : crossing G S T ⊆ ownerCut G T := by
    intro e he
    rcases (mem_crossing G S T e).1 he with hs | hs
    · exact (mem_ownerCut G T e).2 (Or.inr ⟨
        fun ht => Finset.disjoint_left.1 (outsideNeighbors_disjoint G S) hs.1 ht, hs.2⟩)
    · exact (mem_ownerCut G T e).2 (Or.inl ⟨hs.1,
        fun ht => Finset.disjoint_left.1 (outsideNeighbors_disjoint G S) hs.2 ht⟩)
  have hc : cutSize G S ≤ cutSize G T := by
    unfold cutSize
    rw [cut_eq_cross_outsideNeighbors]
    exact Finset.card_le_card hsub
  have hsum := degree_sum_region G T
  have hupper : (∑ v ∈ T, G.degree v) ≤ 3 * T.card := by
    calc
      _ ≤ ∑ _v ∈ T, 3 := Finset.sum_le_sum fun v _ => hdeg v
      _ = 3 * T.card := by simp [Nat.mul_comm]
  have hcutT : cutSize G T ≤ 3 * T.card := by
    omega
  calc
    cutSize G S ≤ cutSize G T := hc
    _ ≤ 3 * T.card := hcutT

/-- Source ball growth factor 1 + h/3 before passing half of the owner. -/
theorem ball_growth (h : ℝ) (hh : 0 ≤ h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (r : ℕ) (u : G.Vertex) (hsmall : ((ball G r u).card : ℝ) ≤ (G.vertexCount : ℝ) / 2) :
    (1 + h / 3) * ((ball G r u).card : ℝ) ≤ (ball G (r + 1) u).card := by
  have hlow := small_region_expansion G h hExp (ball G r u) hsmall
  have hhigh : (cutSize G (ball G r u) : ℝ) ≤
      3 * ((outsideNeighbors G (ball G r u)).card : ℝ) := by
    exact_mod_cast cut_le_three_outsideNeighbors G hdeg (ball G r u)
  have hc : (ball G (r + 1) u).card =
      (ball G r u).card + (outsideNeighbors G (ball G r u)).card := by
    rw [ball_succ, Finset.card_union_of_disjoint (outsideNeighbors_disjoint G _)]
  have hc' : ((ball G (r + 1) u).card : ℝ) =
      (ball G r u).card + (outsideNeighbors G (ball G r u)).card := by exact_mod_cast hc
  nlinarith

/-- If a ball has not passed half, its order is at least the full geometric
lower bound. Monotonicity justifies every earlier application of expansion. -/
theorem ball_power_lower (h : ℝ) (hh : 0 ≤ h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (r : ℕ) (u : G.Vertex) (hsmall : ((ball G r u).card : ℝ) ≤ (G.vertexCount : ℝ) / 2) :
    (1 + h / 3) ^ r ≤ ((ball G r u).card : ℝ) := by
  have hbase : 0 ≤ 1 + h / 3 := by positivity
  have aux : ∀ k, k ≤ r → (1 + h / 3) ^ k ≤ ((ball G k u).card : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro _
        have hc : 1 ≤ (ball G 0 u).card := by
          have hp := Finset.card_pos.2 ⟨u, self_mem_ball G 0 u⟩
          omega
        simpa only [pow_zero] using (show (1 : ℝ) ≤ (ball G 0 u).card by exact_mod_cast hc)
    | succ k ih =>
        intro hk
        have hkr : k ≤ r := by omega
        have hmono : ((ball G k u).card : ℝ) ≤ (ball G r u).card := by
          exact_mod_cast Finset.card_le_card (ball_mono G hkr u)
        have hg := ball_growth G h hh hExp hdeg k u (hmono.trans hsmall)
        calc
          (1 + h / 3) ^ (k + 1) = (1 + h / 3) * (1 + h / 3) ^ k := by
            rw [pow_succ, mul_comm]
          _ ≤ (1 + h / 3) * ((ball G k u).card : ℝ) :=
            mul_le_mul_of_nonneg_left (ih hkr) hbase
          _ ≤ (ball G (k + 1) u).card := hg
  exact aux r le_rfl

theorem ball_more_than_half (h : ℝ) (hh : 0 ≤ h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (r : ℕ) (hpow : (G.vertexCount : ℝ) / 2 < (1 + h / 3) ^ r) (u : G.Vertex) :
    (G.vertexCount : ℝ) / 2 < ((ball G r u).card : ℝ) := by
  by_contra hn
  have hs := le_of_not_gt hn
  exact (not_le_of_gt hpow) ((ball_power_lower G h hh hExp hdeg r u hs).trans hs)

/-- An explicit logarithmic radius. It is defined for all h; its estimate
is used only under h > 0. -/
def connectorRadius (h : ℝ) : ℕ :=
  Nat.ceil (Real.log ((G.vertexCount : ℝ) + 1) / Real.log (1 + h / 3))

theorem connectorRadius_power (h : ℝ) (hh : 0 < h) :
    (G.vertexCount : ℝ) / 2 < (1 + h / 3) ^ connectorRadius G h := by
  have hb : 1 < 1 + h / 3 := by linarith
  have hlog : 0 < Real.log (1 + h / 3) := Real.log_pos hb
  have hceil : Real.log ((G.vertexCount : ℝ) + 1) / Real.log (1 + h / 3) ≤
      (connectorRadius G h : ℝ) :=
    (Nat.ceil_le).1 (le_refl (connectorRadius G h))
  have hnum : Real.log ((G.vertexCount : ℝ) + 1) ≤
      (connectorRadius G h : ℝ) * Real.log (1 + h / 3) :=
    (div_le_iff₀ hlog).1 hceil
  have hp : (G.vertexCount : ℝ) + 1 ≤ (1 + h / 3) ^ connectorRadius G h :=
    Real.le_pow_of_log_le (by linarith) hnum
  have hn := Nat.cast_nonneg (α := ℝ) G.vertexCount
  linarith

/-- Two balls of this radius intersect. The resulting connected support
has at most 2r+1 actual vertices. -/
theorem short_connection (h : ℝ) (hh : 0 ≤ h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (r : ℕ) (hpow : (G.vertexCount : ℝ) / 2 < (1 + h / 3) ^ r)
    (u v : G.Vertex) :
    ∃ S : Finset G.Vertex, ConnectedRegion G S ∧ u ∈ S ∧ v ∈ S ∧ S.card ≤ 2 * r + 1 := by
  have hu := ball_more_than_half G h hh hExp hdeg r hpow u
  have hv := ball_more_than_half G h hh hExp hdeg r hpow v
  have hex : ∃ z, z ∈ ball G r u ∧ z ∈ ball G r v := by
    by_contra hn
    have hd : Disjoint (ball G r u) (ball G r v) := by
      apply Finset.disjoint_left.2
      intro z hzU hzV
      exact hn ⟨z, hzU, hzV⟩
    have hc : (ball G r u).card + (ball G r v).card ≤ G.vertexCount := by
      rw [← Finset.card_union_of_disjoint hd]
      simpa only [Fintype.card_fin] using Finset.card_le_univ (ball G r u ∪ ball G r v)
    have hc' : ((ball G r u).card : ℝ) + (ball G r v).card ≤ G.vertexCount := by exact_mod_cast hc
    linarith
  obtain ⟨z, hzu, hzv⟩ := hex
  obtain ⟨k, hk, pk⟩ := (mem_ball G r u z).1 hzu
  obtain ⟨l, hl, pl⟩ := (mem_ball G r v z).1 hzv
  obtain ⟨S, hS, huS, hvS, hsize⟩ := (pk.trans pl.symm).connected_support
  exact ⟨S, hS, huS, hvS, by omega⟩

/-- A common root makes all chosen supports simultaneously connected. -/
theorem connected_union_common_root (U : Finset G.Vertex) (hU : ConnectedRegion G U)
    (A : Finset G.Vertex) (S : G.Vertex → Finset G.Vertex)
    (w : G.Vertex) (hw : w ∈ U)
    (hS : ∀ v ∈ A, ConnectedRegion G (S v)) (hroot : ∀ v ∈ A, w ∈ S v) :
    ConnectedRegion G (U ∪ A.biUnion S) := by
  have hwAll : w ∈ U ∪ A.biUnion S := Finset.mem_union_left _ hw
  have reach : ∀ v ∈ U ∪ A.biUnion S, InReach G (U ∪ A.biUnion S) w v := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact (hU.2 w hw v hv).mono Finset.subset_union_left
    · obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.1 hv
      have hsub : S x ⊆ U ∪ A.biUnion S := by
        intro z hz
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, hz⟩)
      exact ((hS x hx).2 w (hroot x hx) v hvx).mono hsub
  exact ⟨⟨w, hwAll⟩, fun u hu v hv => (reach u hu).symm.trans (reach v hv)⟩

/-- The simultaneous connector contains the original connected protector
and every new prescribed vertex. Its cardinal cost is explicit. -/
theorem connected_enlargement (h : ℝ) (hh : 0 ≤ h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (r : ℕ) (hpow : (G.vertexCount : ℝ) / 2 < (1 + h / 3) ^ r)
    (U : Finset G.Vertex) (hU : ConnectedRegion G U) (A : Finset G.Vertex) :
    ∃ W : Finset G.Vertex, ConnectedRegion G W ∧ U ⊆ W ∧ A ⊆ W ∧
      W.card ≤ U.card + A.card * (2 * r + 1) := by
  obtain ⟨w, hw⟩ := hU.1
  let S : G.Vertex → Finset G.Vertex := fun v =>
    Classical.choose (short_connection G h hh hExp hdeg r hpow w v)
  have hprops (v : G.Vertex) : ConnectedRegion G (S v) ∧ w ∈ S v ∧ v ∈ S v ∧
      (S v).card ≤ 2 * r + 1 :=
    Classical.choose_spec (short_connection G h hh hExp hdeg r hpow w v)
  refine ⟨U ∪ A.biUnion S,
    connected_union_common_root G U hU A S w hw
      (fun v _ => (hprops v).1) (fun v _ => (hprops v).2.1),
    Finset.subset_union_left, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, (hprops v).2.2.1⟩)
  · have h1 := Finset.card_union_le U (A.biUnion S)
    have h2 : (A.biUnion S).card ≤ ∑ v ∈ A, (S v).card := Finset.card_biUnion_le
    have h3 : (∑ v ∈ A, (S v).card) ≤ A.card * (2 * r + 1) := by
      calc
        _ ≤ ∑ _v ∈ A, (2 * r + 1) :=
          Finset.sum_le_sum (s := A) fun v _ => (hprops v).2.2.2
        _ = _ := by simp [Nat.mul_comm]
    omega

/-- The explicit connector used by both short-cycle branches. -/
theorem connected_enlargement_logarithmic (h : ℝ) (hh : 0 < h)
    (hExp : HasExpansion G Finset.univ h) (hdeg : ∀ v, G.degree v ≤ 3)
    (U : Finset G.Vertex) (hU : ConnectedRegion G U) (A : Finset G.Vertex) :
    ∃ W : Finset G.Vertex, ConnectedRegion G W ∧ U ⊆ W ∧ A ⊆ W ∧
      W.card ≤ U.card + A.card * (2 * connectorRadius G h + 1) :=
  connected_enlargement G h hh.le hExp hdeg (connectorRadius G h)
    (connectorRadius_power G h hh) U hU A

end Erdos1016.CycleSupply

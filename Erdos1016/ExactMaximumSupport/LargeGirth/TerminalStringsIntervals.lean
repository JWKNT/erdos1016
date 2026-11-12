import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringsSeparation

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual regions between terminal-string vertices

Intervals are connected components after deleting their two endpoints.
Their geometry is proved in the original graph, using the route-separation
property of the retained terminal forest.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
open SimpleGraph ExceptionalPartners
variable {V : Type*} [Fintype V]
local instance decidableIntervals (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual component of an induced graph, returned to the original vertices. -/
def reachRegion (G : SimpleGraph V) (S : Set V) (s : S) : Finset V :=
  Finset.univ.filter fun v => ∃ hv : v ∈ S, (G.induce S).Reachable s ⟨v, hv⟩

@[simp] theorem mem_reachRegion (G : SimpleGraph V) (S : Set V) (s : S) (v : V) :
    v ∈ reachRegion G S s ↔ ∃ hv : v ∈ S, (G.induce S).Reachable s ⟨v, hv⟩ := by
  simp only [reachRegion, Finset.mem_filter, Finset.mem_univ, true_and]

theorem reachRegion_subset (G : SimpleGraph V) (S : Set V) (s : S) :
    (↑(reachRegion G S s) : Set V) ⊆ S := fun _ h => ((mem_reachRegion G S s _).mp h).choose

theorem seed_mem_reachRegion (G : SimpleGraph V) (S : Set V) (s : S) :
    s.1 ∈ reachRegion G S s := (mem_reachRegion G S s _).mpr ⟨s.2, Reachable.rfl⟩

theorem reachRegion_connected (G : SimpleGraph V) (S : Set V) (s : S) :
    (G.induce (↑(reachRegion G S s) : Set V)).Connected := by
  let c := (G.induce S).connectedComponentMk s
  let f : (G.induce S).induce c.supp →g G.induce (↑(reachRegion G S s) : Set V) := {
    toFun := fun v => ⟨v.1.1, (mem_reachRegion G S s _).mpr ⟨v.1.2,
      ConnectedComponent.exact ((ConnectedComponent.mem_supp_iff c v.1).mp v.2).symm⟩⟩
    map_rel' := by intro a b h; exact h }
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨hv, hr⟩ := (mem_reachRegion G S s v.1).mp v.2
    refine ⟨⟨⟨v.1, hv⟩, ?_⟩, Subtype.ext rfl⟩
    exact (ConnectedComponent.mem_supp_iff c _).mpr (ConnectedComponent.sound hr).symm
  exact c.connected_induce_supp.map f hsurj

theorem reachRegion_boundary (G : SimpleGraph V) (S : Set V) (s : S)
    {v w : V} (hv : v ∈ reachRegion G S s) (hvw : G.Adj v w)
    (hw : w ∉ reachRegion G S s) : w ∉ S := by
  intro hwS
  obtain ⟨hvS, hr⟩ := (mem_reachRegion G S s v).mp hv
  exact hw ((mem_reachRegion G S s w).mpr ⟨hwS,
    hr.trans (show (G.induce S).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hvw).reachable⟩)

omit [Fintype V] in
/-- Connectivity inside an actual region can be read after deleting any
vertex outside that region. -/
theorem connected_reachable_deleted (G : SimpleGraph V) (M : Finset V)
    (hM : (G.induce (↑M : Set V)).Connected) {a b v : V}
    (ha : a ∈ M) (hb : b ∈ M) (hv : v ∉ M) :
    (deleted G v).Reachable ⟨a, fun h => hv (h ▸ ha)⟩ ⟨b, fun h => hv (h ▸ hb)⟩ := by
  let f : G.induce (↑M : Set V) →g deleted G v := {
    toFun := fun u => ⟨u.1, fun h => hv (h ▸ u.2)⟩
    map_rel' := by intro u w h; exact h }
  exact (hM.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map f


omit [Fintype V] in
/-- A separating route vertex outside a connected region is absent from
all simple auxiliary routes between vertices of that region. -/
theorem route_avoids (G T : SimpleGraph V) (M : Finset V)
    (hM : (G.induce (↑M : Set V)).Connected) {a b v : V}
    (ha : a∈M) (hb : b∈M) (hv : v∉M) (hc : CutsRoutes G T v)
    (q : T.Walk a b) (hq : q.IsPath) : v ∉ q.support := by
  intro hmem
  exact hc a b q hq hmem _ _ (connected_reachable_deleted G M hM ha hb hv)

omit [Fintype V] in
/-- A walk cannot leave a region if its boundary consists of two avoided vertices. -/
theorem walk_stays (T : SimpleGraph V) (M : Finset V) (x y : V)
    (hboundary : ∀u∈M,∀w,T.Adj u w→w∉M→w=x∨w=y)
    {a b : V} (q : T.Walk a b) (ha : a∈M)
    (havoid : ∀v∈q.support,v≠x ∧ v≠y) : b∈M := by
  induction q with
  | nil => exact ha
  | @cons a b c hab q ih =>
      have hb : b∈M := by
        by_contra hn
        rcases hboundary a ha b hab hn with he | he
        · exact (havoid b (by simp)).1 he
        · exact (havoid b (by simp)).2 he
      exact ih hb (by intro v hv; exact havoid v (by simp [hv]))


omit [Fintype V] in
/-- Route separation separates any two distinct auxiliary neighbors. -/
theorem cutsRoutes_neighbors (G T : SimpleGraph V) {v a b : V}
    (hc : CutsRoutes G T v) (ha : T.Adj v a) (hb : T.Adj v b) (hab : a≠b) :
    ¬(deleted G v).Reachable ⟨a,ha.ne.symm⟩ ⟨b,hb.ne.symm⟩ := by
  let q : T.Walk a b := Walk.cons ha.symm (Walk.cons hb Walk.nil)
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    simp [q,ha.ne,ha.ne.symm,hb.ne,hab]
  exact hc a b q hq (by simp [q]) _ _

section Indices
variable {T : SimpleGraph V} {a b : V} (p : T.Walk a b)

omit [Fintype V] in
/-- Consecutive walk indices give reachability in any containing induced set. -/
theorem indices_reachable (S : Set V) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length)
    (hS : ∀ k, i ≤ k → k ≤ j → p.getVert k ∈ S) :
    (T.induce S).Reachable ⟨p.getVert i, hS i le_rfl hij⟩ ⟨p.getVert j, hS j hij le_rfl⟩ := by
  revert hj hS
  induction j, hij using Nat.le_induction with
  | base => intro hj hS; exact Reachable.rfl
  | succ j hij ih =>
      intro hj hS
      have hprev := ih (by omega) (fun k hk hkj => hS k hk (by omega))
      exact hprev.trans (show (T.induce S).Adj
        ⟨p.getVert j, hS j hij (by omega)⟩
        ⟨p.getVert (j+1), hS (j+1) (by omega) le_rfl⟩ from p.adj_getVert_succ (by omega)).reachable

def openSegment (i j : ℕ) : Finset V := (Finset.Ioo i j).image p.getVert

omit [Fintype V] in
@[simp] theorem mem_openSegment (i j : ℕ) (v : V) :
    v ∈ openSegment p i j ↔ ∃ k, i < k ∧ k < j ∧ p.getVert k = v := by
  simp only [openSegment, Finset.mem_image, Finset.mem_Ioo, and_assoc]

omit [Fintype V] in
theorem openSegment_avoids (hp : p.IsPath) (i j : ℕ) (hij : i < j) (hj : j ≤ p.length)
    {v : V} (hv : v ∈ openSegment p i j) : v ≠ p.getVert i ∧ v ≠ p.getVert j := by
  obtain ⟨k, hik, hkj, rfl⟩ := (mem_openSegment p i j v).mp hv
  constructor <;> intro he
  · have hh := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega
  · have hh := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega

/-- Inside a degree-two simple path, only its two endpoints can leave the
open segment. This assertion concerns the auxiliary forest T. -/
theorem openSegment_boundary (hp : p.IsPath) (i j : ℕ) (hj : j ≤ p.length)
    (hd : ∀ k, i < k → k < j → T.degree (p.getVert k) = 2)
    {v w : V} (hv : v ∈ openSegment p i j) (hvw : T.Adj v w)
    (hw : w ∉ openSegment p i j) : w = p.getVert i ∨ w = p.getVert j := by
  obtain ⟨k, hik, hkj, rfl⟩ := (mem_openSegment p i j v).mp hv
  have hprev : T.Adj (p.getVert k) (p.getVert (k-1)) := by
    simpa only [show k-1+1=k by omega] using (p.adj_getVert_succ (by omega : k-1<p.length)).symm
  have hnext : T.Adj (p.getVert k) (p.getVert (k+1)) := p.adj_getVert_succ (by omega)
  have hne : p.getVert (k-1) ≠ p.getVert (k+1) := by
    intro he
    have hh := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega
  have heq : ({p.getVert (k-1), p.getVert (k+1)} : Finset V) = T.neighborFinset (p.getVert k) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (T.mem_neighborFinset _ _).mpr hprev
      · exact (T.mem_neighborFinset _ _).mpr hnext
    · simp [hne, hd k hik hkj]
  have hw' := (T.mem_neighborFinset _ _).mpr hvw
  rw [← heq] at hw'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
  rcases hw' with rfl | rfl
  · have hk : k-1=i := by
      by_contra hn
      exact hw ((mem_openSegment p i j _).mpr ⟨k-1, by omega, by omega, rfl⟩)
    exact Or.inl (congrArg p.getVert hk)
  · have hk : k+1=j := by
      by_contra hn
      exact hw ((mem_openSegment p i j _).mpr ⟨k+1, by omega, by omega, rfl⟩)
    exact Or.inr (congrArg p.getVert hk)


omit [Fintype V] in
/-- Every nonempty open path segment is connected in the auxiliary graph. -/
theorem openSegment_connected (i j : ℕ) (hgap : i+2 ≤ j) (hj : j ≤ p.length) :
    (T.induce (↑(openSegment p i j) : Set V)).Connected := by
  have hseed : p.getVert (i+1) ∈ openSegment p i j :=
    (mem_openSegment p i j _).mpr ⟨i+1, by omega, by omega, rfl⟩
  letI : Nonempty (↑(openSegment p i j) : Set V) := ⟨⟨p.getVert (i+1), hseed⟩⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨k, hik, hkj, hk⟩ := (mem_openSegment p i j _).mp u.2
  obtain ⟨l, hil, hlj, hl⟩ := (mem_openSegment p i j _).mp v.2
  have hbetween (x y : ℕ) (hix : i<x) (hxy : x≤y) (hyj : y<j) :
      (T.induce (↑(openSegment p i j) : Set V)).Reachable
        ⟨p.getVert x, (mem_openSegment p i j _).mpr ⟨x,hix,by omega,rfl⟩⟩
        ⟨p.getVert y, (mem_openSegment p i j _).mpr ⟨y,by omega,hyj,rfl⟩⟩ :=
    indices_reachable p _ x y hxy (by omega) (by
      intro z hxz hzy
      exact (mem_openSegment p i j _).mpr ⟨z,by omega,by omega,rfl⟩)
  by_cases hkl : k≤l
  · have h := hbetween k l hik hkl hlj
    simpa only [hk,hl] using h
  · have h := (hbetween l k hil (by omega) hkj).symm
    simpa only [hk,hl] using h

/-- The component between two separated path positions in the original graph. -/
def betweenRegion (G : SimpleGraph V) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length) : Finset V :=
  reachRegion G {v | v≠p.getVert i ∧ v≠p.getVert j}
    ⟨p.getVert (i+1), openSegment_avoids p hp i j (by omega) hj
      ((mem_openSegment p i j _).mpr ⟨i+1,by omega,by omega,rfl⟩)⟩

theorem betweenRegion_connected (G : SimpleGraph V) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length) :
    (G.induce (↑(betweenRegion p G hp i j hgap hj) : Set V)).Connected :=
  reachRegion_connected _ _ _

theorem betweenRegion_avoids (G : SimpleGraph V) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length) {v : V}
    (hv : v ∈ betweenRegion p G hp i j hgap hj) :
    v≠p.getVert i ∧ v≠p.getVert j := by
  exact reachRegion_subset G {v | v≠p.getVert i ∧ v≠p.getVert j} _ hv

theorem betweenRegion_boundary (G : SimpleGraph V) (hp : p.IsPath) (i j : ℕ)
    (hgap : i+2 ≤ j) (hj : j ≤ p.length) {v w : V}
    (hv : v ∈ betweenRegion p G hp i j hgap hj) (hadj : G.Adj v w)
    (hw : w ∉ betweenRegion p G hp i j hgap hj) :
    w=p.getVert i ∨ w=p.getVert j := by
  have hn := reachRegion_boundary _ _ _ hv hadj hw
  simpa only [Set.mem_setOf_eq, not_and_or, not_not] using hn

theorem openSegment_subset_between (G : SimpleGraph V) (hTG : T≤G)
    (hp : p.IsPath) (i j : ℕ) (hgap : i+2 ≤ j) (hj : j ≤ p.length) :
    openSegment p i j ⊆ betweenRegion p G hp i j hgap hj := by
  intro v hv
  let f : T.induce (↑(openSegment p i j) : Set V) →g
      G.induce {v | v≠p.getVert i ∧ v≠p.getVert j} := {
    toFun := fun u => ⟨u.1,openSegment_avoids p hp i j (by omega) hj u.2⟩
    map_rel' := by intro u w h; exact hTG h }
  have hseed : p.getVert (i+1) ∈ openSegment p i j :=
    (mem_openSegment p i j _).mpr ⟨i+1,by omega,by omega,rfl⟩
  exact (mem_reachRegion _ _ _ _).mpr ⟨_,
    ((openSegment_connected p i j hgap hj).preconnected
      ⟨p.getVert (i+1),hseed⟩ ⟨v,hv⟩).map f⟩


/-- The actual between-region contains no feet. -/
theorem betweenRegion_no_feet (G : SimpleGraph V) (hTG : T≤G)
    (hp : p.IsPath) (B : Finset V) (hfeet : ∀v∈p.support,v∉B)
    (i j : ℕ) (hgap : i+2 ≤ j) (hj : j≤p.length)
    (hd : ∀k,i<k→k<j→T.degree (p.getVert k)=2)
    (hiCuts : CutsRoutes G T (p.getVert i))
    (hjCuts : CutsRoutes G T (p.getVert j))
    (hterm : ∀t∈B,G.Reachable (p.getVert (i+1)) t→T.Reachable (p.getVert (i+1)) t) :
    Disjoint (betweenRegion p G hp i j hgap hj) B := by
  apply Finset.disjoint_left.mpr
  intro t ht htB
  let M := betweenRegion p G hp i j hgap hj
  have hseedI : p.getVert (i+1)∈openSegment p i j :=
    (mem_openSegment p i j _).mpr ⟨i+1,by omega,by omega,rfl⟩
  have hseed : p.getVert (i+1)∈M := openSegment_subset_between p G hTG hp i j hgap hj hseedI
  have hconn := betweenRegion_connected p G hp i j hgap hj
  have hiout : p.getVert i∉M := fun hm => (betweenRegion_avoids p G hp i j hgap hj hm).1 rfl
  have hjout : p.getVert j∉M := fun hm => (betweenRegion_avoids p G hp i j hgap hj hm).2 rfl
  have hreach : G.Reachable (p.getVert (i+1)) t :=
    (hconn.preconnected ⟨_,hseed⟩ ⟨_,ht⟩).map (SimpleGraph.Embedding.induce (↑M : Set V)).toHom
  obtain ⟨q,hq⟩ := (hterm t htB hreach).exists_isPath
  have hqi := route_avoids G T M hconn hseed ht hiout hiCuts q hq
  have hqj := route_avoids G T M hconn hseed ht hjout hjCuts q hq
  have htI := walk_stays T (openSegment p i j) (p.getVert i) (p.getVert j)
    (fun _ hu _ hadj hw => openSegment_boundary p hp i j hj hd hu hadj hw)
    q hseedI (fun v hv => ⟨fun he => hqi (he ▸ hv),fun he => hqj (he ▸ hv)⟩)
  obtain ⟨k,_,_,rfl⟩ := (mem_openSegment p i j _).mp htI
  exact hfeet _ (p.getVert_mem_support k) htB


omit [Fintype V] in
/-- A path-index interval avoiding one position remains connected after its deletion. -/
theorem indices_reachable_avoiding (G : SimpleGraph V) (hTG : T≤G)
    (hp : p.IsPath) (i j k : ℕ) (hij : i≤j) (hj : j≤p.length) (hk : k≤p.length)
    (hout : j < k ∨ k < i) :
    ∃hi : p.getVert i≠p.getVert k, ∃hj' : p.getVert j≠p.getVert k,
      (deleted G (p.getVert k)).Reachable ⟨p.getVert i,hi⟩ ⟨p.getVert j,hj'⟩ := by
  have hne (l : ℕ) (hil : i≤l) (hlj : l≤j) : p.getVert l≠p.getVert k := by
    intro he
    have heq := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega
  refine ⟨hne i le_rfl hij,hne j hij le_rfl,?_⟩
  let f : T.induce {v | v≠p.getVert k} →g deleted G (p.getVert k) := {
    toFun := id
    map_rel' := by intro u v h; exact hTG h }
  exact (indices_reachable p {v | v≠p.getVert k} i j hij hj hne).map f

omit [Fintype V] in
/-- A separating interior path position separates all positions on its two sides. -/
theorem separated_indices (G : SimpleGraph V) (hTG : T≤G) (hp : p.IsPath)
    (i k j : ℕ) (hik : i<k) (hkj : k<j) (hj : j≤p.length)
    (hc : CutsRoutes G T (p.getVert k))
    (hi : p.getVert i≠p.getVert k) (hj' : p.getVert j≠p.getVert k) :
    ¬(deleted G (p.getVert k)).Reachable ⟨p.getVert i,hi⟩ ⟨p.getVert j,hj'⟩ := by
  have hprev : T.Adj (p.getVert k) (p.getVert (k-1)) := by
    simpa only [show k-1+1=k by omega] using (p.adj_getVert_succ (by omega : k-1<p.length)).symm
  have hnext : T.Adj (p.getVert k) (p.getVert (k+1)) := p.adj_getVert_succ (by omega)
  have hne : p.getVert (k-1)≠p.getVert (k+1) := by
    intro he
    have heq := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) he
    omega
  obtain ⟨_,_,hl⟩ := indices_reachable_avoiding p G hTG hp i (k-1) k
    (by omega) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨_,_,hr⟩ := indices_reachable_avoiding p G hTG hp (k+1) j k
    (by omega) hj (by omega) (Or.inr (by omega))
  intro h
  exact cutsRoutes_neighbors G T hc hprev hnext hne (hl.symm.trans (h.trans hr.symm))

/-- Ordered, nonoverlapping string intervals give disjoint actual regions. -/
theorem betweenRegion_disjoint (G : SimpleGraph V) (hTG : T≤G) (hp : p.IsPath)
    (i j k l : ℕ) (hij : i+2≤j) (hkl : k+2≤l) (hjk : j≤k) (hl : l≤p.length)
    (hjCuts : CutsRoutes G T (p.getVert j)) (hkCuts : CutsRoutes G T (p.getVert k)) :
    Disjoint (betweenRegion p G hp i j hij (by omega))
      (betweenRegion p G hp k l hkl hl) := by
  let M := betweenRegion p G hp i j hij (by omega)
  let N := betweenRegion p G hp k l hkl hl
  have hm := betweenRegion_connected p G hp i j hij (by omega)
  have hn := betweenRegion_connected p G hp k l hkl hl
  have hmi : p.getVert (i+1)∈M := openSegment_subset_between p G hTG hp i j hij (by omega)
    ((mem_openSegment p i j _).mpr ⟨i+1,by omega,by omega,rfl⟩)
  have hnk : p.getVert (k+1)∈N := openSegment_subset_between p G hTG hp k l hkl hl
    ((mem_openSegment p k l _).mpr ⟨k+1,by omega,by omega,rfl⟩)
  have hjM : p.getVert j∉M := fun h => (betweenRegion_avoids p G hp i j hij (by omega) h).2 rfl
  have hkN : p.getVert k∉N := fun h => (betweenRegion_avoids p G hp k l hkl hl h).1 rfl
  have hjN : p.getVert j∉N := by
    by_cases he : j=k
    · simpa only [he] using hkN
    · intro hjN
      have hr := connected_reachable_deleted G N hn hjN hnk hkN
      exact separated_indices p G hTG hp j k (k+1) (by omega) (by omega) (by omega)
        hkCuts _ _ hr
  apply Finset.disjoint_left.mpr
  intro v hvM hvN
  have hr1 := connected_reachable_deleted G M hm hmi hvM hjM
  have hr2 := connected_reachable_deleted G N hn hvN hnk hjN
  exact separated_indices p G hTG hp (i+1) j (k+1) (by omega) (by omega) (by omega)
    hjCuts _ _ (hr1.trans hr2)

end Indices
end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings

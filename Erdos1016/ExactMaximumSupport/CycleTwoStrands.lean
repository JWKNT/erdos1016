import Erdos1016.ExactMaximumSupport.CycleLayerSpan
import Erdos1016.ExactMaximumSupport.DistanceFourLayers
import Erdos1016.ExactMaximum.PoleMatchings

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Two physical strands through a layer of size two

Selected cut parity forces two crossings at each threshold.
Concentrating all crossings at one layer vertex would disconnect the cycle.
Each layer vertex therefore has one incoming and one outgoing selected label.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.CycleTwoStrands
open BoundaryTrace BoundaryTrace.Network

local instance twoStrandsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

private def incident (z : N.Word) (v : V) : Finset E :=
  Finset.univ.filter fun e => z e ≠ 0 ∧ (N.src e = v ∨ N.dst e = v)

/-- Incoming selected labels at a vertex, across the lower threshold. -/
def incoming (level : V → ℕ) (z : N.Word) (j : ℕ) (v : V) : Finset E :=
  (N.crossSet (fun w => level w < j) z).filter (fun e => N.src e = v ∨ N.dst e = v)

/-- Outgoing selected labels at a vertex, across the upper threshold. -/
def outgoing (level : V → ℕ) (z : N.Word) (j : ℕ) (v : V) : Finset E :=
  (N.crossSet (fun w => level w ≤ j) z).filter (fun e => N.src e = v ∨ N.dst e = v)

omit [Fintype V] in
/-- Each incoming label joins the layer vertex to the immediately preceding level. -/
theorem mem_incoming_iff (level : V → ℕ) (z : N.Word) (j : ℕ) (v : V)
    (hv : level v = j)
    (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1) (e : E) :
    e ∈ incoming N level z j v ↔ z e ≠ 0 ∧
      ((N.src e = v ∧ level (N.dst e) + 1 = j) ∨
        (N.dst e = v ∧ level (N.src e) + 1 = j)) := by
  constructor
  · intro he
    obtain ⟨hc,hi⟩ := Finset.mem_filter.mp he
    obtain ⟨hc,hz⟩ := N.mem_crossSet.mp hc
    have hd := hlip e
    change ¬ (level (N.src e) < j ↔ level (N.dst e) < j) at hc
    refine ⟨hz,?_⟩
    rcases hi with hs | ht
    · left
      refine ⟨hs,?_⟩
      rw [hs,hv] at hc hd
      omega
    · right
      refine ⟨ht,?_⟩
      rw [ht,hv] at hc hd
      omega
  · rintro ⟨hz,hi⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply N.mem_crossSet.mpr
      refine ⟨?_,hz⟩
      change ¬ (level (N.src e) < j ↔ level (N.dst e) < j)
      rcases hi with ⟨hs,h⟩ | ⟨ht,h⟩
      · rw [hs,hv]
        omega
      · rw [ht,hv]
        omega
    · exact hi.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

omit [Fintype V] in
/-- Each outgoing label joins the layer vertex to the immediately following level. -/
theorem mem_outgoing_iff (level : V → ℕ) (z : N.Word) (j : ℕ) (v : V)
    (hv : level v = j)
    (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1) (e : E) :
    e ∈ outgoing N level z j v ↔ z e ≠ 0 ∧
      ((N.src e = v ∧ level (N.dst e) = j + 1) ∨
        (N.dst e = v ∧ level (N.src e) = j + 1)) := by
  constructor
  · intro he
    obtain ⟨hc,hi⟩ := Finset.mem_filter.mp he
    obtain ⟨hc,hz⟩ := N.mem_crossSet.mp hc
    have hd := hlip e
    change ¬ (level (N.src e) ≤ j ↔ level (N.dst e) ≤ j) at hc
    refine ⟨hz,?_⟩
    rcases hi with hs | ht
    · left
      refine ⟨hs,?_⟩
      rw [hs,hv] at hc hd
      omega
    · right
      refine ⟨ht,?_⟩
      rw [ht,hv] at hc hd
      omega
  · rintro ⟨hz,hi⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply N.mem_crossSet.mpr
      refine ⟨?_,hz⟩
      change ¬ (level (N.src e) ≤ j ↔ level (N.dst e) ≤ j)
      rcases hi with ⟨hs,h⟩ | ⟨ht,h⟩
      · rw [hs,hv]
        omega
      · rw [ht,hv]
        omega
    · exact hi.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

private theorem cycle_not_concentrated (z : N.Word) (hz : N.IsCycleWord z)
    (S : V → Prop) (u b w : V) (hu : 0 < N.deg z u) (hb : 0 < N.deg z b)
    (hSu : S u) (hSb : ¬ S b) (hSw : ¬ S w) (hbw : b ≠ w)
    (htwo : 2 ≤ (N.crossSet S z).card) :
    ¬ (∀ e ∈ N.crossSet S z, N.src e = w ∨ N.dst e = w) := by
  classical
  intro hcon
  have hsub : N.crossSet S z ⊆ incident N z w := by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.mem_crossSet.mp he).2,hcon e he⟩
  have hdeg : (incident N z w).card ≤ 2 := by
    change N.deg z w ≤ 2
    rcases hz.2.1 w with h | h <;> omega
  have heq := Finset.eq_of_subset_of_card_le hsub (hdeg.trans htwo)
  have hcross (e : E) (he : z e ≠ 0) (hi : N.src e = w ∨ N.dst e = w) :
      N.crosses S e := by
    have hm : e ∈ N.crossSet S z := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,hi⟩
    exact (N.mem_crossSet.mp hm).1
  let T : V → Prop := fun v => S v ∨ v = w
  have hclosed (e : E) (he : z e ≠ 0) : T (N.src e) ↔ T (N.dst e) := by
    by_cases hs : S (N.src e) <;> by_cases ht : S (N.dst e)
    · exact iff_of_true (Or.inl hs) (Or.inl ht)
    · have hc : N.crosses S e := by unfold Network.crosses; tauto
      rcases hcon e ((N.mem_crossSet).mpr ⟨hc,he⟩) with hw | hw
      · exact (hSw (hw ▸ hs)).elim
      · exact iff_of_true (Or.inl hs) (Or.inr hw)
    · have hc : N.crosses S e := by unfold Network.crosses; tauto
      rcases hcon e ((N.mem_crossSet).mpr ⟨hc,he⟩) with hw | hw
      · exact iff_of_true (Or.inr hw) (Or.inl ht)
      · exact (hSw (hw ▸ ht)).elim
    · have hns : N.src e ≠ w := by
        intro h
        have hc := hcross e he (Or.inl h)
        exact hc (iff_of_false hs ht)
      have hnt : N.dst e ≠ w := by
        intro h
        have hc := hcross e he (Or.inr h)
        exact hc (iff_of_false hs ht)
      exact iff_of_false (not_or.mpr ⟨hs,hns⟩) (not_or.mpr ⟨ht,hnt⟩)
  have hempty : N.crossSet T z = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨hc,hz⟩ := N.mem_crossSet.mp he
    exact hc (hclosed e hz)
  rcases hz.within_inside_or_outside hempty with hin | hout
  · obtain ⟨e,he,hi⟩ := N.exists_edge_of_deg_pos hb
    have hh := hin e he
    have hbT : T b := hi.elim (fun h => h ▸ hh.1) (fun h => h ▸ hh.2)
    exact hbT.elim hSb hbw
  · obtain ⟨e,he,hi⟩ := N.exists_edge_of_deg_pos hu
    have hh := hout e he
    have huT : ¬ T u := hi.elim (fun h => h ▸ hh.1) (fun h => h ▸ hh.2)
    exact huT (Or.inl hSu)

private theorem cut_touches_both (z : N.Word) (hz : N.IsCycleWord z)
    (S : V → Prop) (R : Finset V) (hR : R.card = 2)
    (hRS : ∀ v ∈ R, ¬ S v)
    (htouch : ∀ e ∈ N.crossSet S z, ∃ v ∈ R, N.src e = v ∨ N.dst e = v)
    (u b : V) (hu : 0 < N.deg z u) (hb : 0 < N.deg z b)
    (hSu : S u) (hSb : ¬ S b) (hbR : b ∉ R)
    (htwo : 2 ≤ (N.crossSet S z).card) (v : V) (hv : v ∈ R) :
    0 < ((N.crossSet S z).filter (fun e => N.src e = v ∨ N.dst e = v)).card := by
  classical
  obtain ⟨a,c,hac,hpair⟩ := Finset.card_eq_two.mp hR
  have hother : ∃ w ∈ R, w ≠ v ∧ ∀ x ∈ R, x = v ∨ x = w := by
    rw [hpair] at hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · subst v
      refine ⟨c,by rw [hpair]; simp,Ne.symm hac,?_⟩
      intro x hx
      simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hx
    · subst v
      refine ⟨a,by rw [hpair]; simp,hac,?_⟩
      intro x hx
      simpa only [hpair,Finset.mem_insert,Finset.mem_singleton,or_comm] using hx
  obtain ⟨w,hw,_,hcover⟩ := hother
  by_contra hn
  apply cycle_not_concentrated N z hz S u b w hu hb hSu hSb (hRS w hw)
    (fun h => hbR (h ▸ hw)) htwo
  intro e he
  obtain ⟨x,hx,hi⟩ := htouch e he
  rcases hcover x hx with hxv | hxw
  · rw [hxv] at hi
    have hp : 0 < ((N.crossSet S z).filter (fun e => N.src e = v ∨ N.dst e = v)).card :=
      Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨he,hi⟩⟩
    exact (hn hp).elim
  · simpa only [hxw] using hi

omit [Fintype V] in
private theorem cross_compl (z : N.Word) (S : V → Prop) :
    N.crossSet (fun v => ¬ S v) z = N.crossSet S z := by
  ext e
  rw [N.mem_crossSet, N.mem_crossSet]
  change (¬ (¬ S (N.src e) ↔ ¬ S (N.dst e)) ∧ z e ≠ 0) ↔
    (¬ (S (N.src e) ↔ S (N.dst e)) ∧ z e ≠ 0)
  tauto

private theorem incoming_pos (level : V → ℕ) (z : N.Word) (hz : N.IsCycleWord z)
    (j : ℕ) (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (hcard : Nat.card {v : V // level v = j} = 2)
    (u b : V) (hu : 0 < N.deg z u) (hb : 0 < N.deg z b)
    (huj : level u < j) (hjb : j < level b) (v : V) (hv : level v = j) :
    0 < (incoming N level z j v).card := by
  let R := Finset.univ.filter fun w : V => level w = j
  have hR : R.card = 2 := by simpa [R,Nat.card_eq_fintype_card,Fintype.card_subtype] using hcard
  have htwo : 2 ≤ (N.crossSet (fun w => level w < j) z).card := by
    have hh := CycleLayerSpan.two_le_crossing_card N (fun w => (level w : ℤ)) z hz u b hu hb
      ((j : ℤ) - 1) (by change (level u : ℤ) ≤ (j : ℤ) - 1; omega)
      (by change (j : ℤ) - 1 < (level b : ℤ); omega)
    have he : (fun w => (level w : ℤ) ≤ (j : ℤ) - 1) = (fun w => level w < j) := by
      funext w
      apply propext
      omega
    simpa only [he] using hh
  apply cut_touches_both N z hz (fun w => level w < j) R hR
    (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega) ?_
    u b hu hb huj (by omega) (by simp [R]; omega) htwo v (by simp [R,hv])
  intro e he
  have hc := (N.mem_crossSet.mp he).1
  change ¬ (level (N.src e) < j ↔ level (N.dst e) < j) at hc
  have hd := hlip e
  have hh : level (N.src e) = j ∨ level (N.dst e) = j := by omega
  rcases hh with hh | hh
  · exact ⟨N.src e,by simp [R,hh],Or.inl rfl⟩
  · exact ⟨N.dst e,by simp [R,hh],Or.inr rfl⟩

private theorem outgoing_pos (level : V → ℕ) (z : N.Word) (hz : N.IsCycleWord z)
    (j : ℕ) (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (hcard : Nat.card {v : V // level v = j} = 2)
    (u b : V) (hu : 0 < N.deg z u) (hb : 0 < N.deg z b)
    (huj : level u < j) (hjb : j < level b) (v : V) (hv : level v = j) :
    0 < (outgoing N level z j v).card := by
  let R := Finset.univ.filter fun w : V => level w = j
  have hR : R.card = 2 := by simpa [R,Nat.card_eq_fintype_card,Fintype.card_subtype] using hcard
  have htwo : 2 ≤ (N.crossSet (fun w => ¬ level w ≤ j) z).card := by
    rw [cross_compl]
    have hh := CycleLayerSpan.two_le_crossing_card N (fun w => (level w : ℤ)) z hz u b hu hb
      (j : ℤ) (by change (level u : ℤ) ≤ (j : ℤ); omega)
      (by change (j : ℤ) < (level b : ℤ); omega)
    simpa only [Nat.cast_le] using hh
  have hp := cut_touches_both N z hz (fun w => ¬ level w ≤ j) R hR
    (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega) ?_
    b u hb hu (by omega) (by omega) (by simp [R]; omega) htwo v (by simp [R,hv])
  · simpa only [cross_compl,outgoing] using hp
  · intro e he
    have hc := (N.mem_crossSet.mp he).1
    change ¬ (¬ level (N.src e) ≤ j ↔ ¬ level (N.dst e) ≤ j) at hc
    have hd := hlip e
    have hh : level (N.src e) = j ∨ level (N.dst e) = j := by omega
    rcases hh with hh | hh
    · exact ⟨N.src e,by simp [R,hh],Or.inl rfl⟩
    · exact ⟨N.dst e,by simp [R,hh],Or.inr rfl⟩

omit [Fintype V] in
private theorem incoming_outgoing_disjoint (level : V → ℕ) (z : N.Word) (j : ℕ)
    (v : V) (hv : level v = j) : Disjoint (incoming N level z j v) (outgoing N level z j v) := by
  apply Finset.disjoint_left.mpr
  intro e hi ho
  obtain ⟨hi,hiv⟩ := Finset.mem_filter.mp hi
  obtain ⟨ho,_⟩ := Finset.mem_filter.mp ho
  have hl := (N.mem_crossSet.mp hi).1
  have hr := (N.mem_crossSet.mp ho).1
  change ¬ (level (N.src e) < j ↔ level (N.dst e) < j) at hl
  change ¬ (level (N.src e) ≤ j ↔ level (N.dst e) ≤ j) at hr
  rcases hiv with h | h <;> rw [h,hv] at hl hr <;> omega

omit [Fintype V] in
private theorem union_subset_incident (level : V → ℕ) (z : N.Word) (j : ℕ) (v : V) :
    incoming N level z j v ∪ outgoing N level z j v ⊆ incident N z v := by
  intro e he
  rcases Finset.mem_union.mp he with hi | ho
  · obtain ⟨hi,hv⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.mem_crossSet.mp hi).2,hv⟩
  · obtain ⟨ho,hv⟩ := Finset.mem_filter.mp ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.mem_crossSet.mp ho).2,hv⟩

/-- Both physical strands pass through each vertex of the two-vertex layer. -/
theorem one_incoming_one_outgoing (level : V → ℕ) (z : N.Word) (hz : N.IsCycleWord z)
    (j : ℕ) (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (hcard : Nat.card {v : V // level v = j} = 2)
    (hbelow : ∃ u, 0 < N.deg z u ∧ level u < j)
    (habove : ∃ b, 0 < N.deg z b ∧ j < level b) :
    ∀ v, level v = j →
      (incoming N level z j v).card = 1 ∧ (outgoing N level z j v).card = 1 := by
  obtain ⟨u,hu,huj⟩ := hbelow
  obtain ⟨b,hb,hjb⟩ := habove
  intro v hv
  have hi := incoming_pos N level z hz j hlip hcard u b hu hb huj hjb v hv
  have ho := outgoing_pos N level z hz j hlip hcard u b hu hb huj hjb v hv
  have hc := Finset.card_le_card (union_subset_incident N level z j v)
  rw [Finset.card_union_of_disjoint (incoming_outgoing_disjoint N level z j v hv)] at hc
  change (incoming N level z j v).card + (outgoing N level z j v).card ≤ N.deg z v at hc
  rcases hz.2.1 v with hd | hd <;> omega

/-- No selected physical label lies inside the two-vertex layer. -/
theorem no_internal_rung (level : V → ℕ) (z : N.Word) (hz : N.IsCycleWord z)
    (j : ℕ) (hlip : ∀ e, level (N.src e) ≤ level (N.dst e) + 1 ∧
      level (N.dst e) ≤ level (N.src e) + 1)
    (hcard : Nat.card {v : V // level v = j} = 2)
    (hbelow : ∃ u, 0 < N.deg z u ∧ level u < j)
    (habove : ∃ b, 0 < N.deg z b ∧ j < level b) :
    ∀ e, level (N.src e) = j → level (N.dst e) = j → z e = 0 := by
  intro e hs ht
  by_contra he
  have hcounts := one_incoming_one_outgoing N level z hz j hlip hcard hbelow habove (N.src e) hs
  have hsub := union_subset_incident N level z j (N.src e)
  have hd : (incident N z (N.src e)).card ≤ 2 := by
    change N.deg z (N.src e) ≤ 2
    rcases hz.2.1 (N.src e) with h | h <;> omega
  have hc : (incoming N level z j (N.src e) ∪ outgoing N level z j (N.src e)).card = 2 := by
    rw [Finset.card_union_of_disjoint (incoming_outgoing_disjoint N level z j (N.src e) hs)]
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hm : e ∈ incoming N level z j (N.src e) ∪ outgoing N level z j (N.src e) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,Or.inl rfl⟩
  rcases Finset.mem_union.mp hm with hi | ho
  · have hcross := (N.mem_crossSet.mp (Finset.mem_filter.mp hi).1).1
    simp [Network.crosses,hs,ht] at hcross
  · have hcross := (N.mem_crossSet.mp (Finset.mem_filter.mp ho).1).1
    simp [Network.crosses,hs,ht] at hcross

omit [Fintype V] in
private theorem incoming_card_eq_degree (s : V) (z : N.Word) (j : ℕ) (v : V)
    (hv : N.graph.dist s v = j) (hj : 0 < j)
    (hlip : ∀ e, N.graph.dist s (N.src e) ≤ N.graph.dist s (N.dst e) + 1 ∧
      N.graph.dist s (N.dst e) ≤ N.graph.dist s (N.src e) + 1) :
    N.deg (restrict z (N.IsLayerEdge s (j - 1))) v =
      (incoming N (N.graph.dist s) z j v).card := by
  unfold Network.deg
  congr 1
  ext e
  rw [mem_incoming_iff N (N.graph.dist s) z j v hv hlip e]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, restrict_ne_zero_iff,
    Network.IsLayerEdge]
  constructor
  · rintro ⟨⟨he,hz⟩,hi⟩
    refine ⟨hz,?_⟩
    rcases hi with hi | hi
    · left
      refine ⟨hi,?_⟩
      have hs : N.graph.dist s (N.src e) = j := hi ▸ hv
      rcases he with he | he <;> omega
    · right
      refine ⟨hi,?_⟩
      have ht : N.graph.dist s (N.dst e) = j := hi ▸ hv
      rcases he with he | he <;> omega
  · rintro ⟨hz,⟨hi,he⟩ | ⟨hi,he⟩⟩
    · refine ⟨⟨Or.inr ?_,hz⟩,Or.inl hi⟩
      have hs : N.graph.dist s (N.src e) = j := hi ▸ hv
      constructor <;> omega
    · refine ⟨⟨Or.inl ?_,hz⟩,Or.inr hi⟩
      have ht : N.graph.dist s (N.dst e) = j := hi ▸ hv
      constructor <;> omega

omit [Fintype V] in
private theorem outgoing_card_eq_degree (s : V) (z : N.Word) (j : ℕ) (v : V)
    (hv : N.graph.dist s v = j)
    (hlip : ∀ e, N.graph.dist s (N.src e) ≤ N.graph.dist s (N.dst e) + 1 ∧
      N.graph.dist s (N.dst e) ≤ N.graph.dist s (N.src e) + 1) :
    N.deg (restrict z (N.IsLayerEdge s j)) v =
      (outgoing N (N.graph.dist s) z j v).card := by
  unfold Network.deg
  congr 1
  ext e
  rw [mem_outgoing_iff N (N.graph.dist s) z j v hv hlip e]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, restrict_ne_zero_iff,
    Network.IsLayerEdge]
  constructor
  · rintro ⟨⟨he,hz⟩,hi⟩
    refine ⟨hz,?_⟩
    rcases hi with hi | hi
    · left
      refine ⟨hi,?_⟩
      have hs : N.graph.dist s (N.src e) = j := hi ▸ hv
      rcases he with he | he <;> omega
    · right
      refine ⟨hi,?_⟩
      have ht : N.graph.dist s (N.dst e) = j := hi ▸ hv
      rcases he with he | he <;> omega
  · rintro ⟨hz,⟨hi,he⟩ | ⟨hi,he⟩⟩
    · exact ⟨⟨Or.inl ⟨hi ▸ hv,he⟩,hz⟩,Or.inl hi⟩
    · exact ⟨⟨Or.inr ⟨he,hi ▸ hv⟩,hz⟩,Or.inr hi⟩

/-- The exact physical-network statement used by the pole cycle encoding. -/
theorem twoStrandsStatement : ExactMaximum.TwoStrandsStatement := by
  intro V E _ _ N s t hN z j hz hj hbelow habove
  have hlip (e : E) : N.graph.dist s (N.src e) ≤ N.graph.dist s (N.dst e) + 1 ∧
      N.graph.dist s (N.dst e) ≤ N.graph.dist s (N.src e) + 1 :=
    DistanceFourLayers.dist_adj N.graph s hN.connected ⟨e,Or.inl ⟨rfl,rfl⟩⟩
  refine ⟨no_internal_rung N (N.graph.dist s) z hz j hlip hj.2.2 hbelow habove,?_⟩
  intro v hv
  rw [incoming_card_eq_degree N s z j v hv hj.1 hlip,
    outgoing_card_eq_degree N s z j v hv hlip]
  exact one_incoming_one_outgoing N (N.graph.dist s) z hz j hlip hj.2.2 hbelow habove v hv

end Erdos1016.ExactMaximumSupport.CycleTwoStrands

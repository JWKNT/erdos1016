import Erdos1016.Cycles.Filtering.ReturnRunCounts

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.WeightedWalkPrefix

open scoped BigOperators
open Erdos1016.Nonbacktracking Erdos1016.Proof.WalkPrefix

variable (G : PhysicalGraph)

/-- Product of vertex weights at the internal vertices of a dart run.
The first tail and final head are excluded. -/
def runWeight (w : G.Vertex → ℝ) : ∀ {k : ℕ} {d e : Dart G}, Run G k d e → ℝ
  | 0, _, _, _ => 1
  | k + 1, d, _, r => w (head G d) * runWeight w r.2.2

@[simp] theorem runWeight_cast (w : G.Vertex → ℝ) {m n : ℕ} (h : m = n)
    {d e : Dart G} (r : Run G m d e) :
    runWeight G w (h ▸ r) = runWeight G w r := by
  cases h
  rfl

private theorem run_transport_eq {m n : ℕ} (h : n = m) {d e : Dart G}
    (r : Run G m d e) :
    Eq.mpr (congrArg (fun t => Run G t d e) h) r = h.symm ▸ r := by
  cases h
  rfl

theorem runWeight_nonneg (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∀ {k : ℕ} {d e : Dart G} (r : Run G k d e), 0 ≤ runWeight G w r := by
  intro k
  induction k with
  | zero => intros; exact zero_le_one
  | succ k ih =>
    intro d e r
    exact mul_nonneg (hw _) (ih r.2.2)

/-- The recursive weight is the product along the actual internal dart
vertices, making it independent of the run representation. -/
theorem runWeight_eq_prod (w : G.Vertex → ℝ) :
    ∀ {k : ℕ} {d e : Dart G} (r : Run G k d e),
      runWeight G w r =
        (((runDarts G k r).dropLast.map (fun d => w (head G d))).prod) := by
  intro k
  induction k with
  | zero => intros; simp [runWeight, runDarts]
  | succ k ih =>
    intro d e r
    have hn : runDarts G k r.2.2 ≠ [] := by cases k <;> simp [runDarts]
    simp [runDarts, runWeight, List.dropLast_cons_of_ne_nil hn, ih]

theorem walkDarts_map_head {u v : G.Vertex} (p : G.toSimpleGraph.Walk u v) :
    (walkDarts G p).map (head G) = p.support.tail := by
  induction p with
  | nil => simp [walkDarts]
  | @cons u v z huv p ih =>
    simp only [walkDarts, List.map_cons, head_dartOfAdj, ih,
      SimpleGraph.Walk.support_cons, List.tail_cons]
    cases p <;> rfl

/-- Dropping a factor in `[0,1]` increases a finite nonnegative product. -/
theorem prod_map_le_dropLast (w : G.Vertex → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hwone : ∀ v, w v ≤ 1) (l : List G.Vertex) :
    (l.map w).prod ≤ (l.dropLast.map w).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    cases l with
    | nil => simpa using hwone v
    | cons u l =>
      simp only [List.dropLast_cons_of_ne_nil (by simp : u :: l ≠ []),
        List.map_cons, List.prod_cons] at *
      exact mul_le_mul_of_nonneg_left ih (hw v)

/-- Every unmarked internal vertex contributes a factor at most one half;
marked vertices cost at most one factor two each. -/
theorem prod_map_le_marked_budget (w : G.Vertex → ℝ) (marked : G.Vertex → Prop)
    [DecidablePred marked] (hw : ∀ v, 0 ≤ w v)
    (hmarked : ∀ v, marked v → w v ≤ 1)
    (hordinary : ∀ v, ¬ marked v → w v ≤ 1 / 2)
    (l : List G.Vertex) :
    (l.map w).prod ≤ (2 : ℝ) ^ (l.countP (fun v => decide (marked v))) /
      (2 : ℝ) ^ l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    have htail : 0 ≤ (l.map w).prod := List.prod_nonneg (by
      intro a ha
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
      exact hw v)
    by_cases hv : marked v
    · have hm := mul_le_mul_of_nonneg_right (hmarked v hv) htail
      simp only [one_mul] at hm
      have heq : (2 : ℝ) ^ ((v :: l).countP (fun v => decide (marked v))) /
          (2 : ℝ) ^ (v :: l).length =
          (2 : ℝ) ^ (l.countP (fun v => decide (marked v))) / (2 : ℝ) ^ l.length := by
        simp [List.countP_cons, hv, pow_succ]
        field_simp
        ring
      rw [heq]
      exact hm.trans ih
    · have hm := mul_le_mul (hordinary v hv) ih htail (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have heq : (2 : ℝ) ^ ((v :: l).countP (fun v => decide (marked v))) /
          (2 : ℝ) ^ (v :: l).length =
          (1 / 2 : ℝ) * ((2 : ℝ) ^ (l.countP (fun v => decide (marked v))) / (2 : ℝ) ^ l.length) := by
        simp only [List.countP_cons, hv, decide_false, Bool.false_eq_true, if_false,
          Nat.add_zero, List.length_cons, pow_succ]
        ring
      rw [heq]
      exact hm

theorem internalVertices_length {k : ℕ} {d e : Dart G} (r : Run G k d e) :
    ((runDarts G k r).dropLast.map (head G)).length = k := by
  have hlen : (runDarts G k r).length = k + 1 := by
    induction k generalizing d e with
    | zero => simp [runDarts]
    | succ k ih => simp [runDarts, ih]
  simp [hlen]

/-- A bound on visits to degree-two vertices turns directly into the weighted
suffix estimate used by the cycle load theorem. -/
theorem runWeight_le_marked_budget
    (w : G.Vertex → ℝ) (marked : G.Vertex → Prop) [DecidablePred marked]
    (hw : ∀ v, 0 ≤ w v) (hmarked : ∀ v, marked v → w v ≤ 1)
    (hordinary : ∀ v, ¬ marked v → w v ≤ 1 / 2)
    {k : ℕ} {d e : Dart G} (r : Run G k d e) (b : ℕ)
    (hb : (((runDarts G k r).dropLast.map (head G)).countP
      (fun v => decide (marked v))) ≤ b) :
    runWeight G w r ≤ (2 : ℝ) ^ b / (2 : ℝ) ^ k := by
  have h := prod_map_le_marked_budget G w marked hw hmarked hordinary
    ((runDarts G k r).dropLast.map (head G))
  simp only [List.map_map, Function.comp_def] at h
  rw [← runWeight_eq_prod, internalVertices_length] at h
  exact h.trans (div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb) (by positivity))

/-- Total weight of all continuations after a specified first dart. -/
def continuationMass (w : G.Vertex → ℝ) (k : ℕ) (d : Dart G) : ℝ :=
  ∑ e, ∑ r : Run G k d e, runWeight G w r

theorem continuationMass_zero (w : G.Vertex → ℝ) (d : Dart G) :
    continuationMass G w 0 d = 1 := by
  classical
  unfold continuationMass
  have h (e : Dart G) : (∑ r : Run G 0 d e, runWeight G w r) =
      if d = e then 1 else 0 := by
    change (∑ _r : Run G 0 d e, (1 : ℝ)) = _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have heq : Fintype.card (Run G 0 d e) = Fintype.card (Flag (d = e)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [heq, card_flag]
    split_ifs <;> norm_num
  simp [h]

theorem continuationMass_succ (w : G.Vertex → ℝ) (k : ℕ) (d : Dart G) :
    continuationMass G w (k + 1) d =
      w (head G d) * ∑ e ∈ successors G d, continuationMass G w k e := by
  classical
  have hsum (e : Dart G) : (∑ r : Run G (k + 1) d e, runWeight G w r) =
      ∑ u : Dart G, if Next G d u then
        w (head G d) * (∑ r : Run G k u e, runWeight G w r) else 0 := by
    calc
      _ = ∑ r : Σ u : Dart G, Flag (Next G d u) × Run G k u e,
          w (head G d) * runWeight G w r.2.2 :=
        @Fintype.sum_equiv (Run G (k + 1) d e)
          (Σ u : Dart G, Flag (Next G d u) × Run G k u e) ℝ
          (runFintype G (k + 1) d e) inferInstance inferInstance
          (Equiv.refl _) _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro u _
        rw [Fintype.sum_prod_type]
        simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [card_flag]
        split_ifs <;> simp_all
  unfold continuationMass
  simp_rw [hsum]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp only [successors, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : Next G d e
  · simp [he, Finset.mul_sum]
  · simp [he]

/-- Substochastic continuation: each incoming dart has at most one unit of
outgoing weight. This covers restriction to the ordinary vertices of a core. -/
theorem continuationMass_le_one (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (k : ℕ) (d : Dart G) : continuationMass G w k d ≤ 1 := by
  induction k generalizing d with
  | zero => rw [continuationMass_zero]
  | succ k ih =>
    rw [continuationMass_succ]
    calc
      _ ≤ w (head G d) * ∑ _e ∈ successors G d, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => ih e) (hw _)
      _ ≤ 1 := by simpa using hrow d

/-- Total internal weight of all walks starting at a fixed vertex is at most
its degree, with no length-dependent factor. -/
theorem startingRuns_weight_le_degree (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (k : ℕ) (v : G.Vertex) :
    (∑ p : StartingRuns G k v, runWeight G w p.2.2) ≤ G.degree v := by
  classical
  calc
    _ = ∑ d : {d : Dart G // tail G d = v}, continuationMass G w k d.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro d _
      exact Fintype.sum_sigma _
    _ ≤ ∑ _d : {d : Dart G // tail G d = v}, (1 : ℝ) :=
      Finset.sum_le_sum fun d _ => continuationMass_le_one G w hw hrow k d.1
    _ = G.degree v := by simp [card_starting_darts]



/-- Splitting a run factors its internal weight exactly. The boundary dart
is shared, but each internal vertex weight is counted only once. -/
theorem runWeight_splitRun (w : G.Vertex → ℝ) :
    ∀ {j k : ℕ} (hjk : j ≤ k) {d e : Dart G} (r : Run G k d e),
      runWeight G w r =
        runWeight G w (splitRun G hjk r).2.1 *
          runWeight G w (splitRun G hjk r).2.2 := by
  intro j
  induction j with
  | zero =>
    intro k hk d e r
    rw [splitRun.eq_1 G k d e r hk]
    simp [runWeight]
  | succ j ih =>
    intro k hjk d e r
    cases k with
    | zero => omega
    | succ k =>
      rcases r with ⟨u, hu, rest⟩
      rw [splitRun.eq_3 G d e j k hjk ⟨u, hu, rest⟩]
      let pieces := splitRun G (Nat.le_of_succ_le_succ hjk) rest
      have hsub : k + 1 - (j + 1) = k - j := Nat.succ_sub_succ_eq_sub k j
      have htransport := run_transport_eq G hsub pieces.2.2
      simp only [runWeight]
      rw [htransport, runWeight_cast]
      have h := ih (Nat.le_of_succ_le_succ hjk) rest
      change runWeight G w rest = runWeight G w pieces.2.1 * runWeight G w pieces.2.2 at h
      rw [h]
      ring

/-- Girth and a small suffix weight bound a whole finite family of weighted
fixed-endpoint runs by the degree at its starting vertex. Only the encoded
family needs the suffix bound; other walks are summed using substochasticity. -/
theorem encoded_endpoint_weight_sum_le
    {ι : Type*} [Fintype ι]
    (w : G.Vertex → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hrow : ∀ d : Dart G, w (head G d) * ((successors G d).card : ℝ) ≤ 1)
    (D a s : ℕ) (u v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsa : s < a) (hshort : 2 * s ≤ D)
    (encode : ι → EndpointRuns G (a - 1) u v) (hinj : Function.Injective encode)
    (weight : ι → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hweight : ∀ i, weight i ≤ runWeight G w (encode i).1.2.2)
    (hsuffix : ∀ i,
      runWeight G w (splitRun G (show a - s - 1 ≤ a - 1 by omega)
        (encode i).1.2.2).2.2 ≤ ε) :
    (∑ i, weight i) ≤ ε * G.degree u := by
  classical
  let takePrefix := fixedEndpointPrefix G (show a - s - 1 ≤ a - 1 by omega) u v
  let f := takePrefix ∘ encode
  have hfinj : Function.Injective f :=
    (ExternalReturnFilter.fixedEndpointPrefix_injective_of_girth G D a s u v
      hg hs hsa hshort).comp hinj
  have hpoint (i : ι) : weight i ≤ ε * runWeight G w (f i).2.2 := by
    have hsplit := runWeight_splitRun G w (show a - s - 1 ≤ a - 1 by omega)
      (encode i).1.2.2
    have hm := mul_le_mul_of_nonneg_left (hsuffix i)
      (runWeight_nonneg G w hw (splitRun G (show a - s - 1 ≤ a - 1 by omega)
        (encode i).1.2.2).2.1)
    calc
      weight i ≤ runWeight G w (encode i).1.2.2 := hweight i
      _ ≤ runWeight G w (f i).2.2 * ε := by
        rw [hsplit]
        exact hm
      _ = ε * runWeight G w (f i).2.2 := mul_comm _ _
  have hsum : (∑ i, runWeight G w (f i).2.2) ≤
      ∑ p : StartingRuns G (a - s - 1) u, runWeight G w p.2.2 := by
    calc
      _ = ∑ p ∈ Finset.univ.image f, runWeight G w p.2.2 := by
        rw [Finset.sum_image (fun i _ j _ hij => hfinj hij)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => runWeight_nonneg G w hw p.2.2)
  calc
    _ ≤ ∑ i, ε * runWeight G w (f i).2.2 := Finset.sum_le_sum fun i _ => hpoint i
    _ = ε * ∑ i, runWeight G w (f i).2.2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ε * G.degree u := mul_le_mul_of_nonneg_left
      (hsum.trans (startingRuns_weight_le_degree G w hw hrow _ u)) hε

end Erdos1016.Proof.WeightedWalkPrefix

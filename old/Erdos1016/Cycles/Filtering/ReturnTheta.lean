import Erdos1016.Nonbacktracking.Walks.CycleWords
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

set_option autoImplicit false

/-!
# The three paths associated to an external return

This file extracts the theta formed by a simple cycle and a simple external
return.  It records the three internally disjoint branches, the three simple
cycles obtained by taking pairs of branches, and their exact length sums.
The finite counting and charging multiplicity are deliberately separate.
-/

namespace Erdos1016.Proof.ExternalReturnTheta

open SimpleGraph

variable {V : Type*} (H : SimpleGraph V) [DecidableEq V]

/-- Three simple branches with common distinct endpoints and pairwise
intersection only at those endpoints. -/
structure ThetaPaths (u v : V) where
  left : H.Walk u v
  right : H.Walk u v
  external : H.Walk u v
  left_path : left.IsPath
  right_path : right.IsPath
  external_path : external.IsPath
  left_right_vertices : ∀ x, x ∈ left.support → x ∈ right.support → x = u ∨ x = v
  left_external_vertices : ∀ x, x ∈ left.support → x ∈ external.support → x = u ∨ x = v
  right_external_vertices : ∀ x, x ∈ right.support → x ∈ external.support → x = u ∨ x = v
  left_right_edges : ∀ e, e ∈ left.edges → e ∉ right.edges
  left_external_edges : ∀ e, e ∈ left.edges → e ∉ external.edges
  right_external_edges : ∀ e, e ∈ right.edges → e ∉ external.edges

private def branchPathTriple {u v : V} (t : ThetaPaths H u v) :
    H.Path u v × (H.Path u v × H.Path u v) :=
  (⟨t.left, t.left_path⟩,
    (⟨t.right, t.right_path⟩, ⟨t.external, t.external_path⟩))

omit [DecidableEq V] in
private theorem branchPathTriple_injective {u v : V} :
    Function.Injective (branchPathTriple (H := H) (u := u) (v := v)) := by
  intro a b h
  cases a
  cases b
  simp only [branchPathTriple, Prod.mk.injEq, Subtype.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- There are finitely many such theta branch triples in a finite graph:
each branch is a simple path, hence an element of Mathlib's finite path type. -/
noncomputable instance thetaPathsFintype [Fintype V] [DecidableRel H.Adj]
    (u v : V) : Fintype (ThetaPaths H u v) :=
  Fintype.ofInjective (branchPathTriple (H := H) (u := u) (v := v))
    (branchPathTriple_injective (H := H) (u := u) (v := v))

omit [DecidableEq V] in
/-- Two simple paths whose only common vertices are their distinct endpoints
form a simple cycle when their edge lists are disjoint. -/
private theorem cycle_of_disjoint_paths {u v : V}
    (p : H.Walk u v) (q : H.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath)
    (hvertices : List.Disjoint p.support.tail q.support.tail)
    (hedges : List.Disjoint p.edges q.edges)
    (huv : u ≠ v) : (p.append q).IsCycle := by
  have htrail : (p.append q).IsTrail := by
    rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_append,
      List.nodup_append]
    exact ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, hedges⟩
  have hnonempty : (p.append q) ≠ SimpleGraph.Walk.nil := by
    intro hn
    have hz : (p.append q).length = 0 := by simp [hn]
    rw [SimpleGraph.Walk.length_append, Nat.add_eq_zero_iff] at hz
    exact huv (SimpleGraph.Walk.eq_of_length_eq_zero hz.1)
  have hsupport : (p.append q).support.tail.Nodup := by
    rw [SimpleGraph.Walk.tail_support_append]
    exact List.Nodup.append hp.support_nodup.tail hq.support_nodup.tail hvertices
  exact ⟨⟨htrail, hnonempty⟩, hsupport⟩

omit [DecidableEq V] in
private theorem tail_disjoint_of_endpoint_overlap {u v : V}
    (p : H.Walk u v) (q : H.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath)
    (hvertices : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
    List.Disjoint p.support.tail q.support.tail := by
  have hu_tail : u ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [SimpleGraph.Walk.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1
  have hv_tail : v ∉ q.support.tail := by
    have hn := hq.support_nodup
    rw [SimpleGraph.Walk.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1
  rw [List.disjoint_left]
  intro x hx hqx
  rcases hvertices x (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hqx) with hxu | hxv
  · subst x
    exact hu_tail hx
  · subst x
    exact hv_tail hqx

omit [DecidableEq V] in
/-- A pair of same-orientation branches yields a simple cycle. -/
private theorem branch_pair_cycle {u v : V}
    (p q : H.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hvertices : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v)
    (hedges : ∀ e, e ∈ p.edges → e ∉ q.edges) (huv : u ≠ v) :
    (p.append q.reverse).IsCycle := by
  have hvertices' : ∀ x, x ∈ p.support → x ∈ q.reverse.support → x = u ∨ x = v := by
    intro x hx hxr
    apply hvertices x hx
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hxr
  have hedges' : List.Disjoint p.edges q.reverse.edges := by
    rw [List.disjoint_left]
    intro e he her
    have her' : e ∈ q.edges := by
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using her
    exact hedges e he her'
  exact cycle_of_disjoint_paths H p q.reverse hp hq.reverse
    (tail_disjoint_of_endpoint_overlap H p q.reverse hp hq.reverse hvertices')
    hedges' huv

def leftRightCycle {u v : V} (t : ThetaPaths H u v) : H.Walk u u :=
  t.left.append t.right.reverse

def leftExternalCycle {u v : V} (t : ThetaPaths H u v) : H.Walk u u :=
  t.left.append t.external.reverse

def externalRightCycle {u v : V} (t : ThetaPaths H u v) : H.Walk u u :=
  t.external.append t.right.reverse

omit [DecidableEq V] in
theorem leftRightCycle_isCycle {u v : V} (t : ThetaPaths H u v) (huv : u ≠ v) :
    (leftRightCycle H t).IsCycle := by
  exact branch_pair_cycle H t.left t.right t.left_path t.right_path
    t.left_right_vertices t.left_right_edges huv

omit [DecidableEq V] in
theorem leftExternalCycle_isCycle {u v : V} (t : ThetaPaths H u v) (huv : u ≠ v) :
    (leftExternalCycle H t).IsCycle := by
  exact branch_pair_cycle H t.left t.external t.left_path t.external_path
    t.left_external_vertices t.left_external_edges huv

omit [DecidableEq V] in
theorem externalRightCycle_isCycle {u v : V} (t : ThetaPaths H u v) (huv : u ≠ v) :
    (externalRightCycle H t).IsCycle := by
  exact branch_pair_cycle H t.external t.right t.external_path t.right_path
    (fun x hx hy => t.right_external_vertices x hy hx)
    (fun e he hne => t.right_external_edges e hne he) huv

omit [DecidableEq V] in
theorem leftRightCycle_length {u v : V} (t : ThetaPaths H u v) :
    (leftRightCycle H t).length = t.left.length + t.right.length := by
  simp [leftRightCycle, SimpleGraph.Walk.length_append]

omit [DecidableEq V] in
theorem leftExternalCycle_length {u v : V} (t : ThetaPaths H u v) :
    (leftExternalCycle H t).length = t.left.length + t.external.length := by
  simp [leftExternalCycle, SimpleGraph.Walk.length_append]

omit [DecidableEq V] in
theorem externalRightCycle_length {u v : V} (t : ThetaPaths H u v) :
    (externalRightCycle H t).length = t.external.length + t.right.length := by
  simp [externalRightCycle, SimpleGraph.Walk.length_append]

/-- The three possible choices of a two-branch base cycle. -/
inductive ThetaPair where
  | leftRight
  | leftExternal
  | externalRight
  deriving DecidableEq, Fintype

/-- Length of a pair-cycle, expressed as the sum of its branch lengths. -/
def pairLength {u v : V} (t : ThetaPaths H u v) : ThetaPair → ℕ
  | .leftRight => t.left.length + t.right.length
  | .leftExternal => t.left.length + t.external.length
  | .externalRight => t.external.length + t.right.length

def firstPairBranchLength {u v : V} (t : ThetaPaths H u v) : ThetaPair → ℕ
  | .leftRight => t.left.length
  | .leftExternal => t.left.length
  | .externalRight => t.external.length

def secondPairBranchLength {u v : V} (t : ThetaPaths H u v) : ThetaPair → ℕ
  | .leftRight => t.right.length
  | .leftExternal => t.external.length
  | .externalRight => t.right.length

/-- The branch omitted when a pair is selected as the base cycle. -/
def omittedBranchLength {u v : V} (t : ThetaPaths H u v) : ThetaPair → ℕ
  | .leftRight => t.external.length
  | .leftExternal => t.right.length
  | .externalRight => t.left.length

omit [DecidableEq V] in
theorem pairLength_eq_branch_sum {u v : V} (t : ThetaPaths H u v) (p : ThetaPair) :
    pairLength H t p = firstPairBranchLength H t p + secondPairBranchLength H t p := by
  cases p <;> rfl

/-- Select a pair with minimum total length among the three pair-cycles. -/
def minimumPair {u v : V} (t : ThetaPaths H u v) : ThetaPair :=
  if pairLength H t .leftRight ≤ pairLength H t .leftExternal then
    if pairLength H t .leftRight ≤ pairLength H t .externalRight then
      .leftRight
    else if pairLength H t .leftExternal ≤ pairLength H t .externalRight then
      .leftExternal
    else
      .externalRight
  else if pairLength H t .leftExternal ≤ pairLength H t .externalRight then
    .leftExternal
  else
    .externalRight

omit [DecidableEq V] in
theorem minimumPair_isMinimum {u v : V} (t : ThetaPaths H u v) (p : ThetaPair) :
    pairLength H t (minimumPair H t) ≤ pairLength H t p := by
  unfold minimumPair
  split_ifs <;> cases p <;> simp [pairLength] at * <;> omega

omit [DecidableEq V] in
theorem minimumPair_branches_le_omitted {u v : V} (t : ThetaPaths H u v) :
    firstPairBranchLength H t (minimumPair H t) ≤ omittedBranchLength H t (minimumPair H t) ∧
    secondPairBranchLength H t (minimumPair H t) ≤ omittedBranchLength H t (minimumPair H t) := by
  unfold minimumPair
  split_ifs <;> simp [pairLength, firstPairBranchLength, secondPairBranchLength,
    omittedBranchLength] at * <;> omega

omit [DecidableEq V] in
/-- If all three pair-cycles exceed D, the omitted branch of a shortest
pair-cycle has length greater than s whenever 2s ≤ D. -/
theorem minimumPair_omitted_gt_of_girth {u v : V} (t : ThetaPaths H u v)
    (D s : ℕ)
    (hLR : D < pairLength H t .leftRight)
    (hLE : D < pairLength H t .leftExternal)
    (hER : D < pairLength H t .externalRight)
    (hs : 2 * s ≤ D) :
    s < omittedBranchLength H t (minimumPair H t) := by
  have hpair : D < pairLength H t (minimumPair H t) := by
    cases hp : minimumPair H t with
    | leftRight => simpa [hp] using hLR
    | leftExternal => simpa [hp] using hLE
    | externalRight => simpa [hp] using hER
  have hbranches := minimumPair_branches_le_omitted H t
  by_contra hn
  have hsmall : omittedBranchLength H t (minimumPair H t) ≤ s := Nat.le_of_not_gt hn
  have hsum : pairLength H t (minimumPair H t) ≤ 2 * s := by
    rw [pairLength_eq_branch_sum]
    calc
      firstPairBranchLength H t (minimumPair H t) +
          secondPairBranchLength H t (minimumPair H t) ≤
        omittedBranchLength H t (minimumPair H t) + omittedBranchLength H t (minimumPair H t) :=
          Nat.add_le_add hbranches.1 hbranches.2
      _ ≤ 2 * s := by omega
  omega

omit [DecidableEq V] in
/-- Under the paper's hypotheses, all three branches have length at most L,
and the shortest pair-cycle also has length at most L. The external return is
the distinguished branch; the source cycle is the left-right pair. -/
theorem minimumPair_girth_length_bounds {u v : V} (t : ThetaPaths H u v)
    (D s L q : ℕ)
    (hsource : pairLength H t .leftRight ≤ L)
    (hreturn : t.external.length ≤ q) (hqL : q ≤ L)
    (hLR : D < pairLength H t .leftRight)
    (hLE : D < pairLength H t .leftExternal)
    (hER : D < pairLength H t .externalRight)
    (hs : 2 * s ≤ D) :
    pairLength H t (minimumPair H t) ≤ L ∧
    s < omittedBranchLength H t (minimumPair H t) ∧
    t.left.length ≤ L ∧ t.right.length ≤ L ∧ t.external.length ≤ L := by
  refine ⟨?_, minimumPair_omitted_gt_of_girth H t D s hLR hLE hER hs, ?_⟩
  · exact (minimumPair_isMinimum H t .leftRight).trans hsource
  · have hsum := hsource
    simp [pairLength] at hsum
    omega

private theorem rotate_length {x u : V} (c : H.Walk x x) (hu : u ∈ c.support) :
    (c.rotate hu).length = c.length := by
  have hs := SimpleGraph.Walk.take_spec c hu
  have hlen := congrArg SimpleGraph.Walk.length hs
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.rotate] at hlen ⊢
  omega

/-- A simple closed cycle plus a simple external return produce three
pairwise internally disjoint simple branches. The cycle walk is the union of
the two cycle arcs, and the other two branch pairs are simple cycles. -/
theorem externalReturn_theta
    {x u v : V} (c : H.Walk x x) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v)
    (r : H.Walk u v) (hr : r.IsPath)
    (hreturnInterior : ∀ z, z ∈ r.support → z ≠ u → z ≠ v → z ∉ c.support)
    (hreturnEdges : ∀ e, e ∈ r.edges → e ∉ c.edges) :
    ∃ t : ThetaPaths H u v,
      leftRightCycle H t = c.rotate hu ∧
      (leftRightCycle H t).IsCycle ∧
      (leftExternalCycle H t).IsCycle ∧
      (externalRightCycle H t).IsCycle ∧
      (leftRightCycle H t).length = t.left.length + t.right.length ∧
      (leftExternalCycle H t).length = t.left.length + t.external.length ∧
      (externalRightCycle H t).length = t.external.length + t.right.length ∧
      t.external = r := by
  let rot := c.rotate hu
  have hrot : rot.IsCycle := by
    exact hc.rotate hu
  have hxTail : x ∈ c.support.tail := by
    cases c with
    | nil => exact (hc.ne_nil rfl).elim
    | cons hadj p => exact p.end_mem_support
  have hvTail : v ∈ c.support.tail := by
    rcases (SimpleGraph.Walk.mem_support_iff c).1 hv with hroot | htail
    · rw [hroot]
      exact hxTail
    · exact htail
  have hvRotTail : v ∈ rot.support.tail := by
    exact (SimpleGraph.Walk.support_rotate c hu).mem_iff.mpr hvTail
  have hvRot : v ∈ rot.support :=
    (SimpleGraph.Walk.mem_support_iff rot).2 (Or.inr hvRotTail)
  let arc₁ := rot.takeUntil v hvRot
  let arc₂tail := rot.dropUntil v hvRot
  let arc₂ := arc₂tail.reverse
  have hsplit : arc₁.append arc₂tail = rot :=
    SimpleGraph.Walk.take_spec rot hvRot
  have hleftPath : arc₁.IsPath := hrot.isPath_takeUntil hvRot
  have hleftNonNil : ¬ arc₁.Nil := by
    intro hn
    have heq : u = v := (SimpleGraph.Walk.nil_takeUntil rot hvRot).1 hn
    exact huv heq
  have hsplitCycle : (arc₁.append arc₂tail).IsCycle := by
    rw [hsplit]
    exact hrot
  have hrightTailPath : arc₂tail.IsPath :=
    hsplitCycle.isPath_of_append_right hleftNonNil
  have hrightPath : arc₂.IsPath := hrightTailPath.reverse
  have htailDisjoint : List.Disjoint arc₁.support.tail arc₂tail.support.tail := by
    have hrotTail : (arc₁.support.tail ++ arc₂tail.support.tail).Nodup := by
      rw [← SimpleGraph.Walk.tail_support_append, hsplit]
      exact hrot.support_nodup
    exact List.disjoint_of_nodup_append hrotTail
  have hrotSupportSubset : rot.support ⊆ c.support := by
    intro z hz
    have hz' : z ∈ ((c.dropUntil u hu).append (c.takeUntil u hu)).support := by
      simpa [rot, SimpleGraph.Walk.rotate] using hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hz' with hleft | hright
    · exact SimpleGraph.Walk.support_dropUntil_subset c hu hleft
    · exact SimpleGraph.Walk.support_takeUntil_subset c hu hright
  have hrotEdgesToC : ∀ e, e ∈ rot.edges → e ∈ c.edges := by
    intro e he
    exact (SimpleGraph.Walk.rotate_edges c hu).mem_iff.mp he
  have hleftToC : ∀ e, e ∈ arc₁.edges → e ∈ c.edges := by
    intro e he
    exact hrotEdgesToC e (SimpleGraph.Walk.edges_takeUntil_subset rot hvRot he)
  have hrightTailToC : ∀ e, e ∈ arc₂tail.edges → e ∈ c.edges := by
    intro e he
    exact hrotEdgesToC e (SimpleGraph.Walk.edges_dropUntil_subset rot hvRot he)
  have hleftRightVertices : ∀ z, z ∈ arc₁.support → z ∈ arc₂.support → z = u ∨ z = v := by
    intro z hz₁ hz₂
    by_cases hzu : z = u
    · exact Or.inl hzu
    · by_cases hzv : z = v
      · exact Or.inr hzv
      · have hz₁tail : z ∈ arc₁.support.tail := by
          rcases (SimpleGraph.Walk.mem_support_iff arc₁).1 hz₁ with h | h
          · exact (hzu h).elim
          · exact h
        have hz₂beta : z ∈ arc₂tail.support := by
          simpa only [arc₂, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz₂
        have hz₂tail : z ∈ arc₂tail.support.tail := by
          rcases (SimpleGraph.Walk.mem_support_iff arc₂tail).1 hz₂beta with h | h
          · exact (hzv h).elim
          · exact h
        exact (htailDisjoint hz₁tail hz₂tail).elim
  have hleftRightEdges : ∀ e, e ∈ arc₁.edges → e ∉ arc₂.edges := by
    intro e he₁ he₂
    have he₂tail : e ∈ arc₂tail.edges := by
      simpa only [arc₂, SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he₂
    have happendNodup : (arc₁.edges ++ arc₂tail.edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, hsplit]
      exact hrot.isTrail.edges_nodup
    exact (List.disjoint_of_nodup_append happendNodup) he₁ he₂tail
  have hleftExternalVertices : ∀ z, z ∈ arc₁.support → z ∈ r.support → z = u ∨ z = v := by
    intro z hz₁ hzr
    by_cases hzu : z = u
    · exact Or.inl hzu
    · by_cases hzv : z = v
      · exact Or.inr hzv
      · have hzc : z ∈ c.support := hrotSupportSubset (SimpleGraph.Walk.support_takeUntil_subset rot hvRot hz₁)
        exact (hreturnInterior z hzr hzu hzv hzc).elim
  have hrightExternalVertices : ∀ z, z ∈ arc₂.support → z ∈ r.support → z = u ∨ z = v := by
    intro z hz₂ hzr
    by_cases hzu : z = u
    · exact Or.inl hzu
    · by_cases hzv : z = v
      · exact Or.inr hzv
      · have hzBeta : z ∈ arc₂tail.support := by
          simpa only [arc₂, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz₂
        have hzc : z ∈ c.support := hrotSupportSubset (SimpleGraph.Walk.support_dropUntil_subset rot hvRot hzBeta)
        exact (hreturnInterior z hzr hzu hzv hzc).elim
  have hleftExternalEdges : ∀ e, e ∈ arc₁.edges → e ∉ r.edges := by
    intro e he₁ her
    exact hreturnEdges e her (hleftToC e he₁)
  have hrightExternalEdges : ∀ e, e ∈ arc₂.edges → e ∉ r.edges := by
    intro e he₂ her
    have heBeta : e ∈ arc₂tail.edges := by
      simpa only [arc₂, SimpleGraph.Walk.edges_reverse, List.mem_reverse] using he₂
    exact hreturnEdges e her (hrightTailToC e heBeta)
  let t : ThetaPaths H u v := {
    left := arc₁
    right := arc₂
    external := r
    left_path := hleftPath
    right_path := hrightPath
    external_path := hr
    left_right_vertices := hleftRightVertices
    left_external_vertices := hleftExternalVertices
    right_external_vertices := hrightExternalVertices
    left_right_edges := hleftRightEdges
    left_external_edges := hleftExternalEdges
    right_external_edges := hrightExternalEdges
  }
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · dsimp [leftRightCycle, t, arc₁, arc₂]
    rw [SimpleGraph.Walk.reverse_reverse, hsplit]
  · exact leftRightCycle_isCycle H t huv
  · exact leftExternalCycle_isCycle H t huv
  · exact externalRightCycle_isCycle H t huv
  · exact leftRightCycle_length H t
  · exact leftExternalCycle_length H t
  · exact externalRightCycle_length H t

theorem theta_base_length_eq_cycle_length
    {x u v : V} (c : H.Walk x x) (hu : u ∈ c.support)
    (t : ThetaPaths H u v)
    (hbase : leftRightCycle H t = c.rotate hu) :
    c.length = t.left.length + t.right.length := by
  rw [← rotate_length H c hu, ← hbase]
  exact leftRightCycle_length H t

/-- The walk-to-physical-cycle adapter preserves the theta length identities.
These are the exact ordinary cycle weights needed by the paper's finite
counting step; this theorem adds no root or orientation multiplicity. -/
theorem leftRightCycleWord_length (G : Erdos1016.PhysicalGraph) {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v) :
    BoundaryDecay.Cycle.length
      (Erdos1016.Nonbacktracking.cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t)
        (leftRightCycle_isCycle G.toSimpleGraph t huv)) = t.left.length + t.right.length := by
  rw [Erdos1016.Nonbacktracking.cycleWordOfWalk_length]
  exact leftRightCycle_length G.toSimpleGraph t

theorem leftExternalCycleWord_length (G : Erdos1016.PhysicalGraph) {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v) :
    BoundaryDecay.Cycle.length
      (Erdos1016.Nonbacktracking.cycleWordOfWalk G (leftExternalCycle G.toSimpleGraph t)
        (leftExternalCycle_isCycle G.toSimpleGraph t huv)) =
      t.left.length + t.external.length := by
  rw [Erdos1016.Nonbacktracking.cycleWordOfWalk_length]
  exact leftExternalCycle_length G.toSimpleGraph t

theorem externalRightCycleWord_length (G : Erdos1016.PhysicalGraph) {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v) :
    BoundaryDecay.Cycle.length
      (Erdos1016.Nonbacktracking.cycleWordOfWalk G (externalRightCycle G.toSimpleGraph t)
        (externalRightCycle_isCycle G.toSimpleGraph t huv)) =
      t.external.length + t.right.length := by
  rw [Erdos1016.Nonbacktracking.cycleWordOfWalk_length]
  exact externalRightCycle_length G.toSimpleGraph t















end Erdos1016.Proof.ExternalReturnTheta

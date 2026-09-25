import Erdos1016.Expansion.ShellCounts

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace Erdos1016.Proof.GraphBalls

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closed radius-`k` neighborhood of a finite root set, constructed by
iterating closed graph neighborhoods. -/
def graphBall (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ → Finset V
  | 0 => S
  | k + 1 => graphBall G S k ∪
      (graphBall G S k).biUnion fun v => G.neighborFinset v

/-- Exact BFS layers for the iterated closed neighborhood. -/
def graphShell (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ → Finset V
  | 0 => S
  | k + 1 => graphBall G S (k + 1) \ graphBall G S k

variable (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)

private theorem ball_subset_succ (k : ℕ) : graphBall G S k ⊆ graphBall G S (k + 1) := by
  intro v hv
  simp [graphBall, hv]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem take_length_eq_of_le {u v : V} (p : G.Walk u v) :
    ∀ i, i ≤ p.length → (p.take i).length = i := by
  induction p with
  | nil =>
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      rfl
  | @cons u v w huv p ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
          simp only [SimpleGraph.Walk.length_cons] at hi
          simp only [SimpleGraph.Walk.take, SimpleGraph.Walk.length_cons]
          exact congrArg Nat.succ (ih i (by omega))

/-- The iterated finite-set ball is exactly the set of vertices reachable
within the stated shortest-path distance from at least one root. -/
theorem graphBall_iff (k : ℕ) (v : V) :
    v ∈ graphBall G S k ↔ ∃ s ∈ S, G.Reachable s v ∧ G.dist s v ≤ k := by
  induction k generalizing v with
  | zero =>
      constructor
      · intro hv
        refine ⟨v, hv, ⟨SimpleGraph.Walk.nil⟩, by simp⟩
      · rintro ⟨s, hs, hr, hd⟩
        have hz : G.dist s v = 0 := by omega
        have hEq := hr.dist_eq_zero_iff.mp hz
        simpa [hEq] using hs
  | succ k ih =>
      constructor
      · intro hv
        simp only [graphBall, Finset.mem_union] at hv
        rcases hv with hv | hv
        · obtain ⟨s, hs, hr, hd⟩ := (ih v).mp hv
          exact ⟨s, hs, hr, hd.trans (Nat.le_succ k)⟩
        · rw [Finset.mem_biUnion] at hv
          obtain ⟨u, hu, huv⟩ := hv
          have hadj : G.Adj u v :=
            SimpleGraph.mem_neighborFinset G u v |>.mp huv
          obtain ⟨s, hs, hr, hd⟩ := (ih u).mp hu
          obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
          have hreach : G.Reachable s v := ⟨p.concat hadj⟩
          have hdist : G.dist s v ≤ k + 1 := by
            calc
              G.dist s v ≤ (p.concat hadj).length := G.dist_le _
              _ = p.length + 1 := by simp
              _ = G.dist s u + 1 := by rw [hp]
              _ ≤ k + 1 := Nat.add_le_add_right hd 1
          exact ⟨s, hs, hreach, hdist⟩
      · rintro ⟨s, hs, hr, hd⟩
        by_cases hle : G.dist s v ≤ k
        · exact Finset.mem_union_left _ ((ih v).mpr ⟨s, hs, hr, hle⟩)
        · have hdist : G.dist s v = k + 1 := by omega
          obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
          have hlen : p.length = k + 1 := by rw [hp, hdist]
          have hnotNil : ¬ p.Nil := by
            rw [SimpleGraph.Walk.not_nil_iff_lt_length]
            omega
          have hadj : G.Adj p.penultimate v := p.adj_penultimate hnotNil
          have hparentEq : p.penultimate = p.getVert k := by
            simp [SimpleGraph.Walk.penultimate, hlen]
          have hreachParent : G.Reachable s p.penultimate := by
            rw [hparentEq]
            exact ⟨p.take k⟩
          have hdistParent : G.dist s p.penultimate ≤ k := by
            rw [hparentEq]
            have h := G.dist_le (p.take k)
            have htake := take_length_eq_of_le G p k (by omega)
            rw [htake] at h
            exact h
          have hparentBall : p.penultimate ∈ graphBall G S k :=
            (ih p.penultimate).mpr ⟨s, hs, hreachParent, hdistParent⟩
          simp only [graphBall, Finset.mem_union]
          right
          exact Finset.mem_biUnion.mpr ⟨p.penultimate, hparentBall,
          SimpleGraph.mem_neighborFinset G p.penultimate v |>.mpr hadj⟩



private theorem ball_mem_neighborhood (k : ℕ) {v : V}
    (hv : v ∈ graphBall G S (k + 1)) (hnot : v ∉ graphBall G S k) :
    ∃ u ∈ graphBall G S k, G.Adj u v := by
  simp only [graphBall, mem_union] at hv
  rcases hv with hv | hv
  · exact (hnot hv).elim
  · rw [mem_biUnion] at hv
    rcases hv with ⟨u, hu, hv⟩
    exact ⟨u, hu, (SimpleGraph.mem_neighborFinset G u v).mp hv⟩

private theorem shell_mem_parent_ball (k : ℕ) {u : V}
    (hu : u ∈ graphShell G S (k + 1)) :
    ∃ p ∈ graphBall G S k, G.Adj p u := by
  simp only [graphShell, mem_sdiff] at hu
  exact ball_mem_neighborhood G S k hu.1 hu.2

private theorem shell_mem_parent_shell (k : ℕ) {u : V}
    (hu : u ∈ graphShell G S (k + 1)) :
    ∃ p ∈ graphShell G S k, G.Adj p u := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨p, hp, hpu⟩ := shell_mem_parent_ball G S 0 hu
    exact ⟨p, by simpa [graphShell, graphBall] using hp, hpu⟩
  · have hkpos : 1 ≤ k := by omega
    obtain ⟨p, hp, hpu⟩ := shell_mem_parent_ball G S k hu
    have hk' : (k - 1) + 1 = k := by omega
    have hpnot : p ∉ graphBall G S (k - 1) := by
      intro hprev
      have huBall : u ∈ graphBall G S k := by
        rw [← hk']
        simp only [graphBall, mem_union]
        right
        exact mem_biUnion.mpr ⟨p, hprev, (SimpleGraph.mem_neighborFinset G p u).mpr hpu⟩
      exact (mem_sdiff.mp hu).2 huBall
    have hpShell : p ∈ graphShell G S k := by
      rw [← hk']
      simp only [graphShell, mem_sdiff]
      rw [← hk'] at hp
      exact ⟨hp, hpnot⟩
    exact ⟨p, hpShell, hpu⟩

private theorem shell_neighbor_forbidden (k : ℕ) (hk : 1 ≤ k) {u : V}
    (hu : u ∈ graphShell G S k) :
    ∃ p, G.Adj u p ∧ p ∉ graphShell G S (k + 1) := by
  have hk' : (k - 1) + 1 = k := by omega
  have hu' : u ∈ graphShell G S ((k - 1) + 1) := by rw [hk']; exact hu
  obtain ⟨p, hp, hpu⟩ := shell_mem_parent_ball G S (k - 1) hu'
  refine ⟨p, hpu.symm, ?_⟩
  intro hpnext
  have hpball : p ∈ graphBall G S k := by
    rw [← hk']
    exact ball_subset_succ G S (k - 1) hp
  have hnot := (mem_sdiff.mp hpnext).2
  exact hnot hpball

/-- If every vertex of `B` has a parent in `A`, and every vertex of `A` has
some neighbor outside `B`, then a subcubic graph has at most two children in
`B` per vertex of `A`. -/
private theorem card_children_le_two
    {A B : Finset V}
    (hparent : ∀ b ∈ B, ∃ a ∈ A, G.Adj a b)
    (hforbidden : ∀ a ∈ A, ∃ c, G.Adj a c ∧ c ∉ B)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    B.card ≤ 2 * A.card := by
  classical
  let pairs : Finset (V × V) := A.attach.biUnion fun a =>
    ((G.neighborFinset a.1).filter (fun b => b ∈ B)).image fun b => (a.1, b)
  let parent : {b // b ∈ B} → V := fun b => Classical.choose (hparent b.1 b.2)
  have hparent_spec (b : {b // b ∈ B}) : parent b ∈ A ∧ G.Adj (parent b) b.1 :=
    Classical.choose_spec (hparent b.1 b.2)
  have hpairmem (b : {b // b ∈ B}) : (parent b, b.1) ∈ pairs := by
    change (parent b, b.1) ∈ A.attach.biUnion (fun a =>
      ((G.neighborFinset a.1).filter (fun v => v ∈ B)).image fun v => (a.1, v))
    rw [mem_biUnion]
    refine ⟨⟨parent b, (hparent_spec b).1⟩, by simp, ?_⟩
    rw [mem_image]
    refine ⟨b.1, ?_, rfl⟩
    simp only [mem_filter]
    constructor
    · exact SimpleGraph.mem_neighborFinset G (parent b) b.1 |>.mpr (hparent_spec b).2
    · exact b.2
  let f : {b // b ∈ B} → {p // p ∈ pairs} := fun b => ⟨(parent b, b.1), hpairmem b⟩
  have hf : Function.Injective f := by
    intro b c h
    apply Subtype.ext
    have hs := congrArg (fun p : {p // p ∈ pairs} => p.1.2) h
    exact hs
  have hcard : Fintype.card {b // b ∈ B} ≤ Fintype.card {p // p ∈ pairs} :=
    Fintype.card_le_of_injective f hf
  have hpaircard : pairs.card ≤ 2 * A.card := by
    calc
      pairs.card ≤ ∑ a ∈ A.attach,
          (((G.neighborFinset a.1).filter (fun b => b ∈ B)).image fun b => (a.1, b)).card :=
        Finset.card_biUnion_le
      _ = ∑ a ∈ A.attach, ((G.neighborFinset a.1).filter (fun b => b ∈ B)).card := by
        apply sum_congr rfl
        intro a ha
        exact Finset.card_image_of_injective _ (fun b c h => congrArg Prod.snd h)
      _ ≤ ∑ _a ∈ A.attach, 2 := by
        apply sum_le_sum
        intro a ha
        obtain ⟨c, hac, hcb⟩ := hforbidden a.1 a.2
        have hc : c ∈ G.neighborFinset a.1 :=
          SimpleGraph.mem_neighborFinset G a.1 c |>.2 hac
        have hsub : (G.neighborFinset a.1).filter (fun b => b ∈ B) ⊆
            (G.neighborFinset a.1).erase c := by
          intro b hb
          simp only [mem_filter] at hb
          simp only [mem_erase]
          exact ⟨fun heq => hcb (heq ▸ hb.2), hb.1⟩
        have hfilter := card_le_card hsub
        rw [card_erase_of_mem hc] at hfilter
        have hdeg : (G.neighborFinset a.1).card ≤ 3 := by
          simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree a.1
        omega
      _ = 2 * A.card := by simp [Nat.mul_comm]
  have hBcard : Fintype.card {b // b ∈ B} = B.card := by simp
  have hPcard : Fintype.card {p // p ∈ pairs} = pairs.card := by simp
  rw [hBcard, hPcard] at hcard
  exact hcard.trans hpaircard

theorem graphShell_one_card_le (hdegree : ∀ v, G.degree v ≤ 3) :
    (graphShell G S 1).card ≤ 3 * S.card := by
  classical
  have hsub : graphShell G S 1 ⊆ S.biUnion (fun v => G.neighborFinset v) := by
    intro v hv
    have hparent := shell_mem_parent_ball G S 0 hv
    rcases hparent with ⟨u, hu, huv⟩
    exact mem_biUnion.mpr ⟨u, by simpa [graphBall] using hu,
      SimpleGraph.mem_neighborFinset G u v |>.2 huv⟩
  calc
    (graphShell G S 1).card ≤ (S.biUnion (fun v => G.neighborFinset v)).card := card_le_card hsub
    _ ≤ ∑ v ∈ S, (G.neighborFinset v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ S, 3 := by
      apply sum_le_sum
      intro v hv
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree v
    _ = 3 * S.card := by simp [Nat.mul_comm]

theorem graphShell_succ_card_le (k : ℕ) (hk : 1 ≤ k)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    (graphShell G S (k + 1)).card ≤ 2 * (graphShell G S k).card := by
  apply card_children_le_two G
  · intro b hb
    obtain ⟨a, ha, hab⟩ := shell_mem_parent_shell G S k hb
    exact ⟨a, ha, hab⟩
  · intro a ha
    exact shell_neighbor_forbidden G S k hk ha
  · exact hdegree

theorem graphBall_card_le (q : ℕ) (hdegree : ∀ v, G.degree v ≤ 3) :
    (graphBall G S q).card ≤ 3 * S.card * 2 ^ q := by
  have hzero : (graphShell G S 0).card ≤ S.card := by simp [graphShell]
  have hone := graphShell_one_card_le G S hdegree
  have hstep : ∀ k, 1 ≤ k → (graphShell G S (k + 1)).card ≤
      2 * (graphShell G S k).card := fun k hk => graphShell_succ_card_le G S k hk hdegree
  have hball : (graphBall G S q).card =
      ∑ k ∈ Finset.range (q + 1), (graphShell G S k).card := by
    induction q with
    | zero => simp [graphShell, graphBall]
    | succ q ih =>
        rw [Finset.sum_range_succ, ← ih]
        have hunion : graphBall G S q ∪ graphShell G S (q + 1) =
            graphBall G S (q + 1) := by
          ext v
          simp only [Finset.mem_union, graphShell, Finset.mem_sdiff]
          constructor
          · rintro (hv | ⟨hv, _⟩)
            · exact ball_subset_succ G S q hv
            · exact hv
          · intro hv
            by_cases hq : v ∈ graphBall G S q
            · exact Or.inl hq
            · exact Or.inr ⟨hv, hq⟩
        have hdisj : Disjoint (graphBall G S q) (graphShell G S (q + 1)) := by
          rw [Finset.disjoint_left]
          intro v hv hvs
          exact (Finset.mem_sdiff.mp hvs).2 hv
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hsum := Erdos1016.Proof.ShellCounts.sum_shell_card_le
    (fun k => (graphShell G S k).card) S.card q hzero hone hstep
  rw [hball]
  exact hsum

end Erdos1016.Proof.GraphBalls

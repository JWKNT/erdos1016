import Erdos1016.Extremal.Statement

set_option autoImplicit false

/-!
# Complete graph witnesses for the pancyclic extremal set

The complete graph contains a cycle of every length from three through its
order. The cycles are built from a descending walk on an initial segment of
`Fin` and one closing edge.
-/

namespace Erdos1016.Problem1016
open SimpleGraph

private def descendingWalk (n : ℕ) : (k : ℕ) → (hk : k ≤ n) →
    (completeGraph (Fin (n + 1))).Walk ⟨k, Nat.lt_succ_of_le hk⟩
      (0 : Fin (n + 1))
  | 0, _ => Walk.nil
  | k + 1, hk =>
      Walk.cons (by
        change (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) ≠
          ⟨k, Nat.lt_succ_of_le (by omega)⟩
        intro he
        have hv := congrArg Fin.val he
        simp at hv) (descendingWalk n k (by omega))

private theorem descendingWalk_support_bound (n : ℕ) :
    ∀ k hk x, x ∈ (descendingWalk n k hk).support → x.val ≤ k := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      have hx' : x = (0 : Fin (n + 1)) := by simpa [descendingWalk] using hx
      subst x
      simp
  | succ k ih =>
      intro hk x hx
      simp only [descendingWalk, Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp
      · exact (ih (by omega) x hx).trans (by omega)

private theorem descendingWalk_isPath (n : ℕ) :
    ∀ k hk, (descendingWalk n k hk).IsPath := by
  intro k
  induction k with
  | zero => intro hk; simp [descendingWalk, Walk.isPath_def]
  | succ k ih =>
      intro hk
      dsimp only [descendingWalk]
      rw [Walk.cons_isPath_iff]
      refine ⟨ih (by omega), ?_⟩
      intro hx
      have hb := descendingWalk_support_bound n k (by omega) ⟨k + 1, by omega⟩ hx
      simp at hb

private theorem closingEdge_not_mem_descendingWalk (n : ℕ) (hn : 2 ≤ n) :
    ∀ k hk, s(0, Fin.last n) ∉ (descendingWalk n k hk).edges := by
  intro k
  induction k with
  | zero => intro hk; simp [descendingWalk]
  | succ k ih =>
      intro hk he
      dsimp only [descendingWalk] at he
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · have he' := Sym2.eq_iff.mp he
        rcases he' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · have hv₁ := congrArg Fin.val h₁
          have hv₂ := congrArg Fin.val h₂
          simp at hv₁ hv₂
        · have hv₁ := congrArg Fin.val h₁
          have hv₂ := congrArg Fin.val h₂
          simp at hv₁ hv₂
          omega
      · have hlast : Fin.last n ∈ (descendingWalk n k (by omega)).support :=
          Walk.snd_mem_support_of_mem_edges _ he
        have hb := descendingWalk_support_bound n k (by omega) (Fin.last n) hlast
        simp at hb
        omega

private def completeCycle (n : ℕ) (hn : 2 ≤ n) :
    (completeGraph (Fin (n + 1))).Walk 0 0 := by
  have hclose : (completeGraph (Fin (n + 1))).Adj 0 (Fin.last n) := by
    change (0 : Fin (n + 1)) ≠ Fin.last n
    intro he
    have hv := congrArg Fin.val he
    simp at hv
    omega
  exact Walk.cons hclose (descendingWalk n n le_rfl)

private theorem completeCycle_isCycle (n : ℕ) (hn : 2 ≤ n) :
    (completeCycle n hn).IsCycle := by
  unfold completeCycle
  rw [Walk.cons_isCycle_iff]
  exact ⟨descendingWalk_isPath n n le_rfl,
    closingEdge_not_mem_descendingWalk n hn n le_rfl⟩

private theorem descendingWalk_length (n : ℕ) :
    ∀ k hk, (descendingWalk n k hk).length = k := by
  intro k
  induction k with
  | zero => intro hk; simp [descendingWalk]
  | succ k ih =>
      intro hk
      simp [descendingWalk, ih (by omega)]

private theorem completeCycle_length (n : ℕ) (hn : 2 ≤ n) :
    (completeCycle n hn).length = n + 1 := by
  unfold completeCycle
  rw [Walk.length_cons, descendingWalk_length]

/-- The complete graph on `Fin n` contains every cycle length in the required
range; the statement is vacuous for `n < 3`. -/
theorem completeGraph_isPancyclic (n : ℕ) :
    IsPancyclic (completeGraph (Fin n)) := by
  intro ℓ hℓn hℓ
  let m := ℓ - 1
  have hm : m + 1 = ℓ := by dsimp [m]; omega
  have hmn : m + 1 ≤ n := by rw [hm]; simpa using hℓ
  let f : completeGraph (Fin (m + 1)) →g completeGraph (Fin n) := {
    toFun := Fin.castLE hmn
    map_rel' := by
      intro a b hab
      change a ≠ b at hab
      change Fin.castLE hmn a ≠ Fin.castLE hmn b
      intro he
      apply hab
      apply Fin.ext
      simpa using congrArg Fin.val he
  }
  have hf : Function.Injective f := by
    intro a b he
    apply Fin.ext
    simpa using congrArg Fin.val he
  let p := completeCycle m (by dsimp [m]; omega)
  refine ⟨f (0 : Fin (m + 1)), p.map f, ?_, ?_⟩
  · exact SimpleGraph.Walk.IsCycle.map (f := f) hf
      (completeCycle_isCycle m (by dsimp [m]; omega))
  · rw [Walk.length_map]
    dsimp [p]
    rw [completeCycle_length]
    exact hm

/-- A complete graph witnesses nonemptiness of the candidate excess set at
every order. -/
theorem candidateExcesses_nonempty (n : ℕ) : (candidateExcesses n).Nonempty := by
  classical
  exact ⟨excess n (completeGraph (Fin n)),
    ⟨completeGraph (Fin n), completeGraph_isPancyclic n, rfl⟩⟩

end Erdos1016.Problem1016

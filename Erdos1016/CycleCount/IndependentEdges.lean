import Erdos1016.CycleCount.ChordExtension

set_option autoImplicit false

/-!
# Independent edges of the cycle space

A graph of cycle rank `r` has, for each `t ≤ r`, a set of `t` edges on which
the cycle space restricts onto all binary words. Equivalently, exactly
`2^(r - t)` even subgraphs avoid all of them. The proof is a direct count. It
uses no spanning tree. Each chosen edge lies on an even subgraph, so each of
its ends meets a second edge.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.CycleCount
open PhysicalGraph

theorem f2_cases (a : F₂) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The cycle-space elements that vanish on every edge of `D`. -/
def avoiding (G : PhysicalGraph) (D : Finset G.Edge) : Finset G.CycleSpace := by
  classical
  exact Finset.univ.filter fun x => ∀ e ∈ D, x.1 e = 0

theorem mem_avoiding (G : PhysicalGraph) (D : Finset G.Edge) (x : G.CycleSpace) :
    x ∈ avoiding G D ↔ ∀ e ∈ D, x.1 e = 0 := by
  simp [avoiding]

/-- One more edge on an avoiding even subgraph halves the avoiding set. -/
theorem avoiding_insert_card (G : PhysicalGraph) (D : Finset G.Edge) (e : G.Edge)
    (y : G.CycleSpace) (hy : y ∈ avoiding G D) (hye : y.1 e ≠ 0) :
    (avoiding G (insert e D)).card * 2 = (avoiding G D).card := by
  classical
  have hy1 : y.1 e = 1 := (f2_cases (y.1 e)).resolve_left hye
  have hy0 := (mem_avoiding G D y).1 hy
  have hyy : y + y = 0 := by
    apply Subtype.ext
    funext f
    change y.1 f + y.1 f = 0
    rcases f2_cases (y.1 f) with h | h <;> rw [h] <;> decide
  have hadd : ∀ x : G.CycleSpace, x ∈ avoiding G D → x + y ∈ avoiding G D := by
    intro x hx
    refine (mem_avoiding G D _).2 ?_
    intro f hf
    have hx0 := (mem_avoiding G D x).1 hx f hf
    change x.1 f + y.1 f = 0
    rw [hx0, hy0 f hf, add_zero]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := avoiding G D)
    (fun x : G.CycleSpace => x.1 e = 0)
  have hzero : (avoiding G D).filter (fun x : G.CycleSpace => x.1 e = 0) =
      avoiding G (insert e D) := by
    ext x
    simp only [Finset.mem_filter, mem_avoiding, Finset.mem_insert, forall_eq_or_imp]
    tauto
  have hbij : ((avoiding G D).filter (fun x : G.CycleSpace => ¬ x.1 e = 0)).card =
      ((avoiding G D).filter (fun x : G.CycleSpace => x.1 e = 0)).card := by
    apply Finset.card_bij (fun x _ => x + y)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hadd x hx.1, ?_⟩
      have hx1 : x.1 e = 1 := (f2_cases (x.1 e)).resolve_left hx.2
      change x.1 e + y.1 e = 0
      rw [hx1, hy1]
      decide
    · intro x _ x' _ h
      exact add_right_cancel h
    · intro z hz
      rw [Finset.mem_filter] at hz
      refine ⟨z + y, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hadd z hz.1, ?_⟩
        change ¬ (z.1 e + y.1 e = 0)
        rw [hz.2, hy1]
        decide
      · rw [add_assoc, hyy, add_zero]
  rw [hzero] at hsplit hbij
  omega

/-- For `t ≤ r` there are `t` edges that exactly `2^(r - t)` even subgraphs avoid. -/
theorem exists_independent_edges (G : PhysicalGraph) :
    ∀ t : ℕ, t ≤ G.cycleRank →
      ∃ D : Finset G.Edge, D.card = t ∧
        (avoiding G D).card * 2 ^ t = 2 ^ G.cycleRank ∧
        ∀ e ∈ D, ∃ y : G.CycleSpace, y.1 e ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨∅, rfl, ?_, by simp⟩
    have hall : avoiding G ∅ = Finset.univ := by
      ext x
      simp [mem_avoiding]
    rw [hall, Finset.card_univ, G.cycleSpace_card]
    simp
  | succ t ih =>
    intro ht
    obtain ⟨D, hD, hcard, hwit⟩ := ih (by omega)
    have hlt : 1 < (avoiding G D).card := by
      by_contra hle
      have hle' : (avoiding G D).card ≤ 1 := by omega
      have hmul : (avoiding G D).card * 2 ^ t ≤ 1 * 2 ^ t :=
        Nat.mul_le_mul_right _ hle'
      have hpow : 2 ^ t < 2 ^ G.cycleRank :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      rw [hcard, one_mul] at hmul
      omega
    obtain ⟨y, hy, hy0⟩ := Finset.exists_mem_ne hlt (0 : G.CycleSpace)
    have hex : ∃ e, y.1 e ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy0 (Subtype.ext (funext h))
    obtain ⟨e, he⟩ := hex
    have heD : e ∉ D := fun hmem => he ((mem_avoiding G D y).1 hy e hmem)
    refine ⟨insert e D, by rw [Finset.card_insert_of_not_mem heD, hD], ?_, ?_⟩
    · have h2 := avoiding_insert_card G D e y hy he
      rw [pow_succ, ← hcard, ← h2]
      ring
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨y, he⟩
      · exact hwit f hf

theorem selectedDegree_eq_card (G : PhysicalGraph) (x : G.Word) (v : G.Vertex)
    [DecidablePred fun e : G.Edge => x e ≠ 0 ∧ G.incident e v] :
    G.selectedDegree x v =
      (Finset.univ.filter fun e : G.Edge => x e ≠ 0 ∧ G.incident e v).card := by
  unfold PhysicalGraph.selectedDegree
  congr

/-- An edge on an even subgraph has a third vertex next to its head. -/
theorem exists_apex (G : PhysicalGraph) (y : G.CycleSpace) (e : G.Edge)
    (he : y.1 e ≠ 0) :
    ∃ w : G.Vertex, w ≠ G.src e ∧ G.toSimpleGraph.Adj (G.dst e) w := by
  classical
  have hb : G.boundary y.1 (G.dst e) = 0 :=
    congrFun (LinearMap.mem_ker.mp y.2) (G.dst e)
  rw [Nonbacktracking.boundary_eq_selectedDegree_cast, selectedDegree_eq_card] at hb
  have heven := (ZMod.eq_zero_iff_even).1 hb
  have hmem : e ∈ Finset.univ.filter
      fun f : G.Edge => y.1 f ≠ 0 ∧ G.incident f (G.dst e) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, Or.inr rfl⟩
  have hpos := Finset.card_pos.mpr ⟨e, hmem⟩
  have hcard : 1 < (Finset.univ.filter
      fun f : G.Edge => y.1 f ≠ 0 ∧ G.incident f (G.dst e)).card := by
    obtain ⟨k, hk⟩ := heven
    omega
  obtain ⟨g, hg, hge⟩ := Finset.exists_mem_ne hcard e
  have hginc : G.incident g (G.dst e) := (Finset.mem_filter.mp hg).2.2
  rcases hginc with hs | hd
  · refine ⟨G.dst g, ?_, adj_of_endpoints G g (Or.inl ⟨hs, rfl⟩)⟩
    intro h
    exact hge (G.simple g e (Or.inr ⟨hs, h⟩))
  · refine ⟨G.src g, ?_, adj_of_endpoints G g (Or.inr ⟨rfl, hd⟩)⟩
    intro h
    exact hge (G.simple g e (Or.inl ⟨h, hd⟩))

end Erdos1016.CycleCount

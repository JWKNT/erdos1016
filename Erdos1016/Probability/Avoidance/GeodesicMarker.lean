import Erdos1016.Probability.Avoidance.LevelWindowBoundary
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# A connected thin marker from geodesics

Choose one shortest walk from the root to each port. Their union is connected.
Each chosen walk has at most one vertex in each distance level.
-/
noncomputable section

namespace Erdos1016.Probability.GeodesicMarker
open FiniteMultiGraph

local instance markerDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Walks
variable {V : Type*} {H : SimpleGraph V} {u v : V}

theorem length_take (p : H.Walk u v) (n : ℕ) :
    (p.take n).length = min n p.length := by
  induction p generalizing n with
  | nil => simp [SimpleGraph.Walk.take]
  | cons h p ih =>
    cases n with
    | zero => simp [SimpleGraph.Walk.take]
    | succ n => simp [SimpleGraph.Walk.take, ih, Nat.succ_min_succ]

theorem length_drop (p : H.Walk u v) (n : ℕ) :
    (p.drop n).length = p.length-n := by
  induction p generalizing n with
  | nil => simp [SimpleGraph.Walk.drop]
  | cons h p ih =>
    cases n with
    | zero => simp [SimpleGraph.Walk.drop]
    | succ n => simp [SimpleGraph.Walk.drop, ih]

theorem dist_getVert (hH : H.Connected) (p : H.Walk u v)
    (hp : p.length = H.dist u v) (n : ℕ) (hn : n ≤ p.length) :
    H.dist u (p.getVert n) = n := by
  have ht := H.dist_le (p.take n)
  have hd := H.dist_le (p.drop n)
  rw [length_take, min_eq_left hn] at ht
  rw [length_drop] at hd
  have hh := hH.dist_triangle (u := u) (v := p.getVert n) (w := v)
  omega

theorem dist_injective_on_support (hH : H.Connected) (p : H.Walk u v)
    (hp : p.length = H.dist u v) :
    Set.InjOn (H.dist u) {w | w ∈ p.support} := by
  intro a ha b hb he
  obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha
  obtain ⟨j, hj, hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hb
  have hdi := dist_getVert hH p hp i hil
  have hdj := dist_getVert hH p hp j hjl
  rw [hi] at hdi
  rw [hj] at hdj
  have hij : i = j := by omega
  exact hi.symm.trans (hij ▸ hj)

end Walks

variable (G : FiniteMultiGraph) (hG : G.toSimpleGraph.Connected)
  (ports : Finset G.Vertex) (o : G.Vertex)

def route (v : G.Vertex) : G.toSimpleGraph.Walk o v :=
  Classical.choose (hG.exists_walk_length_eq_dist o v)

theorem route_length (v : G.Vertex) :
    (route G hG o v).length = G.toSimpleGraph.dist o v :=
  Classical.choose_spec (hG.exists_walk_length_eq_dist o v)

def marker : Finset G.Vertex := ports.biUnion fun v => (route G hG o v).support.toFinset

theorem mem_marker (v : G.Vertex) :
    v ∈ marker G hG ports o ↔ ∃ p ∈ ports, v ∈ (route G hG o p).support := by
  simp [marker]

theorem ports_subset_marker : ports ⊆ marker G hG ports o := by
  intro v hv
  exact (mem_marker G hG ports o v).mpr ⟨v, hv, (route G hG o v).end_mem_support⟩

theorem root_mem_marker (ho : o ∈ ports) : o ∈ marker G hG ports o :=
  ports_subset_marker G hG ports o ho

theorem marker_connected (ho : o ∈ ports) :
    (G.toSimpleGraph.induce (↑(marker G hG ports o) : Set G.Vertex)).Connected := by
  apply G.toSimpleGraph.induce_connected_of_patches o (root_mem_marker G hG ports o ho)
  intro v hv
  obtain ⟨p, hp, hvp⟩ := (mem_marker G hG ports o v).mp hv
  refine ⟨{w | w ∈ (route G hG o p).support}, ?_, (route G hG o p).start_mem_support, hvp, ?_⟩
  · intro w hw
    exact (mem_marker G hG ports o w).mpr ⟨p, hp, hw⟩
  · exact (route G hG o p).connected_induce_support _ _

def level (v : G.Vertex) : ℤ := G.toSimpleGraph.dist o v

theorem route_layer_card_le_one (v : G.Vertex) (j : ℤ) :
    ((route G hG o v).support.toFinset.filter fun w => level G o w = j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  apply dist_injective_on_support hG (route G hG o v) (route_length G hG o v)
    (List.mem_toFinset.mp ha'.1) (List.mem_toFinset.mp hb'.1)
  have he : level G o a = level G o b := ha'.2.trans hb'.2.symm
  dsimp [level] at he
  exact_mod_cast he

theorem marker_layer_card (j : ℤ) :
    (LevelWindowBoundary.markedLayer G (marker G hG ports o) (level G o) j).card ≤ ports.card := by
  have hs : LevelWindowBoundary.markedLayer G (marker G hG ports o) (level G o) j ⊆
      ports.biUnion (fun v => (route G hG o v).support.toFinset.filter fun w => level G o w = j) := by
    intro w hw
    have hh := (Finset.mem_filter.mp hw).2
    obtain ⟨p, hp, hwp⟩ := (mem_marker G hG ports o w).mp hh.1
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hwp, hh.2⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ∑ v ∈ ports, ((route G hG o v).support.toFinset.filter fun w => level G o w = j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ ports, 1 := Finset.sum_le_sum (fun v _ => route_layer_card_le_one G hG o v j)
    _ = ports.card := by simp

include hG in
theorem level_edge (e : G.Edge) :
    level G o (G.src e) ≤ level G o (G.dst e)+1 ∧
      level G o (G.dst e) ≤ level G o (G.src e)+1 := by
  by_cases he : G.src e = G.dst e
  · simp [he]
  · have ha : G.toSimpleGraph.Adj (G.src e) (G.dst e) := ⟨he, e, Or.inl ⟨rfl, rfl⟩⟩
    have hd : G.toSimpleGraph.dist (G.src e) (G.dst e) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ha
    have h1 := hG.dist_triangle (u := o) (v := G.dst e) (w := G.src e)
    have h2 := hG.dist_triangle (u := o) (v := G.src e) (w := G.dst e)
    have hrev : G.toSimpleGraph.dist (G.dst e) (G.src e) = 1 := by
      rw [SimpleGraph.dist_comm]; exact hd
    rw [hrev] at h1
    rw [hd] at h2
    constructor <;> dsimp [level] <;> omega

end Erdos1016.Probability.GeodesicMarker

import Erdos1016.ExactMaximumSupport.FourThinLayers
import Erdos1016.ExactMaximumSupport.NetworkFourCycle
import Erdos1016.ExactMaximumSupport.NetworkParallel
import Erdos1016.ExactMaximumSupport.DistanceFourLayers
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A physical cycle in four distance layers

The finite square lemma gives four actual vertices. Their adjacencies lift
to physical edge labels, so the conclusion counts multigraph edges.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkFourLayers
open BoundaryTrace BoundaryTrace.Network

local instance networkFourLayersDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The actual vertices in four consecutive distance layers. -/
def window (s : V) (k : ℕ) (v : V) : Prop :=
  k ≤ N.graph.dist s v ∧ N.graph.dist s v ≤ k + 3

omit [Fintype V] [Fintype E] in
/-- Every neighbor of a middle-layer vertex stays inside the four-layer window. -/
theorem neighbor_middle_mem_window (hconn : N.graph.Connected)
    (s : V) (k : ℕ) {v w : V}
    (hv : N.graph.dist s v = k + 1 ∨ N.graph.dist s v = k + 2)
    (hadj : N.graph.Adj v w) : window N s k w := by
  have h1 := hconn.dist_triangle (u := s) (v := v) (w := w)
  have h2 := hconn.dist_triangle (u := s) (v := w) (w := v)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h1
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at h2
  unfold window
  rcases hv with hv | hv <;> omega

/-- Without a short cycle in the window, physical degree equals degree at each middle vertex. -/
theorem middle_degree_eq_of_no_short_cycle (hconn : N.graph.Connected)
    (s : V) (k : ℕ)
    (hno : ¬ ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → window N s k v)
    (v : V) (hv : N.graph.dist s v = k + 1 ∨ N.graph.dist s v = k + 2) :
    N.deg (fun _ => 1) v = N.graph.degree v := by
  apply NetworkParallel.degree_eq_of_unique_at N v
  intro e f w he hf
  by_contra hef
  obtain ⟨z,hz,hlen,hsupport⟩ := NetworkParallel.exists_cycle_of_parallel N hef he hf
  apply hno
  refine ⟨z,hz,hlen.trans (by decide),?_⟩
  intro x hx
  rcases hsupport x hx with rfl | rfl
  · unfold window
    rcases hv with hv | hv <;> omega
  · exact neighbor_middle_mem_window N hconn s k hv ⟨e,he⟩

/-- An injectively labelled four-layer window contains an actual physical cycle. -/
theorem exists_cycle_of_layer_embedding
    (ι : FourThinLayers.Vertex → V) (hinj : Function.Injective ι)
    (hlevel : ∀ u v, (N.graph.comap ι).Adj u v →
      u.1.val ≤ v.1.val + 1 ∧ v.1.val ≤ u.1.val + 1)
    (hmiddle : ∀ v : FourThinLayers.Vertex, v.1 = 1 ∨ v.1 = 2 →
      (N.graph.comap ι).degree v = 3)
    (hfirst : ∀ v : FourThinLayers.Vertex, v.1 = 0 →
      (N.graph.comap ι).degree v ≤ 2)
    (hdegree : ∀ v : FourThinLayers.Vertex, (N.graph.comap ι).degree v ≤ 3)
    (hprev : ∀ v : FourThinLayers.Vertex, 0 < v.1.val →
      ∃ w : FourThinLayers.Vertex,
        (N.graph.comap ι).Adj w v ∧ w.1.val + 1 = v.1.val) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → v ∈ Set.range ι := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hab',hbc',hcd',hda'⟩ :=
    FourThinLayers.exists_square (N.graph.comap ι) hlevel hmiddle hfirst hdegree hprev
  obtain ⟨z,hz,hlen,hsupport⟩ := NetworkFourCycle.exists_cycle_of_four_adj N
    (ι a) (ι b) (ι c) (ι d)
    (hinj.ne hab) (hinj.ne hac) (hinj.ne had)
    (hinj.ne hbc) (hinj.ne hbd) (hinj.ne hcd)
    hab' hbc' hcd' hda'
  refine ⟨z,hz,hlen,?_⟩
  intro v hv
  have h := hsupport v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨a,rfl⟩
  · exact ⟨b,rfl⟩
  · exact ⟨c,rfl⟩
  · exact ⟨d,rfl⟩

/-- Four actual thin distance layers contain a physical cycle of length at most four. -/
theorem exists_cycle_of_four_distance_layers
    (hconn : N.graph.Connected) (s : V) (k : ℕ) (hk : 1 ≤ k)
    (hcard : ∀ i : Fin 4, Nat.card {v : V // N.graph.dist s v = k + i.val} = 2)
    (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hmiddle : ∀ v, N.graph.dist s v = k + 1 ∨ N.graph.dist s v = k + 2 →
      N.deg (fun _ => 1) v = 3) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → window N s k v := by
  by_contra hno
  have hdegree' (v : V) : N.graph.degree v ≤ 3 :=
    (NetworkParallel.graph_degree_le N v).trans (hdegree v)
  have hmiddle' (v : V)
      (hv : N.graph.dist s v = k + 1 ∨ N.graph.dist s v = k + 2) :
      N.graph.degree v = 3 := by
    rw [← middle_degree_eq_of_no_short_cycle N hconn s k hno v hv]
    exact hmiddle v hv
  obtain ⟨ι,hinj,hdist,hlevel,hmid,hfirst,hdeg,hprev⟩ :=
    DistanceFourLayers.exists_layer_embedding N.graph s k hcard hconn hk hdegree' hmiddle'
  obtain ⟨z,hz,hlen,hsupport⟩ :=
    exists_cycle_of_layer_embedding N ι hinj hlevel hmid hfirst hdeg hprev
  apply hno
  refine ⟨z,hz,hlen,?_⟩
  intro v hv
  obtain ⟨x,rfl⟩ := hsupport v hv
  unfold window
  rw [hdist]
  have hx := x.1.isLt
  omega

end Erdos1016.ExactMaximumSupport.NetworkFourLayers

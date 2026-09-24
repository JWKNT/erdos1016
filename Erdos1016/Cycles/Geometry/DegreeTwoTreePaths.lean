import Erdos1016.Graph.ConnectedRegionBoundary
import Erdos1016.Cycles.Geometry.TreePaths

set_option autoImplicit false

namespace Erdos1016.Proof.FiniteTreeDegreeTwoPath

open SimpleGraph

variable {V : Type*}

/-- A vertex strictly inside a path has two distinct neighbors on that path. -/
theorem exists_two_path_neighbors_of_mem_support_of_ne_endpoints
    {H : SimpleGraph V} {a b : V} {p : H.Walk a b}
    (hp : p.IsPath) :
    ∀ ⦃v⦄, v ∈ p.support → v ≠ a → v ≠ b →
      ∃ x y, x ≠ y ∧ H.Adj v x ∧ H.Adj v y ∧
        x ∈ p.support ∧ y ∈ p.support := by
  induction p with
  | nil =>
      intro v hv hva hvb
      exact (hva (by simpa using hv)).elim
  | @cons a c b hac q ih =>
      intro v hv hva hvb
      simp only [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact (hva rfl).elim
      · by_cases hvc : v = c
        · subst v
          have hqpath : q.IsPath := Walk.IsPath.of_cons hp
          cases q with
          | nil => exact (hvb rfl).elim
          | @cons c d b hcd r =>
              have hac_not_d : a ≠ d := by
                intro had
                subst d
                have ha_mem : a ∈ (Walk.cons hcd r).support := by
                  exact List.mem_cons_of_mem _ (Walk.start_mem_support r)
                have hnot := (Walk.cons_isPath_iff hac (Walk.cons hcd r)).mp hp |>.2
                exact hnot ha_mem
              refine ⟨a, d, hac_not_d, hac.symm, hcd, ?_, ?_⟩
              · simp
              · simp [Walk.support_cons]
        · obtain ⟨x, y, hxy, hvx, hvy, hxq, hyq⟩ :=
            ih (Walk.IsPath.of_cons hp) hv hvc hvb
          exact ⟨x, y, hxy, hvx, hvy,
            List.mem_cons_of_mem _ hxq, List.mem_cons_of_mem _ hyq⟩

/-- Every finite connected acyclic simple graph with maximum degree at most two
has a path whose support contains every vertex. -/
theorem exists_spanning_path
    (H : SimpleGraph V) [Fintype V] [DecidableRel H.Adj]
    (hconn : H.Connected) (hacyc : H.IsAcyclic)
    (hdegree : ∀ v, (H.neighborFinset v).card ≤ 2) :
    ∃ a b, ∃ p : H.Walk a b, p.IsPath ∧ ∀ v, v ∈ p.support := by
  classical
  let path : ∀ a b : V, H.Walk a b := fun a b =>
    Classical.choose (FiniteAcyclicPathExtraction.exists_path_of_connected_acyclic
      H hconn hacyc a b)
  have hpath : ∀ a b, (path a b).IsPath := by
    intro a b
    exact Classical.choose_spec
      (FiniteAcyclicPathExtraction.exists_path_of_connected_acyclic
        H hconn hacyc a b)
  let base : V := Classical.choice hconn.nonempty
  obtain ⟨ab, hab, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V × V)) (fun ab => (path ab.1 ab.2).length)
    ⟨(base, base), by simp⟩
  let a := ab.1
  let b := ab.2
  let p := path a b
  have hp : p.IsPath := hpath a b
  refine ⟨a, b, p, hp, ?_⟩
  intro v
  by_contra hvnot
  let S : Set V := {x | x ∉ p.support}
  have hS : S.Nonempty := ⟨v, hvnot⟩
  have hSproper : S ≠ Set.univ := by
    intro heq
    have : a ∈ S := by rw [heq]; simp
    exact this (Walk.start_mem_support p)
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    Erdos1016.Proof.ConnectedRegionBoundary.Connected.exists_adj_boundary
      hconn hS hSproper
  have hxout : x ∉ p.support := by simpa [S] using hx
  have hyin : y ∈ p.support := by simpa [S] using hy
  by_cases hya : y = a
  · subst y
    have hq : (Walk.cons hxy p).IsPath :=
      (Walk.cons_isPath_iff hxy p).2 ⟨hp, hxout⟩
    have huniq := FiniteAcyclicPathExtraction.existsUnique_path_of_connected_acyclic
      H hconn hacyc x b
    have heq : path x b = Walk.cons hxy p := huniq.unique (hpath x b) hq
    have hle := hmax (x, b) (by simp)
    rw [heq] at hle
    have hlen : p.length + 1 ≤ p.length := by
      simpa [Walk.length_cons, p, a, b] using hle
    omega
  · by_cases hyb : y = b
    · subst y
      have hq : (Walk.cons hxy p.reverse).IsPath :=
        (Walk.cons_isPath_iff hxy p.reverse).2
          ⟨hp.reverse, by simpa using hxout⟩
      have huniq := FiniteAcyclicPathExtraction.existsUnique_path_of_connected_acyclic
        H hconn hacyc x a
      have heq : path x a = Walk.cons hxy p.reverse :=
        huniq.unique (hpath x a) hq
      have hle := hmax (x, a) (by simp)
      rw [heq] at hle
      have hlen : p.length + 1 ≤ p.length := by
        simpa [Walk.length_cons, Walk.length_reverse, p, a, b] using hle
      omega
    · obtain ⟨u, w, huw, hyu, hyw, huin, hwin⟩ :=
        exists_two_path_neighbors_of_mem_support_of_ne_endpoints hp hyin hya hyb
      have hxmem : x ∈ H.neighborFinset y := by
        simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
      have humem : u ∈ H.neighborFinset y := by
        simpa [SimpleGraph.mem_neighborFinset] using hyu
      have hwmem : w ∈ H.neighborFinset y := by
        simpa [SimpleGraph.mem_neighborFinset] using hyw
      have hxu : x ≠ u := by
        intro h
        subst u
        exact hxout huin
      have hxw : x ≠ w := by
        intro h
        subst w
        exact hxout hwin
      have htriple : ({x, u, w} : Finset V).card = 3 := by
        simp [huw, hxu, hxw]
      have hsub : ({x, u, w} : Finset V) ⊆ H.neighborFinset y := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hxmem
        · exact humem
        · exact hwmem
      have hthree : 3 ≤ (H.neighborFinset y).card := by
        rw [← htriple]
        exact Finset.card_le_card hsub
      have hdeg := hdegree y
      omega

end Erdos1016.Proof.FiniteTreeDegreeTwoPath

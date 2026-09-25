import Erdos1016.Probability.Moments.CompatibleTupleMoments
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators





local instance conditionalCycleFactorizationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p





























/-- The literal short-external-return exclusion localized to a region R:
there is no path inside R joining two distinct vertices of C, with one
attachment edge at each end, whose total length is at most q. This is the
geometric predicate needed for the small-component contact step. -/
def NoShortExternalReturnThrough (G : PhysicalGraph)
    (R C : Finset G.Vertex) (q : ℕ) : Prop :=
  ∀ (r s u v : G.Vertex) (hr : r ∈ R) (hs : s ∈ R)
    (hu : u ∈ C) (hv : v ∈ C), u ≠ v →
    G.toSimpleGraph.Adj r u → G.toSimpleGraph.Adj s v →
    ∀ p : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Walk
      ⟨r, hr⟩ ⟨s, hs⟩, p.IsPath → q < p.length + 2





private theorem crossing_edge_endpoints
    {G : PhysicalGraph} (R C : Finset G.Vertex) (e : G.Edge)
    (he : e ∈ Erdos1016.SafeCore.crossing G R C) :
    ∃ r u, r ∈ R ∧ u ∈ C ∧ G.toSimpleGraph.Adj r u ∧
      ((G.src e = r ∧ G.dst e = u) ∨ (G.src e = u ∧ G.dst e = r)) := by
  rcases (Erdos1016.SafeCore.mem_crossing G R C e).mp he with
    ⟨hsR, hdC⟩ | ⟨hsC, hdR⟩
  · exact ⟨G.src e, G.dst e, hsR, hdC,
      ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨G.dst e, G.src e, hdR, hsC,
      ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- The one-contact theorem for an actual cubic `CycleWord`: the spare
incidence argument supplies the distinct-endpoint premise, and the localized
short-return exclusion then rules out two different crossing edges. -/
theorem cubic_cycle_contact_edges_unique_of_no_short_external_return
    {G : PhysicalGraph} (R : Finset G.Vertex) (C : G.CycleWord) (q : ℕ)
    (hR : Erdos1016.SafeCore.ConnectedRegion G R)
    (hsize : R.card + 1 ≤ q)
    (hdisj : Disjoint R (Erdos1016.BoundaryDecay.Cycle.vertices C))
    (hregular : ∀ v ∈ Erdos1016.BoundaryDecay.Cycle.vertices C,
      G.degree v = 3)
    (hNoReturn : NoShortExternalReturnThrough G R
      (Erdos1016.BoundaryDecay.Cycle.vertices C) q) :
    ∀ e d, e ∈ Erdos1016.SafeCore.crossing G R
        (Erdos1016.BoundaryDecay.Cycle.vertices C) →
      d ∈ Erdos1016.SafeCore.crossing G R
        (Erdos1016.BoundaryDecay.Cycle.vertices C) → e = d := by
  intro e d he hd
  by_contra hne
  obtain ⟨r, u, hr, hu, hru, hendsE⟩ := crossing_edge_endpoints R
    (Erdos1016.BoundaryDecay.Cycle.vertices C) e he
  obtain ⟨s, v, hs, hv, hsv, hendsD⟩ := crossing_edge_endpoints R
    (Erdos1016.BoundaryDecay.Cycle.vertices C) d hd
  have huv : u ≠ v := by
    by_contra huv
    subst v
    have hrnot : r ∉ Erdos1016.BoundaryDecay.Cycle.vertices C :=
      fun hrC => (Finset.disjoint_left.mp hdisj) hr hrC
    have hsnot : s ∉ Erdos1016.BoundaryDecay.Cycle.vertices C :=
      fun hsC => (Finset.disjoint_left.mp hdisj) hs hsC
    have hecut : e ∈ G.traceCutEdgesAt
        (Erdos1016.BoundaryDecay.Cycle.vertices C) u := by
      unfold Erdos1016.PhysicalGraph.traceCutEdgesAt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Erdos1016.PhysicalGraph.incident]
      rcases hendsE with h | h
      · exact ⟨Or.inr h.2, Or.inr ⟨by simpa [h.1] using hrnot,
          by simpa [h.2] using hu⟩⟩
      · exact ⟨Or.inl h.1, Or.inl ⟨by simpa [h.1] using hu,
          by simpa [h.2] using hrnot⟩⟩
    have hdcut : d ∈ G.traceCutEdgesAt
        (Erdos1016.BoundaryDecay.Cycle.vertices C) u := by
      unfold Erdos1016.PhysicalGraph.traceCutEdgesAt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Erdos1016.PhysicalGraph.incident]
      rcases hendsD with h | h
      · exact ⟨Or.inr h.2, Or.inr ⟨by simpa [h.1] using hsnot,
          by simpa [h.2] using hu⟩⟩
      · exact ⟨Or.inl h.1, Or.inl ⟨by simpa [h.1] using hu,
          by simpa [h.2] using hsnot⟩⟩
    have hinside : 2 ≤ G.traceInsideDegree
        (Erdos1016.BoundaryDecay.Cycle.vertices C) u := by
      have hsel : G.selectedDegree C.1 u = 2 := C.2.2.2.2 u hu
      have hsub : Finset.univ.filter
          (fun f : G.Edge => C.1 f ≠ 0 ∧ G.incident f u) ⊆
          G.traceInsideEdgesAt (Erdos1016.BoundaryDecay.Cycle.vertices C) u := by
        intro f hf
        rcases Finset.mem_filter.mp hf with ⟨_, hneF, hinc⟩
        have hsrc := Erdos1016.BoundaryDecay.src_mem_used_of_ne_zero C.1 f hneF
        have hdst := Erdos1016.BoundaryDecay.dst_mem_used_of_ne_zero C.1 f hneF
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc, hsrc, hdst⟩
      have hcard : G.selectedDegree C.1 u =
          (Finset.univ.filter
            (fun f : G.Edge => C.1 f ≠ 0 ∧ G.incident f u)).card := rfl
      calc
        2 = G.selectedDegree C.1 u := hsel.symm
        _ = (Finset.univ.filter
            (fun f : G.Edge => C.1 f ≠ 0 ∧ G.incident f u)).card := hcard
        _ ≤ (G.traceInsideEdgesAt
            (Erdos1016.BoundaryDecay.Cycle.vertices C) u).card :=
          Finset.card_le_card hsub
    have hcut := G.traceCutDegree_le_one
      (Erdos1016.BoundaryDecay.Cycle.vertices C) u hu
      (hregular u hu) hinside
    exact hne ((Finset.card_le_one.mp hcut) e hecut d hdcut)
  have hconn :
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected := by
    exact (Erdos1016.SafeCore.connectedRegion_iff_induce_connected G _).mp hR
  obtain ⟨p, hp, _⟩ := hconn.exists_path_of_dist ⟨r, hr⟩ ⟨s, hs⟩
  have hpLen : p.length < R.card := by simpa using hp.length_lt
  have hreturn := hNoReturn r s u v hr hs hu hv huv hru hsv p hp
  have hupper : p.length + 2 ≤ q := by omega
  omega























/-- A finite family of compatible forced-region cylinders is one cylinder on
the union. The seed-zero condition says each region's prescribed word vanishes
on incidences belonging to every other region. -/
theorem forcedRegion_biUnion_iff
    {G : PhysicalGraph} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset ι) (S : ι → Finset G.Vertex) (z : ι → G.CycleSpace)
    (x : G.CycleSpace)
    (hzero : ∀ i ∈ F, ∀ k ∈ F, k ≠ i → ∀ e,
      G.src e ∈ S i ∨ G.dst e ∈ S i → (z k).1 e = 0) :
    (∀ i ∈ F, Erdos1016.BoundaryDecay.ForcedRegion G.traceNetwork (S i)
      (z i).1 x.1) ↔
      Erdos1016.BoundaryDecay.ForcedRegion G.traceNetwork
        (F.biUnion S) (∑ i ∈ F, z i).1 x.1 := by
  constructor
  · intro hAll e he
    change G.src e ∈ F.biUnion S ∨ G.dst e ∈ F.biUnion S at he
    rcases he with hs | hd
    · rcases Finset.mem_biUnion.mp hs with ⟨i, hi, his⟩
      have hsum : (∑ k ∈ F, (z k).1 e) = (z i).1 e := by
        rw [Finset.sum_eq_single i]
        · intro k hk hki
          exact hzero i hi k hk hki e (Or.inl his)
        · intro hnot
          exact (hnot hi).elim
      have hword : (∑ k ∈ F, z k).1 e = ∑ k ∈ F, (z k).1 e := by simp
      change x.1 e = (∑ k ∈ F, z k).1 e
      rw [hword, hsum]
      exact hAll i hi e (Or.inl his)
    · rcases Finset.mem_biUnion.mp hd with ⟨i, hi, hid⟩
      have hsum : (∑ k ∈ F, (z k).1 e) = (z i).1 e := by
        rw [Finset.sum_eq_single i]
        · intro k hk hki
          exact hzero i hi k hk hki e (Or.inr hid)
        · intro hnot
          exact (hnot hi).elim
      have hword : (∑ k ∈ F, z k).1 e = ∑ k ∈ F, (z k).1 e := by simp
      change x.1 e = (∑ k ∈ F, z k).1 e
      rw [hword, hsum]
      exact hAll i hi e (Or.inr hid)
  · intro hUnion i hi e he
    have hsum : (∑ k ∈ F, (z k).1 e) = (z i).1 e := by
      rw [Finset.sum_eq_single i]
      · intro k hk hki
        exact hzero i hi k hk hki e he
      · intro hnot
        exact (hnot hi).elim
    have h := hUnion e (by
      change G.src e ∈ F.biUnion S ∨ G.dst e ∈ F.biUnion S
      rcases he with hs | hd
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, hd⟩))
    have hword : (∑ k ∈ F, z k).1 e = ∑ k ∈ F, (z k).1 e := by simp
    change x.1 e = (∑ k ∈ F, z k).1 e at h
    rw [hword, hsum] at h
    exact h








end Erdos1016.Proof.ConditionalMoments

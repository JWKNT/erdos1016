import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximumSupport.NetworkParallel
import Erdos1016.ExactMaximumSupport.PoleCyclePacking
import Erdos1016.ExactMaximumSupport.NetworkExteriorRank
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingRegionRank

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Parallel vertices outside a path

In a subcubic network, a vertex has at most one parallel neighbor.
Disjoint parallel pairs supply independent actual cycles in the induced exterior.
The path degree conditions keep each exterior parallel pair entirely outside the path.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.PoleParallelCount
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph
open LargeGirth

local instance poleParallelCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
private theorem other_endpoint_eq {e : E} {v w z : V}
    (h : N.Joins e v w) (h' : N.Joins e v z) : w = z := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    rcases h' with ⟨h3,h4⟩ | ⟨h3,h4⟩
  · exact h2.symm.trans h4
  · exact h2.symm.trans (h4.trans (h1.symm.trans h3))
  · exact h1.symm.trans (h3.trans (h2.symm.trans h4))
  · exact h1.symm.trans h3

omit [Fintype V] in
/-- Two parallel neighbors would require four physical labels at one vertex. -/
theorem parallel_neighbor_unique {v w z : V} {e f g h : E}
    (hdeg : N.deg (fun _ => 1) v ≤ 3)
    (hef : e ≠ f) (he : N.Joins e v w) (hf : N.Joins f v w)
    (hgh : g ≠ h) (hg : N.Joins g v z) (hh : N.Joins h v z) : w = z := by
  classical
  by_contra hwz
  have heg : e ≠ g := by intro h; subst g; exact hwz (other_endpoint_eq N he hg)
  have heh : e ≠ h := by intro h'; subst h; exact hwz (other_endpoint_eq N he hh)
  have hfg : f ≠ g := by intro h; subst g; exact hwz (other_endpoint_eq N hf hg)
  have hfh : f ≠ h := by intro h'; subst h; exact hwz (other_endpoint_eq N hf hh)
  have hs : ({e,f,g,h} : Finset E) ⊆
      Finset.univ.filter (fun a => (1 : Bit) ≠ 0 ∧ (N.src a = v ∨ N.dst a = v)) := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,he.at_left⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,hf.at_left⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,hg.at_left⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,hh.at_left⟩
  have hc := Finset.card_le_card hs
  have hfour : ({e,f,g,h} : Finset E).card = 4 := by
    simp [hef,heg,heh,hfg,hfh,hgh]
  change ({e,f,g,h} : Finset E).card ≤ N.deg (fun _ => 1) v at hc
  omega

private def IsPair (R : Finset V) : Prop :=
  ∃ v w : V, ∃ e f : E, R = {v,w} ∧ e ≠ f ∧ N.Joins e v w ∧ N.Joins f v w

omit [Fintype V] [Fintype E] in
private theorem pair_at {R : Finset V} (hR : IsPair N R) {v : V} (hv : v ∈ R) :
    ∃ w : V, ∃ e f : E, R = {v,w} ∧ e ≠ f ∧ N.Joins e v w ∧ N.Joins f v w := by
  classical
  obtain ⟨a,b,e,f,rfl,hef,he,hf⟩ := hR
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨b,e,f,rfl,hef,he,hf⟩
  · exact ⟨a,e,f,Finset.pair_comm _ _,hef,he.symm,hf.symm⟩

omit [Fintype V] in
private theorem pairs_disjoint (hdeg : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    {R S : Finset V} (hR : IsPair N R) (hS : IsPair N S) (hne : R ≠ S) :
    Disjoint R S := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨w,e,f,hRw,hef,he,hf⟩ := pair_at N hR hv
  obtain ⟨z,g,h,hSz,hgh,hg,hh⟩ := pair_at N hS hv'
  have hwz := parallel_neighbor_unique N (hdeg v) hef he hf hgh hg hh
  exact hne (by rw [hRw,hSz,hwz])

private def pairs (X : Finset V) : Finset (Finset V) :=
  X.powerset.filter (IsPair N)

omit [Fintype V] [Fintype E] in
private theorem mem_pairs (X R : Finset V) :
    R ∈ pairs N X ↔ R ⊆ X ∧ IsPair N R := by simp [pairs]

omit [Fintype V] [Fintype E] in
private theorem pair_card {R : Finset V} (hR : IsPair N R) : R.card = 2 := by
  classical
  obtain ⟨v,w,e,f,rfl,_,he,_⟩ := hR
  simp [he.ne]

private theorem pair_cyclic {R : Finset V} (hR : IsPair N R) :
    ∃ z : (NetworkMultigraph.graph N).internalCycleSpace
      (R.image (NetworkMultigraph.vertices N)), z ≠ 0 := by
  classical
  obtain ⟨v,w,e,f,rfl,hef,he,hf⟩ := hR
  obtain ⟨z,hz,_,hsupport⟩ := NetworkParallel.exists_cycle_of_parallel N hef he hf
  let G := NetworkMultigraph.graph N
  let x := NetworkMultigraph.wordEquiv N z
  have hx : G.IsCycleWord x := PoleCyclePacking.cycle_wordEquiv N z hz
  have hsub : CycleRegions.region G x ⊆ ({v,w} : Finset V).image (NetworkMultigraph.vertices N) := by
    intro a ha
    obtain ⟨b,rfl⟩ := (NetworkMultigraph.vertices N).surjective a
    have hp : 0 < N.deg z b := (PoleCyclePacking.region_wordEquiv N z b).mp ha
    rcases hsupport b hp with rfl | rfl <;> simp
  obtain ⟨q,hq⟩ := CycleRegions.cycle_region_cyclic G x hx
  refine ⟨⟨q.1,PackingRegionRank.internalCycleSpace_mono G hsub q.2⟩,?_⟩
  intro hzero
  apply hq
  apply Subtype.ext
  have hv := congrArg (fun z : G.internalCycleSpace
    (({v,w} : Finset V).image (NetworkMultigraph.vertices N)) => z.1) hzero
  exact hv

/-- Parallel vertices in a closed region cost at least one rank per pair. -/
theorem card_parallel_le_twice_induced_rank (X : Finset V)
    (hdeg : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hclosed : ∀ v ∈ X, ∀ e f w, e ≠ f →
      N.Joins e v w → N.Joins f v w → w ∈ X) :
    (X.filter N.OnParallel).card ≤ 2 * networkRank (N.induce (fun v => v ∈ X)) := by
  classical
  let F := pairs N X
  have hcover : X.filter N.OnParallel ⊆ F.biUnion id := by
    intro v hv
    obtain ⟨hvX,e,f,w,hef,he,hf⟩ := Finset.mem_filter.mp hv
    have hwX := hclosed v hvX e f w hef he hf
    refine Finset.mem_biUnion.mpr ⟨{v,w},?_,by simp⟩
    apply (mem_pairs N X _).mpr
    refine ⟨?_,⟨v,w,e,f,rfl,hef,he,hf⟩⟩
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hvX
    · exact hwX
  have hcount : (X.filter N.OnParallel).card ≤ 2 * F.card := by
    calc
      _ ≤ (F.biUnion id).card := Finset.card_le_card hcover
      _ ≤ ∑ R ∈ F, R.card := Finset.card_biUnion_le
      _ = 2 * F.card := by
        have hsum : ∑ R ∈ F, R.card = ∑ _R ∈ F, 2 := by
          apply Finset.sum_congr rfl
          intro R hR
          exact pair_card N ((mem_pairs N X R).mp hR).2
        rw [hsum]
        simp [Nat.mul_comm]
  let G := NetworkMultigraph.graph N
  let Y := X.image (NetworkMultigraph.vertices N)
  let U (i : F) := i.1.image (NetworkMultigraph.vertices N)
  have hUX : ∀ i : F, U i ⊆ Y := by
    intro i
    exact Finset.image_subset_image ((mem_pairs N X i.1).mp i.2).1
  have hdisj : Pairwise (fun i j : F => Disjoint (U i) (U j)) := by
    intro i j hij
    have hd := pairs_disjoint N hdeg ((mem_pairs N X i.1).mp i.2).2
      ((mem_pairs N X j.1).mp j.2).2 (fun h => hij (Subtype.ext h))
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp ha
    obtain ⟨w,hw,hwa⟩ := Finset.mem_image.mp hb
    have hvw := (NetworkMultigraph.vertices N).injective (hva.trans hwa.symm)
    subst w
    exact Finset.disjoint_left.mp hd hv hw
  have hc := PackingRegionRank.card_le_induced_cycleRank G Y U hUX hdisj
    (fun i => pair_cyclic N ((mem_pairs N X i.1).mp i.2).2)
  have hr : networkRank (N.induce (fun v => v ∈ X)) =
      (PieceCore.Induced.graph G Y).cycleRank := by
    apply NetworkExteriorRank.rank_induce_eq N (fun v => v ∈ X) Y
    intro v
    simp [Y]
  have hrank : F.card ≤ networkRank (N.induce (fun v => v ∈ X)) := by
    rw [hr]
    simpa only [Fintype.card_coe] using hc
  exact hcount.trans (Nat.mul_le_mul_left 2 hrank)

omit [Fintype V] in
private theorem degree_add_two_le (A : N.Word) {v : V} {e f : E}
    (hef : e ≠ f) (he : N.src e = v ∨ N.dst e = v)
    (hf : N.src f = v ∨ N.dst f = v) (hAe : A e = 0) (hAf : A f = 0) :
    N.deg A v + 2 ≤ N.deg (fun _ => 1) v := by
  classical
  let S := Finset.univ.filter fun a : E => A a ≠ 0 ∧ (N.src a = v ∨ N.dst a = v)
  have heS : e ∉ S := by simp [S,hAe]
  have hfS : f ∉ insert e S := by simp [S,hAf,Ne.symm hef]
  have hs : insert f (insert e S) ⊆ Finset.univ.filter
      (fun a => (1 : Bit) ≠ 0 ∧ (N.src a = v ∨ N.dst a = v)) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,hf⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,he⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,one_ne_zero,
        (Finset.mem_filter.mp ha).2.2⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_not_mem hfS,Finset.card_insert_of_not_mem heS] at hc
  change N.deg A v + 1 + 1 ≤ N.deg (fun _ => 1) v at hc
  omega

omit [Fintype V] in
/-- A parallel pair meeting the path exterior has both endpoints in that exterior. -/
theorem parallel_stays_off_path {s t : V} {A : N.Word}
    (hA : N.IsPathWord s t A)
    (hs : N.deg (fun _ => 1) s ≤ 2) (ht : N.deg (fun _ => 1) t ≤ 2)
    (hdeg : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    {v w : V} {e f : E} (hv : N.deg A v = 0)
    (hef : e ≠ f) (he : N.Joins e v w) (hf : N.Joins f v w) :
    N.deg A w = 0 := by
  have hAe := N.eq_zero_of_deg_eq_zero hv he.at_left
  have hAf := N.eq_zero_of_deg_eq_zero hv hf.at_left
  have hc := degree_add_two_le N A hef he.at_right hf.at_right hAe hAf
  by_cases hws : w = s
  · subst w
    have ha := hA.2.1
    omega
  by_cases hwt : w = t
  · subst w
    have ha := hA.2.2.1
    omega
  rcases hA.2.2.2.1 w hws hwt with hzero | htwo
  · exact hzero
  · have hd := hdeg w
    omega

/-- Count the actual parallel vertices outside the designated path by exterior rank. -/
theorem card_parallel_outside_le_twice_rank {s t : V} (A : N.Word)
    (hA : N.IsPathWord s t A)
    (hs : N.deg (fun _ => 1) s ≤ 2) (ht : N.deg (fun _ => 1) t ≤ 2)
    (hdeg : ∀ v, N.deg (fun _ => 1) v ≤ 3) :
    (Finset.univ.filter fun v : V => N.deg A v = 0 ∧ N.OnParallel v).card ≤
      2 * networkRank (N.sub (fun e =>
        N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0)) := by
  classical
  let X := Finset.univ.filter fun v : V => N.deg A v = 0
  have hclosed : ∀ v ∈ X, ∀ e f w, e ≠ f →
      N.Joins e v w → N.Joins f v w → w ∈ X := by
    intro v hv e f w hef he hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      parallel_stays_off_path N hA hs ht hdeg (Finset.mem_filter.mp hv).2 hef he hf⟩
  have hc := card_parallel_le_twice_induced_rank N X hdeg hclosed
  have hr : networkRank (N.induce (fun v => v ∈ X)) =
      networkRank (N.sub (fun e =>
        N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0)) := by
    rw [N.networkRank_induce]
    apply N.networkRank_sub_congr
    funext e
    apply propext
    simp [Network.inside,X]
  rw [hr] at hc
  simpa [X,Finset.filter_filter] using hc

end Erdos1016.ExactMaximumSupport.PoleParallelCount

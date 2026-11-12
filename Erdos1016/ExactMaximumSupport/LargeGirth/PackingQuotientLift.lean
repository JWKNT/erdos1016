import Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
import Erdos1016.ExactMaximumSupport.LargeGirth.BlockGeometry

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Connected quotient intervals lift to actual small-boundary regions. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
open FiniteMultiGraph ConnectedContraction
local instance packingLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι → Finset G.Vertex)

def lift (M : Finset (graph G X).Vertex) : Finset G.Vertex :=
  Finset.univ.filter fun v => vertex G X v∈M

@[simp] theorem mem_lift (M : Finset (graph G X).Vertex) (v : G.Vertex) :
    v∈lift G X M ↔ vertex G X v∈M := by simp [lift]

theorem lift_disjoint {M N : Finset (graph G X).Vertex} (h : Disjoint M N) :
    Disjoint (lift G X M) (lift G X N) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.disjoint_left.mp h) ((mem_lift G X M v).mp hv) ((mem_lift G X N v).mp hw)

theorem selected_subset_lift (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (M : Finset (graph G X).Vertex) (i : ι) (hi : mark G X i∈M) : X i⊆lift G X M := by
  intro v hv
  rw [mem_lift,(vertex_eq_mark_iff G X hdisj v i).mpr hv]
  exact hi

def representative (hFib : ConnectedFibers G (label G X)) (q : (graph G X).Vertex) : G.Vertex :=
  (fiberRoot G (label G X) hFib (vertexEquiv.symm q)).1

@[simp] theorem vertex_representative (hFib : ConnectedFibers G (label G X))
    (q : (graph G X).Vertex) : vertex G X (representative G X hFib q)=q := by
  unfold vertex representative
  rw [(fiberRoot G (label G X) hFib (vertexEquiv.symm q)).2]
  exact vertexEquiv.apply_symm_apply q

theorem fiber_reachable_in_lift (hFib : ConnectedFibers G (label G X))
    (M : Finset (graph G X).Vertex) (a b : G.Vertex)
    (ha : a∈lift G X M) (hb : b∈lift G X M)
    (hab : vertex G X a=vertex G X b) :
    (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
  have hl : label G X b=label G X a := vertexEquiv.injective hab.symm
  let f : G.toSimpleGraph.induce {v | label G X v=label G X a} →g
      G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex) :=
    { toFun := fun u => ⟨u.1,by
        change u.1∈lift G X M
        rw [mem_lift]
        change vertexEquiv (label G X u.1)∈M
        rw [u.2]
        exact (mem_lift G X M a).mp ha⟩
      map_rel' := fun h => h }
  exact ((hFib (label G X a)).preconnected ⟨a,rfl⟩ ⟨b,hl⟩).map f

theorem adjacent_fibers_reachable_in_lift (hFib : ConnectedFibers G (label G X))
    (M : Finset (graph G X).Vertex) (a b : G.Vertex)
    (ha : a∈lift G X M) (hb : b∈lift G X M)
    (hab : (graph G X).toSimpleGraph.Adj (vertex G X a) (vertex G X b)) :
    (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
  have step (a b : G.Vertex) (ha : a∈lift G X M) (hb : b∈lift G X M)
      (e : CrossingEdge G (label G X))
      (hs : vertex G X (G.src e.1)=vertex G X a)
      (ht : vertex G X (G.dst e.1)=vertex G X b) :
      (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
    have hsm : G.src e.1∈lift G X M := by rw [mem_lift,hs]; exact (mem_lift G X M a).mp ha
    have htm : G.dst e.1∈lift G X M := by rw [mem_lift,ht]; exact (mem_lift G X M b).mp hb
    have hne : G.src e.1≠G.dst e.1 := fun h => e.2 (congrArg (label G X) h)
    have he : (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Adj
        ⟨G.src e.1,hsm⟩ ⟨G.dst e.1,htm⟩ := ⟨hne,e.1,Or.inl ⟨rfl,rfl⟩⟩
    exact (fiber_reachable_in_lift G X hFib M a _ ha hsm hs.symm).trans
      (he.reachable.trans (fiber_reachable_in_lift G X hFib M _ b htm hb ht))
  obtain ⟨_,e,he | he⟩ := hab
  · exact step a b ha hb ((edgeEquiv G (label G X)).symm e) he.1 he.2
  · exact (step b a hb ha ((edgeEquiv G (label G X)).symm e) he.1 he.2).symm

/-- An interval's connectedness lifts through the actual connected fibers. -/
theorem lift_connected (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected)
    (M : Finset (graph G X).Vertex)
    (hM : ((graph G X).toSimpleGraph.induce (↑M:Set (graph G X).Vertex)).Connected) :
    (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Connected := by
  let hFib := connectedFibers G X hdisj hconn
  have hw : ∀ {q r : {q : (graph G X).Vertex // q∈M}},
      (((graph G X).toSimpleGraph.induce (↑M:Set (graph G X).Vertex)).Walk q r) →
      ∀ (a b : G.Vertex) (ha : a∈lift G X M) (hb : b∈lift G X M),
      vertex G X a=q.1 → vertex G X b=r.1 →
      (G.toSimpleGraph.induce (↑(lift G X M):Set G.Vertex)).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
    intro q r p
    induction p with
    | nil =>
        intro a b ha hb hqa hqb
        exact fiber_reachable_in_lift G X hFib M a b ha hb (hqa.trans hqb.symm)
    | @cons q s r hqs p ih =>
        intro a b ha hb hqa hrb
        let c := representative G X hFib s.1
        have hc : c∈lift G X M := by simp [c,s.2]
        have hcs : vertex G X c=s.1 := vertex_representative G X hFib s.1
        have hac : (graph G X).toSimpleGraph.Adj (vertex G X a) (vertex G X c) := by
          rw [hqa,hcs]
          exact hqs
        exact (adjacent_fibers_reachable_in_lift G X hFib M a c ha hc hac).trans
          (ih c b hc hb hcs hrb)
  letI : Nonempty {v : G.Vertex // v∈(↑(lift G X M):Set G.Vertex)} := by
    obtain ⟨q⟩ := hM.nonempty
    exact ⟨⟨representative G X hFib q.1,by simp [q.2]⟩⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨p⟩ := hM.preconnected ⟨vertex G X a.1,(mem_lift G X M a.1).mp a.2⟩
    ⟨vertex G X b.1,(mem_lift G X M b.1).mp b.2⟩
  exact hw p a.1 b.1 a.2 b.2 rfl rfl

/-- Quotient boundary endpoints give an inclusion of actual physical cuts. -/
theorem lift_cut_subset (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (M : Finset (graph G X).Vertex) (i j : ι)
    (hi : mark G X i∉M) (hj : mark G X j∉M)
    (hbd : ∀u∈M,∀w,(graph G X).toSimpleGraph.Adj u w → w∉M →
      w=mark G X i ∨ w=mark G X j) :
    G.cutEdges (lift G X M)⊆G.cutEdges (X i)∪G.cutEdges (X j) := by
  have step {a b : G.Vertex} (ha : a∈lift G X M) (hb : b∉lift G X M)
      (hab : G.toSimpleGraph.Adj a b) :
      (a∉X i ∧ a∉X j) ∧ (b∈X i ∨ b∈X j) := by
    have hia : a∉X i := fun h => hi ((vertex_eq_mark_iff G X hdisj a i).mpr h ▸
      (mem_lift G X M a).mp ha)
    have hja : a∉X j := fun h => hj ((vertex_eq_mark_iff G X hdisj a j).mpr h ▸
      (mem_lift G X M a).mp ha)
    have hvb : vertex G X b∉M := fun h => hb ((mem_lift G X M b).mpr h)
    have hne : label G X a≠label G X b := by
      intro h
      have hh : vertex G X a=vertex G X b := congrArg vertexEquiv h
      exact hvb (hh ▸ (mem_lift G X M a).mp ha)
    obtain ⟨_,e,he | he⟩ := hab
    all_goals
      have hcross : label G X (G.src e)≠label G X (G.dst e) := by
        simp only [he.1,he.2]
        first | exact hne | exact hne.symm
      have hq : (graph G X).toSimpleGraph.Adj (vertex G X a) (vertex G X b) := by
        refine ⟨fun h => hne (vertexEquiv.injective h),edgeEquiv G (label G X) ⟨e,hcross⟩,?_⟩
        simp only [graph,quotient,Equiv.symm_apply_apply,he.1,he.2,vertex]
        tauto
      have hh := hbd _ ((mem_lift G X M a).mp ha) _ hq hvb
      exact ⟨⟨hia,hja⟩,hh.imp ((vertex_eq_mark_iff G X hdisj b i).mp)
        ((vertex_eq_mark_iff G X hdisj b j).mp)⟩
  intro e he
  have hc := (Finset.mem_filter.mp he).2
  rcases hc with hc | hc
  · have hn : G.src e≠G.dst e := fun h => hc.2 (h ▸ hc.1)
    have hh := step hc.1 hc.2 ⟨hn,e,Or.inl ⟨rfl,rfl⟩⟩
    simp only [cutEdges,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  · have hn : G.dst e≠G.src e := fun h => hc.1 (h ▸ hc.2)
    have hh := step hc.2 hc.1 ⟨hn,e,Or.inr ⟨rfl,rfl⟩⟩
    simp only [cutEdges,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto

theorem lift_cut_card_le (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (M : Finset (graph G X).Vertex) (i j : ι)
    (hi : mark G X i∉M) (hj : mark G X j∉M)
    (hbd : ∀u∈M,∀w,(graph G X).toSimpleGraph.Adj u w → w∉M →
      w=mark G X i ∨ w=mark G X j) (d : ℕ)
    (hdi : (G.cutEdges (X i)).card≤d) (hdj : (G.cutEdges (X j)).card≤d) :
    (G.cutEdges (lift G X M)).card≤2*d := by
  exact (Finset.card_le_card (lift_cut_subset G X hdisj M i j hi hj hbd)).trans
    ((Finset.card_union_le _ _).trans (by omega))

/-- A lifted interval avoids every selected region whose mark it omits. -/
theorem lift_disjoint_selected (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (M : Finset (graph G X).Vertex) (i : ι) (hi : mark G X i∉M) :
    Disjoint (lift G X M) (X i) := by
  apply Finset.disjoint_left.mpr
  intro v hv hi'
  have he := (vertex_eq_mark_iff G X hdisj v i).mpr hi'
  exact hi (he ▸ (mem_lift G X M v).mp hv)

/-- A connected exterior marker consumes at most one disjoint interval. -/
theorem marker_bad_card_le_one {κ : Type*} [DecidableEq κ]
    (F : Finset κ) (M : κ → Finset (graph G X).Vertex)
    (hdisj : ∀i∈F,∀j∈F,i≠j → Disjoint (M i) (M j))
    (P : Finset G.Vertex)
    (hP : (G.toSimpleGraph.induce (↑P:Set G.Vertex)).Connected)
    (hPX : ∀i,Disjoint P (X i)) :
    (F.filter fun i => ¬ Disjoint (lift G X (M i)) P).card≤1 := by
  obtain ⟨c,hc⟩ := marker_single_fiber G X P hP hPX
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hne
  obtain ⟨u,huM,huP⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
  obtain ⟨w,hwM,hwP⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hj).2
  have hu : vertexEquiv (Sum.inr c : Label G X)∈M i := by
    have h := (mem_lift G X (M i) u).mp huM
    change vertexEquiv (label G X u)∈M i at h
    rwa [hc u huP] at h
  have hw : vertexEquiv (Sum.inr c : Label G X)∈M j := by
    have h := (mem_lift G X (M j) w).mp hwM
    change vertexEquiv (label G X w)∈M j at h
    rwa [hc w hwP] at h
  exact (Finset.disjoint_left.mp (hdisj i (Finset.mem_filter.mp hi).1
    j (Finset.mem_filter.mp hj).1 hne)) hu hw

/-- Deleting an additional vertex set discards at most its cardinality. -/
theorem deleted_bad_card_le {κ : Type*} [DecidableEq κ]
    (F : Finset κ) (M : κ → Finset (graph G X).Vertex)
    (hdisj : ∀i∈F,∀j∈F,i≠j → Disjoint (M i) (M j)) (S : Finset G.Vertex) :
    (F.filter fun i => ¬ Disjoint (lift G X (M i)) S).card≤S.card := by
  exact bad_blocks_card_le F (fun i => lift G X (M i)) S
    (fun i hi j hj hne => lift_disjoint G X (hdisj i hi j hj hne))

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient

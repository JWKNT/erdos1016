import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringsThreads
import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringsIntervals
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Ordered terminal strings with actual interval regions

The input consists of terminal feet and a relevant set. The geometric
premise explicitly requires two terminal-containing branches at each
relevant nonfoot. The conclusion constructs every region in the original
graph, rather than only in an auxiliary spanning forest.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
open SimpleGraph ExceptionalPartners
variable {V : Type*} [Fintype V]
local instance decidableAssembly (p : Prop) : Decidable p := Classical.propDecidable p

/-- One ordered string and its actual interval regions. -/
structure OrderedString (G : SimpleGraph V) (B R : Finset V) where
  length : ℕ
  vertex : Fin length → V
  injective : Function.Injective vertex
  relevant : ∀i,vertex i∈R
  region : (i j : Fin length) → i.val+2≤j.val → Finset V
  connected : ∀i j h,(G.induce (↑(region i j h) : Set V)).Connected
  no_feet : ∀i j h,Disjoint (region i j h) B
  avoids : ∀i j h,vertex i∉region i j h ∧ vertex j∉region i j h
  between : ∀i j h k,i<k→k<j→vertex k∈region i j h
  boundary : ∀i j h u,u∈region i j h→∀w,G.Adj u w→w∉region i j h→
    w=vertex i ∨ w=vertex j
  disjoint : ∀i j h k l h',j≤k→Disjoint (region i j h) (region k l h')

omit [Fintype V] in
private theorem exists_index {T : SimpleGraph V} {a b v : V} (p : T.Walk a b)
    (hv : v∈p.support) : ∃k,k≤p.length ∧ p.getVert k=v := by
  induction p with
  | nil =>
      simp only [Walk.support_nil,List.mem_singleton] at hv
      exact ⟨0,by simp,by simpa using hv.symm⟩
  | @cons a b c hab q ih =>
      simp only [Walk.support_cons,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨0,by omega,rfl⟩
      · obtain ⟨k,hk,he⟩ := ih hv
        exact ⟨k+1,by simpa using Nat.succ_le_succ hk,by simpa using he⟩

private theorem embedding_gap {n : ℕ} (f : Fin n ↪o ℕ) (i j : Fin n)
    (h : i.val+2≤j.val) : f i+2≤f j := by
  let k : Fin n := ⟨i.val+1,by omega⟩
  have h1 := f.strictMono (show i<k by change i.val < i.val+1; omega)
  have h2 := f.strictMono (show k<j by change i.val+1 < j.val; omega)
  omega

/-- Order the selected vertices of one auxiliary path. -/
theorem orderedString_of_path (G T : SimpleGraph V) (hTG : T≤G)
    (B R : Finset V) {a b : V} (p : T.Walk a b) (hp : p.IsPath)
    (hinterior : ∀v∈p.support,v∈interiors T B)
    (hcuts : ∀v∈R,CutsRoutes G T v)
    (hterm : ∀v∈p.support,∀t∈B,G.Reachable v t→T.Reachable v t) :
    ∃s : OrderedString G B R,∀v,(∃i,s.vertex i=v) ↔ v∈p.support ∧ v∈R := by
  let S := (Finset.range (p.length+1)).filter fun k => p.getVert k∈R
  let f : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  have hf (i : Fin S.card) : f i≤p.length ∧ p.getVert (f i)∈R := by
    have hi := S.orderEmbOfFin_mem rfl i
    simpa only [S,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff] using hi
  have hinj : Function.Injective (fun i => p.getVert (f i)) := by
    intro i j he
    exact f.injective (hp.getVert_injOn (hf i).1 (hf j).1 he)
  have hd (k : ℕ) : T.degree (p.getVert k)=2 :=
    (Finset.mem_filter.mp (hinterior _ (p.getVert_mem_support k))).2.1
  let reg := fun (i j : Fin S.card) (h : i.val+2≤j.val) =>
    betweenRegion p G hp (f i) (f j) (embedding_gap f i j h) (hf j).1
  let s : OrderedString G B R := {
    length := S.card
    vertex := fun i => p.getVert (f i)
    injective := hinj
    relevant := fun i => (hf i).2
    region := reg
    connected := fun i j h => betweenRegion_connected p G hp _ _ _ _
    no_feet := by
      intro i j h
      exact betweenRegion_no_feet p G hTG hp B
        (fun v hv => (Finset.mem_filter.mp (hinterior v hv)).2.2)
        _ _ _ _ (fun k _ _ => hd k) (hcuts _ (hf i).2) (hcuts _ (hf j).2)
        (hterm _ (p.getVert_mem_support _))
    avoids := by
      intro i j h
      exact ⟨fun hm => (betweenRegion_avoids p G hp _ _ _ _ hm).1 rfl,
        fun hm => (betweenRegion_avoids p G hp _ _ _ _ hm).2 rfl⟩
    between := by
      intro i j h k hik hkj
      exact openSegment_subset_between p G hTG hp _ _ _ _
        ((mem_openSegment p _ _ _).mpr ⟨f k,f.strictMono hik,f.strictMono hkj,rfl⟩)
    boundary := fun i j h _ hu _ hadj hw => betweenRegion_boundary p G hp _ _ _ _ hu hadj hw
    disjoint := by
      intro i j h k l h' hjk
      exact betweenRegion_disjoint p G hTG hp _ _ _ _ _ _ (f.monotone hjk) (hf l).1
        (hcuts _ (hf j).2) (hcuts _ (hf k).2) }
  refine ⟨s,?_⟩
  intro v
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨p.getVert_mem_support _,(hf i).2⟩
  · rintro ⟨hvp,hvR⟩
    obtain ⟨k,hk,he⟩ := exists_index p hvp
    have hkS : k∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),he.symm ▸ hvR⟩
    have hkrange : k∈Set.range f := by
      rw [show f=S.orderEmbOfFin rfl from rfl,Finset.range_orderEmbOfFin]
      exact hkS
    obtain ⟨i,hi⟩ := hkrange
    exact ⟨i,by change p.getVert (f i)=v; rw [hi,he]⟩

/-- The geometric strings lemma. The original graph may be disconnected.
The terminal-branch premise is explicit and supplies all relevance geometry. -/
theorem exists_strings (G : SimpleGraph V) (B R : Finset V)
    (hrelevant : ∀v∈R,v∉B→2≤Nat.card (TerminalBranch G B v)) :
    ∃E : Finset V,E⊆R ∧ E.card≤2*B.card ∧
      ∃n : ℕ,n≤2*B.card ∧ ∃s : Fin n→OrderedString G B (R\E),
        ∀v∈R,v∉E→∃c i,(s c).vertex i=v := by
  obtain ⟨F,hFG,hF,hreach,hE,hinterior⟩ := exists_terminal_span G B R hrelevant
  let T := TerminalForest.span F B
  let E := exceptions T B R
  have hTG : T≤G := (TerminalForest.span_le F B).trans hFG
  have hT : T.IsAcyclic := TerminalForest.span_isAcyclic F hF B
  have hcuts (v : V) (hv : v∈R\E) : CutsRoutes G T v := by
    obtain ⟨hvR,hvE⟩ := Finset.mem_sdiff.mp hv
    have hvI := hinterior v hvR hvE
    have hvd := (Finset.mem_filter.mp hvI).2
    exact span_cutsRoutes G F hFG hF hreach B v (hrelevant v hvR hvd.2) hvd.1
  have hbuild (c : Thread T B) :
      ∃s : OrderedString G B (R\E),∀v,(∃i,s.vertex i=v) ↔ v∈threadVertices T B c ∧ v∈R\E := by
    obtain ⟨a,b,p,hp,hpc⟩ := exists_thread_path T hT B c
    have hpin (v : V) (hv : v∈p.support) : v∈interiors T B :=
      thread_subset T B c (hpc ▸ List.mem_toFinset.mpr hv)
    obtain ⟨s,hs⟩ := orderedString_of_path G T hTG B (R\E) p hp hpin hcuts (by
      intro v hv t ht hvt
      have hd := (Finset.mem_filter.mp (hpin v hv)).2.1
      exact terminal_reachable G F hreach B (by change 0<T.degree v; omega) ht hvt)
    refine ⟨s,?_⟩
    intro v
    rw [hs]
    exact and_congr_left (fun _ => by rw [←hpc,List.mem_toFinset])
  choose s hs using hbuild
  letI : Fintype (Thread T B) := Fintype.ofFinite _
  let e := Fintype.equivFin (Thread T B)
  refine ⟨E,Finset.inter_subset_left,hE,Fintype.card (Thread T B),?_,fun c => s (e.symm c),?_⟩
  · simpa only [Nat.card_eq_fintype_card] using thread_count F hF B
  · intro v hvR hvE
    have hvI := hinterior v hvR hvE
    let c : Thread T B := (T.induce (↑(interiors T B) : Set V)).connectedComponentMk ⟨v,hvI⟩
    have hvc : v∈threadVertices T B c := by
      apply Finset.mem_image.mpr
      refine ⟨⟨v,hvI⟩,?_,rfl⟩
      apply Set.mem_toFinset.mpr
      exact (ConnectedComponent.mem_supp_iff c _).mpr rfl
    obtain ⟨i,hi⟩ := (hs c v).mpr ⟨hvc,Finset.mem_sdiff.mpr ⟨hvR,hvE⟩⟩
    refine ⟨e c,?_⟩
    change ∃i,(s (e.symm (e c))).vertex i=v
    rw [e.symm_apply_apply]
    exact ⟨i,hi⟩


/-- A terminal budget also bounds both the exceptions and string count. -/
theorem exists_strings_of_card_le (G : SimpleGraph V) (B R : Finset V) (b : ℕ)
    (hB : B.card≤b)
    (hrelevant : ∀v∈R,v∉B→2≤Nat.card (TerminalBranch G B v)) :
    ∃E : Finset V,E⊆R ∧ E.card≤2*b ∧
      ∃n : ℕ,n≤2*b ∧ ∃s : Fin n→OrderedString G B (R\E),
        ∀v∈R,v∉E→∃c i,(s c).vertex i=v := by
  obtain ⟨E,hER,hE,n,hn,s,hs⟩ := exists_strings G B R hrelevant
  exact ⟨E,hER,hE.trans (Nat.mul_le_mul_left 2 hB),n,
    hn.trans (Nat.mul_le_mul_left 2 hB),s,hs⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings

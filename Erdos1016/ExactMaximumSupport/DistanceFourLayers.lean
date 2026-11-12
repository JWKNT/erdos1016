import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The actual graph on four distance layers

Each layer has two vertices. The enumeration preserves the distance labels,
and the pulled-back graph inherits its local constraints from shortest paths
and the ambient degrees. Only the two middle layers require degree three.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.DistanceFourLayers

local instance distanceLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Label := Fin 4 × Bool
variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V) (k : ℕ)

omit [Fintype V] in
/-- Adjacent vertices differ by at most one in actual distance from the base. -/
theorem dist_adj (hH : H.Connected) {u v : V} (huv : H.Adj u v) :
    H.dist s u ≤ H.dist s v+1 ∧ H.dist s v ≤ H.dist s u+1 := by
  have h1 := hH.dist_triangle (u:=s) (v:=v) (w:=u)
  have h2 := hH.dist_triangle (u:=s) (v:=u) (w:=v)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm] at h1
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr huv] at h2
  exact ⟨h1,h2⟩

omit [Fintype V] in
/-- Every nonzero distance layer has an actual predecessor neighbor. -/
theorem exists_predecessor (hH : H.Connected) (v : V) (hv : 0 < H.dist s v) :
    ∃ w, H.Adj w v ∧ H.dist s w+1=H.dist s v := by
  obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist v s
  cases p with
  | nil => simp only [SimpleGraph.dist_self] at hv; omega
  | @cons v w s hvw q =>
    have hq := H.dist_le q
    rw [SimpleGraph.Walk.length_cons,SimpleGraph.dist_comm (u:=v) (v:=s)] at hp
    rw [SimpleGraph.dist_comm (u:=w) (v:=s)] at hq
    have hh := (dist_adj H s hH hvw).1
    exact ⟨w,hvw.symm,by omega⟩

variable (hcard : ∀ i : Fin 4, Nat.card {v : V // H.dist s v = k+i.val}=2)

def layerEquiv (i : Fin 4) : Bool ≃ {v : V // H.dist s v=k+i.val} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_bool,← Nat.card_eq_fintype_card]
    exact (hcard i).symm)

def label (v : Label) : V := (layerEquiv H s k hcard v.1 v.2).1

theorem label_distance (v : Label) : H.dist s (label H s k hcard v)=k+v.1.val :=
  (layerEquiv H s k hcard v.1 v.2).2

theorem label_injective : Function.Injective (label H s k hcard) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hd := congrArg (H.dist s) he
  rw [label_distance,label_distance] at hd
  have hij : i=j := Fin.ext (by dsimp at hd; omega)
  subst j
  have hb : b=c := (layerEquiv H s k hcard i).injective (Subtype.ext he)
  exact Prod.ext rfl hb

theorem exists_label (i : Fin 4) (v : V) (hv : H.dist s v=k+i.val) :
    ∃ b : Bool, label H s k hcard (i,b)=v := by
  refine ⟨(layerEquiv H s k hcard i).symm ⟨v,hv⟩,?_⟩
  exact congrArg Subtype.val ((layerEquiv H s k hcard i).apply_symm_apply ⟨v,hv⟩)

def windowGraph : SimpleGraph Label := H.comap (label H s k hcard)

section DegreeTransport
variable {W : Type*} [Fintype W]
omit s k in
/-- Injective pullback cannot increase a vertex degree. -/
theorem degree_comap_le (f : W → V) (hf : Function.Injective f) (u : W) :
    (H.comap f).degree u ≤ H.degree (f u) := by
  unfold SimpleGraph.degree
  apply Finset.card_le_card_of_injOn f
  · intro w hw
    exact (H.mem_neighborFinset _ _).mpr ((H.comap f).mem_neighborFinset _ _ |>.mp hw)
  · intro a _ b _ hab
    exact hf hab

omit s k in
/-- If every ambient neighbor is retained, the pullback degree is exact. -/
theorem degree_comap_eq (f : W → V) (hf : Function.Injective f) (u : W)
    (hall : ∀ v, H.Adj (f u) v → ∃ w, f w=v) :
    (H.comap f).degree u = H.degree (f u) := by
  unfold SimpleGraph.degree
  apply Finset.card_bij (fun w _ => f w)
  · intro w hw
    exact (H.mem_neighborFinset _ _).mpr ((H.comap f).mem_neighborFinset _ _ |>.mp hw)
  · intro a _ b _ hab
    exact hf hab
  · intro v hv
    obtain ⟨w,hw⟩ := hall v ((H.mem_neighborFinset _ _).mp hv)
    refine ⟨w,?_,hw⟩
    apply ((H.comap f).mem_neighborFinset _ _).mpr
    change H.Adj (f u) (f w)
    rw [hw]
    exact (H.mem_neighborFinset _ _).mp hv

omit s k in
/-- A missing neighbor costs at least one degree in the pulled-back graph. -/
theorem degree_comap_add_one_le (f : W → V) (hf : Function.Injective f) (u : W)
    (v : V) (hv : H.Adj (f u) v) (hout : ∀ w, f w≠v) :
    (H.comap f).degree u+1 ≤ H.degree (f u) := by
  have hn : v ∉ ((H.comap f).neighborFinset u).image f := by
    intro h
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp h
    exact hout w hw
  have hs : insert v (((H.comap f).neighborFinset u).image f) ⊆ H.neighborFinset (f u) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (H.mem_neighborFinset _ _).mpr hv
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      exact (H.mem_neighborFinset _ _).mpr ((H.comap f).mem_neighborFinset _ _ |>.mp hw)
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_not_mem hn,Finset.card_image_of_injective _ hf] at hc
  exact hc
end DegreeTransport

/-- Pullback edges join only the same or consecutive distance layers. -/
theorem window_adj_levels (hH : H.Connected) (u v : Label)
    (huv : (windowGraph H s k hcard).Adj u v) :
    u.1.val ≤ v.1.val+1 ∧ v.1.val ≤ u.1.val+1 := by
  have h := dist_adj H s hH huv
  rw [label_distance,label_distance] at h
  omega

/-- Every layer after the first has a neighbor in the preceding retained layer. -/
theorem window_predecessor (hH : H.Connected) (v : Label) (hv : 0 < v.1.val) :
    ∃ w : Label, (windowGraph H s k hcard).Adj w v ∧ w.1.val+1=v.1.val := by
  have hd := label_distance H s k hcard v
  obtain ⟨u,hu,hdist⟩ := exists_predecessor H s hH (label H s k hcard v) (by omega)
  let i : Fin 4 := ⟨v.1.val-1,by have := v.1.isLt; omega⟩
  have hi : H.dist s u=k+i.val := by dsimp [i]; omega
  obtain ⟨b,hb⟩ := exists_label H s k hcard i u hi
  refine ⟨(i,b),?_,by dsimp [i]; omega⟩
  change H.Adj (label H s k hcard (i,b)) (label H s k hcard v)
  rw [hb]
  exact hu

/-- Every neighbor of a middle-layer vertex is in the enumerated window. -/
theorem middle_neighbor_retained (hH : H.Connected) (v : Label)
    (hv : v.1=1 ∨ v.1=2) (u : V) (hu : H.Adj (label H s k hcard v) u) :
    ∃ w : Label, label H s k hcard w=u := by
  have hd := label_distance H s k hcard v
  have hh := dist_adj H s hH hu
  have hmid : v.1.val=1 ∨ v.1.val=2 := by
    rcases hv with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  have hlo : k ≤ H.dist s u := by omega
  have hhi : H.dist s u < k+4 := by omega
  let i : Fin 4 := ⟨H.dist s u-k,by omega⟩
  obtain ⟨b,hb⟩ := exists_label H s k hcard i u (by dsimp [i]; omega)
  exact ⟨(i,b),hb⟩

/-- Both middle layers preserve their full ambient degree. -/
theorem window_middle_degree (hH : H.Connected)
    (hmid : ∀ v, H.dist s v=k+1 ∨ H.dist s v=k+2 → H.degree v=3)
    (v : Label) (hv : v.1=1 ∨ v.1=2) :
    (windowGraph H s k hcard).degree v=3 := by
  change (H.comap (label H s k hcard)).degree v=3
  rw [degree_comap_eq H (label H s k hcard) (label_injective H s k hcard) v
    (middle_neighbor_retained H s k hcard hH v hv)]
  apply hmid
  rw [label_distance]
  rcases hv with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-- A first-layer vertex loses its predecessor outside the retained window. -/
theorem window_first_degree (hH : H.Connected) (hk : 1 ≤ k)
    (hdeg : ∀ v,H.degree v≤3) (v : Label) (hv : v.1=0) :
    (windowGraph H s k hcard).degree v≤2 := by
  have hd : H.dist s (label H s k hcard v)=k := by
    rw [label_distance,hv]; simp
  obtain ⟨u,hu,hdist⟩ := exists_predecessor H s hH (label H s k hcard v) (by omega)
  have hout : ∀ w : Label, label H s k hcard w≠u := by
    intro w he
    have hw := label_distance H s k hcard w
    rw [he] at hw
    omega
  have hh := degree_comap_add_one_le H (label H s k hcard)
    (label_injective H s k hcard) v u hu.symm hout
  have hm := hdeg (label H s k hcard v)
  change (H.comap (label H s k hcard)).degree v≤2
  omega

/-- No pulled-back vertex has larger degree than its ambient vertex. -/
theorem window_degree_le (hdeg : ∀ v,H.degree v≤3) (v : Label) :
    (windowGraph H s k hcard).degree v≤3 :=
  (degree_comap_le H (label H s k hcard) (label_injective H s k hcard) v).trans
    (hdeg (label H s k hcard v))

include hcard in
/-- The actual eight-vertex distance-window graph satisfies all four-layer hypotheses. -/
theorem exists_layer_embedding (hH : H.Connected) (hk : 1 ≤ k)
    (hdeg : ∀ v,H.degree v≤3)
    (hmid : ∀ v, H.dist s v=k+1 ∨ H.dist s v=k+2 → H.degree v=3) :
    ∃ ι : Label → V, Function.Injective ι ∧
      (∀ v : Label, H.dist s (ι v)=k+v.1.val) ∧
      (∀ u v : Label, (H.comap ι).Adj u v →
        u.1.val≤v.1.val+1 ∧ v.1.val≤u.1.val+1) ∧
      (∀ v : Label, v.1=1 ∨ v.1=2 → (H.comap ι).degree v=3) ∧
      (∀ v : Label, v.1=0 → (H.comap ι).degree v≤2) ∧
      (∀ v : Label, (H.comap ι).degree v≤3) ∧
      (∀ v : Label, 0<v.1.val → ∃ w : Label,
        (H.comap ι).Adj w v ∧ w.1.val+1=v.1.val) := by
  exact ⟨label H s k hcard,label_injective H s k hcard,label_distance H s k hcard,
    window_adj_levels H s k hcard hH,window_middle_degree H s k hcard hH hmid,
    window_first_degree H s k hcard hH hk hdeg,window_degree_le H s k hcard hdeg,
    window_predecessor H s k hcard hH⟩

end Erdos1016.ExactMaximumSupport.DistanceFourLayers

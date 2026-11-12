import Erdos1016.ExactMaximumSupport.MixedTiles
import Erdos1016.ExactMaximumSupport.NetworkIsoInduce
import Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore
import Erdos1016.ExactMaximum.NetAddVertex

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Remove two cap vertices from a physical ladder

The induced networks retain every original physical label.
Positive-degree normalization removes only isolated ambient vertices.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTilesUncap
open BoundaryTrace BoundaryTrace.Network
open MixedTiles

local instance uncapDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The internal vertices of a capped mixed chain. -/
def internal (v : CappedVertex T) : Prop := v≠Sum.inr false ∧ v≠Sum.inr true

/-- Removing the two cap vertices leaves the exact physical chain. -/
def chainIso : NetworkIso (chain T) ((capped T).induce (internal T)) where
  vertices := Equiv.ofBijective (fun v => ⟨Sum.inl v,by simp [internal]⟩)
    ⟨fun _ _ h => Sum.inl.inj (congrArg Subtype.val h),by
      rintro ⟨v,hv⟩
      rcases v with v | b
      · exact ⟨v,rfl⟩
      · cases b <;> simp [internal] at hv⟩
  edges := Equiv.ofBijective (fun e => ⟨Sum.inl e,by
      simp [Network.inside,capped,cappedSrc,cappedDst,internal]⟩)
    ⟨fun _ _ h => Sum.inl.inj (congrArg Subtype.val h),by
      rintro ⟨e,he⟩
      rcases e with e | (b | b)
      · exact ⟨e,rfl⟩
      · simp [Network.inside,capped,cappedSrc,cappedDst,internal] at he
      · simp [Network.inside,capped,cappedSrc,cappedDst,internal] at he⟩
  joins _ := Or.inl ⟨rfl,rfl⟩

@[simp] theorem chainIso_vertices (v : Vertex T) :
    ((chainIso T).vertices v).1=Sum.inl v := rfl

@[simp] theorem chainIso_edges (e : ChainEdge T) :
    ((chainIso T).edges e).1=Sum.inl e := rfl

variable {V E : Type*} [Fintype E] (N : Network V E) (a b c d : V)

/-- Add the two physical cap vertices. -/
abbrev doubleCap := (N.addVertex a b).addVertex (some c) (some d)

/-- Normalize the double cap by removing only isolated vertices. -/
abbrev positiveCap := ThirdPortMarkedCore.positive (doubleCap N a b c d)

/-- Surviving original vertices in the normalized double cap. -/
def old (v : {v // 0<(doubleCap N a b c d).deg (fun _ => 1) v}) : Prop :=
  v.1≠some none ∧ v.1≠none

/-- Original positive-degree vertices stay positive after the two caps are added. -/
theorem positive_old {v : V} (hv : 0<N.deg (fun _ => 1) v) :
    0<(doubleCap N a b c d).deg (fun _ => 1) (some (some v)) := by
  change 0<((N.addVertex a b).addVertex (some c) (some d)).deg _ _
  rw [Network.deg_addVertex_some,Network.deg_addVertex_some]
  omega

/-- Positive original cap endpoints cannot create a new positive old vertex. -/
theorem positive_old_iff
    (ha : 0<N.deg (fun _ => 1) a) (hb : 0<N.deg (fun _ => 1) b)
    (hc : 0<N.deg (fun _ => 1) c) (hd : 0<N.deg (fun _ => 1) d) (v : V) :
    0<(doubleCap N a b c d).deg (fun _ => 1) (some (some v)) ↔
      0<N.deg (fun _ => 1) v := by
  constructor
  · intro h
    by_cases hpos : 0<N.deg (fun _ => 1) v
    · exact hpos
    · have hva : v≠a := fun h => hpos (h ▸ ha)
      have hvb : v≠b := fun h => hpos (h ▸ hb)
      have hvc : v≠c := fun h => hpos (h ▸ hc)
      have hvd : v≠d := fun h => hpos (h ▸ hd)
      change 0<((N.addVertex a b).addVertex (some c) (some d)).deg _ _ at h
      rw [Network.deg_addVertex_some,Network.deg_addVertex_some] at h
      simpa [hva,hvb,hvc,hvd] using h
  · exact positive_old N a b c d

/-- Removing both normalized caps recovers the original positive-degree network. -/
def oldIso
    (ha : 0<N.deg (fun _ => 1) a) (hb : 0<N.deg (fun _ => 1) b)
    (hc : 0<N.deg (fun _ => 1) c) (hd : 0<N.deg (fun _ => 1) d) :
    NetworkIso (ThirdPortMarkedCore.positive N)
      ((positiveCap N a b c d).induce (old N a b c d)) where
  vertices := Equiv.ofBijective
    (fun v => ⟨⟨some (some v.1),positive_old N a b c d v.2⟩,by simp [old]⟩)
    ⟨fun _ _ h => Subtype.ext (Option.some.inj (Option.some.inj
        (congrArg (fun v => v.1.1) h))),by
      rintro ⟨⟨v,hv⟩,h⟩
      rcases v with _ | v
      · simp [old] at h
      rcases v with _ | v
      · simp [old] at h
      exact ⟨⟨v,(positive_old_iff N a b c d ha hb hc hd v).mp hv⟩,rfl⟩⟩
  edges := Equiv.ofBijective
    (fun e => ⟨ThirdPortMarkedCore.positiveEdge (doubleCap N a b c d)
        (Sum.inl (Sum.inl e.1)),by
      simp [Network.inside,Network.induce,Network.addVertex,old]⟩)
    ⟨fun _ _ h => Subtype.ext (Sum.inl.inj (Sum.inl.inj
        (congrArg (fun e => e.1.1) h))),by
      rintro ⟨⟨e,he⟩,h⟩
      rcases e with (e | b') | b'
      · exact ⟨ThirdPortMarkedCore.positiveEdge N e,rfl⟩
      · simp [Network.inside,Network.induce,Network.addVertex,old] at h
      · simp [Network.inside,Network.induce,Network.addVertex,old] at h⟩
  joins _ := Or.inl ⟨rfl,rfl⟩

variable (I : NetworkIso (capped T) (positiveCap N a b c d))
    (hl : (I.vertices (Sum.inr false)).1=some none)
    (hr : (I.vertices (Sum.inr true)).1=none)

include hl hr in
/-- A cap-preserving isomorphism maps exactly the internal vertices to old vertices. -/
theorem internal_iff_old (v : CappedVertex T) :
    internal T v ↔ old N a b c d (I.vertices v) := by
  change (v≠Sum.inr false ∧ v≠Sum.inr true) ↔
    ((I.vertices v).1≠some none ∧ (I.vertices v).1≠none)
  rw [← hl,← hr]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun h => h₁ (I.vertices.injective (Subtype.ext h)),
      fun h => h₂ (I.vertices.injective (Subtype.ext h))⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨fun h => h₁ (congrArg (fun v => (I.vertices v).1) h),
      fun h => h₂ (congrArg (fun v => (I.vertices v).1) h)⟩

/-- Delete both caps from an actual normalized capped-ladder isomorphism. -/
def uncap
    (ha : 0<N.deg (fun _ => 1) a) (hb : 0<N.deg (fun _ => 1) b)
    (hc : 0<N.deg (fun _ => 1) c) (hd : 0<N.deg (fun _ => 1) d) :
    NetworkIso (chain T) (ThirdPortMarkedCore.positive N) :=
  (chainIso T).trans ((I.induce (internal T) (old N a b c d)
    (internal_iff_old T N a b c d I hl hr)).trans (oldIso N a b c d ha hb hc hd).symm)

variable (ha : 0<N.deg (fun _ => 1) a) (hb : 0<N.deg (fun _ => 1) b)
    (hc : 0<N.deg (fun _ => 1) c) (hd : 0<N.deg (fun _ => 1) d)

/-- The uncapped vertex map is the original vertex map with both `some` wrappers removed. -/
theorem uncap_vertices (v : Vertex T) :
    some (some ((uncap T N a b c d I hl hr ha hb hc hd).vertices v).1)=
      (I.vertices (Sum.inl v)).1 := by
  exact congrArg (fun v => v.1.1)
    ((oldIso N a b c d ha hb hc hd).vertices.apply_symm_apply
      ((I.induce (internal T) (old N a b c d)
        (internal_iff_old T N a b c d I hl hr)).vertices ((chainIso T).vertices v)))

/-- The uncapped edge map retains the original physical label. -/
theorem uncap_edges (e : ChainEdge T) :
    Sum.inl (Sum.inl ((uncap T N a b c d I hl hr ha hb hc hd).edges e).1)=
      (I.edges (Sum.inl e)).1 := by
  exact congrArg (fun e => e.1.1)
    ((oldIso N a b c d ha hb hc hd).edges.apply_symm_apply
      ((I.induce (internal T) (old N a b c d)
        (internal_iff_old T N a b c d I hl hr)).edges ((chainIso T).edges e)))

omit [Fintype E] in
/-- An old neighbor of the first cap is one of its two prescribed endpoints. -/
theorem left_neighbor {g : (E ⊕ Bool) ⊕ Bool} {v : V}
    (h : (doubleCap N a b c d).Joins g (some none) (some (some v))) : v=a ∨ v=b := by
  rcases g with (g | q) | q
  · simp [Network.Joins,Network.addVertex] at h
  · cases q <;> simp [Network.Joins,Network.addVertex] at h <;> aesop
  · simp [Network.Joins,Network.addVertex] at h

omit [Fintype E] in
/-- An old neighbor of the second cap is one of its two prescribed endpoints. -/
theorem right_neighbor {g : (E ⊕ Bool) ⊕ Bool} {v : V}
    (h : (doubleCap N a b c d).Joins g none (some (some v))) : v=c ∨ v=d := by
  rcases g with (g | q) | q
  · simp [Network.Joins,Network.addVertex] at h
  · simp [Network.Joins,Network.addVertex] at h
  · cases q <;> simp [Network.Joins,Network.addVertex] at h <;> aesop

/-- Each left chain port maps to an original endpoint of the first cap. -/
theorem uncap_left (q : Bool) :
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.left T 0 q)).1=a ∨
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.left T 0 q)).1=b := by
  have hj := I.map_joins (show (capped T).Joins (Sum.inr (Sum.inl q))
      (Sum.inr false) (Sum.inl (MixedTiles.left T 0 q)) from Or.inl ⟨rfl,rfl⟩)
  have hj' : (doubleCap N a b c d).Joins (I.edges (Sum.inr (Sum.inl q))).1
      (I.vertices (Sum.inr false)).1 (I.vertices (Sum.inl (MixedTiles.left T 0 q))).1 := by
    rcases hj with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
    · exact Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
  rw [hl,← uncap_vertices T N a b c d I hl hr ha hb hc hd] at hj'
  exact left_neighbor N a b c d hj'

/-- Each right chain port maps to an original endpoint of the second cap. -/
theorem uncap_right (q : Bool) :
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.right T (Fin.last k) q)).1=c ∨
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.right T (Fin.last k) q)).1=d := by
  have hj := I.map_joins (show (capped T).Joins (Sum.inr (Sum.inr q))
      (Sum.inr true) (Sum.inl (MixedTiles.right T (Fin.last k) q)) from Or.inr ⟨rfl,rfl⟩)
  have hj' : (doubleCap N a b c d).Joins (I.edges (Sum.inr (Sum.inr q))).1
      (I.vertices (Sum.inr true)).1 (I.vertices (Sum.inl (MixedTiles.right T (Fin.last k) q))).1 := by
    rcases hj with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
    · exact Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
  rw [hr,← uncap_vertices T N a b c d I hl hr ha hb hc hd] at hj'
  exact right_neighbor N a b c d hj'

private theorem unordered_pair {α : Type*} (f : Bool → α) (a b : α)
    (hinj : Function.Injective f) (h : ∀q,f q=a ∨ f q=b) :
    (f false=a ∧ f true=b) ∨ (f false=b ∧ f true=a) := by
  have hne : f false≠f true := fun he => Bool.false_ne_true (hinj he)
  rcases h false with h₀ | h₀ <;> rcases h true with h₁ | h₁
  · exact False.elim (hne (h₀.trans h₁.symm))
  · exact Or.inl ⟨h₀,h₁⟩
  · exact Or.inr ⟨h₀,h₁⟩
  · exact False.elim (hne (h₀.trans h₁.symm))

/-- The left pair is preserved, with either of its two physical rail orders. -/
theorem uncap_left_pair :
    let J := uncap T N a b c d I hl hr ha hb hc hd
    ((J.vertices (MixedTiles.left T 0 false)).1=a ∧
      (J.vertices (MixedTiles.left T 0 true)).1=b) ∨
    ((J.vertices (MixedTiles.left T 0 false)).1=b ∧
      (J.vertices (MixedTiles.left T 0 true)).1=a) := by
  apply unordered_pair (fun q =>
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.left T 0 q)).1) a b
  · intro q r he
    have hv := (uncap T N a b c d I hl hr ha hb hc hd).vertices.injective (Subtype.ext he)
    apply (T 0).left_injective
    simpa only [MixedTiles.left,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hv
  · exact uncap_left T N a b c d I hl hr ha hb hc hd

/-- The right pair is preserved, with either of its two physical rail orders. -/
theorem uncap_right_pair :
    let J := uncap T N a b c d I hl hr ha hb hc hd
    ((J.vertices (MixedTiles.right T (Fin.last k) false)).1=c ∧
      (J.vertices (MixedTiles.right T (Fin.last k) true)).1=d) ∨
    ((J.vertices (MixedTiles.right T (Fin.last k) false)).1=d ∧
      (J.vertices (MixedTiles.right T (Fin.last k) true)).1=c) := by
  apply unordered_pair (fun q =>
    ((uncap T N a b c d I hl hr ha hb hc hd).vertices (MixedTiles.right T (Fin.last k) q)).1) c d
  · intro q r he
    have hv := (uncap T N a b c d I hl hr ha hb hc hd).vertices.injective (Subtype.ext he)
    apply (T (Fin.last k)).right_injective
    simpa only [MixedTiles.right,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hv
  · exact uncap_right T N a b c d I hl hr ha hb hc hd

end Erdos1016.ExactMaximumSupport.MixedTilesUncap

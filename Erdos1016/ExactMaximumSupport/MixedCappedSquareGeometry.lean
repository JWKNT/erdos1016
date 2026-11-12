import Erdos1016.ExactMaximumSupport.MixedCappedStem
import Erdos1016.ExactMaximumSupport.MarkedSquareLocalCounts

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! # Actual square geometry after one marked label is deleted

All vertices and surviving labels retain their original identities.
Deleting the two right square vertices leaves precisely the preceding stem.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
open MixedCappedTileCut MixedCappedStem
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

def localEdge (t : Kind) (h : t=Kind.square) (b c : Bool) : t.Edge := by
  subst t
  exact (b,c)

@[simp] theorem local_src (t : Kind) (h : t=Kind.square) (b c : Bool) :
    t.src (localEdge t h b c)=t.left b := by subst t; rfl
@[simp] theorem local_dst (t : Kind) (h : t=Kind.square) (b c : Bool) :
    t.dst (localEdge t h b c)=t.right c := by subst t; rfl

theorem local_all (t : Kind) (h : t=Kind.square) (e : t.Edge) :
    ∃b c,e=localEdge t h b c := by subst t; exact ⟨e.1,e.2,rfl⟩

def squareLabel (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) : CappedEdge T := Sum.inl (inner T p (localEdge (T p) h b c))

def L (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedVertex T :=
  Sum.inl (left T p b)
def R (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) : CappedVertex T :=
  Sum.inl (right T p b)

@[simp] theorem label_src (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (b c : Bool) : (capped T).src (squareLabel T p h b c)=L T p b := by
  simp [squareLabel,capped,cappedSrc,MixedTiles.inner,chain,chainSrc,L,left]
@[simp] theorem label_dst (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (b c : Bool) : (capped T).dst (squareLabel T p h b c)=R T p c := by
  simp [squareLabel,capped,cappedDst,MixedTiles.inner,chain,chainDst,R,right]

theorem label_joins (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (b c : Bool) :
    (capped T).Joins (squareLabel T p h b c) (L T p b) (R T p c) :=
  Or.inl ⟨label_src T p h b c,label_dst T p h b c⟩

theorem L_inj (T : Fin (k+1) → Kind) (p : Fin (k+1)) {b c : Bool}
    (he : L T p b=L T p c) : b=c :=
  Kind.left_injective (T p) (eq_of_heq (Sigma.mk.inj (Sum.inl.inj he)).2)
theorem R_inj (T : Fin (k+1) → Kind) (p : Fin (k+1)) {b c : Bool}
    (he : R T p b=R T p c) : b=c :=
  Kind.right_injective (T p) (eq_of_heq (Sigma.mk.inj (Sum.inl.inj he)).2)

theorem L_ne_R (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (b c : Bool) : L T p b≠R T p c := by
  intro he
  have hh : (T p).left b=(T p).right c := eq_of_heq (Sigma.mk.inj (Sum.inl.inj he)).2
  rw [h] at hh
  exact Bool.false_ne_true (congrArg Prod.fst hh)

theorem label_inj (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) {b c b' c' : Bool}
    (he : squareLabel T p h b c=squareLabel T p h b' c') : b=b' ∧ c=c' := by
  have hs := congrArg (capped T).src he
  have hd := congrArg (capped T).dst he
  simp only [label_src,label_dst] at hs hd
  exact ⟨L_inj T p hs,R_inj T p hd⟩

/-- In the prefix through this tile, only local square labels meet a right vertex. -/
theorem incident_right (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (c : Bool) (g : CappedEdge T)
    (hi : (capped T).inside (after T p) g)
    (hg : (capped T).src g=R T p c ∨ (capped T).dst g=R T p c) :
    ∃b,g=squareLabel T p h b c := by
  rcases g with (⟨i,e⟩ | ⟨i,b⟩) | (b | b)
  · have hip : i=p := by
      rcases hg with hg | hg <;> exact congrArg Sigma.fst (Sum.inl.inj hg)
    subst i
    obtain ⟨b',c',rfl⟩ := local_all (T p) h e
    change (capped T).src (squareLabel T p h b' c')=R T p c ∨
      (capped T).dst (squareLabel T p h b' c')=R T p c at hg
    rw [label_src,label_dst] at hg
    rcases hg with hg | hg
    · exact False.elim (L_ne_R T p h b' c hg)
    · have he := R_inj T p hg
      subst c'
      exact ⟨b',rfl⟩
  · rcases hg with hg | hg
    · have hip : i.castSucc=p := congrArg Sigma.fst (Sum.inl.inj hg)
      have hh : i.val+1≤p.val := hi.2
      have he := congrArg Fin.val hip
      simp only [Fin.coe_castSucc] at he
      omega
    · have hip : i.succ=p := congrArg Sigma.fst (Sum.inl.inj hg)
      subst p
      exact False.elim (L_ne_R T i.succ h b c hg)
  · rcases hg with hg | hg
    · contradiction
    · have hip : (0 : Fin (k+1))=p := congrArg Sigma.fst (Sum.inl.inj hg)
      subst p
      exact False.elim (L_ne_R T 0 h b c hg)
  · exact False.elim (Bool.false_ne_true hi.2.symm)

/-- The literal prefix after deletion of the marked square label. -/
abbrev D (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square) (b c : Bool) :=
  ((capped T).sub (fun g => g≠squareLabel T p h b c)).sub
    (((capped T).sub (fun g => g≠squareLabel T p h b c)).inside (after T p))

theorem squareLabel_surjective (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (h : T p=Kind.square) (e : (T p).Edge) :
    ∃b c,Sum.inl (inner T p e)=squareLabel T p h b c := by
  obtain ⟨b,c,rfl⟩ := local_all (T p) h e
  exact ⟨b,c,rfl⟩

/-- Every other local square label remains in this actual prefix. -/
def retainedLabel (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c b' c' : Bool) (hne : (b',c')≠(b,c)) :
    {q : {g : CappedEdge T // g≠squareLabel T p h b c} //
      (capped T).inside (after T p) q.val} :=
  ⟨⟨squareLabel T p h b' c',fun he => hne (Prod.ext (label_inj T p h he).1
    (label_inj T p h he).2)⟩,by simp [Network.inside,label_src,label_dst,L,R,after,left,right]⟩

def leafLabel (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) := retainedLabel T p h b c (!b) c (by cases b <;> simp)

theorem leaf_joins (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) : (D T p h b c).Joins (leafLabel T p h b c) (R T p c) (L T p (!b)) :=
  (label_joins T p h (!b) c).symm

theorem leaf_only (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) (q) (hq : (D T p h b c).src q=R T p c ∨
      (D T p h b c).dst q=R T p c) : q=leafLabel T p h b c := by
  obtain ⟨b',hb'⟩ := incident_right T p h c q.val.val q.property hq
  have hne : b'≠b := by
    intro he
    subst b'
    exact q.val.property hb'
  have he : b'=!b := by cases b <;> cases b' <;> simp_all
  apply Subtype.ext
  apply Subtype.ext
  simpa [leafLabel,retainedLabel,he] using hb'

abbrev M (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square) (b c : Bool) :=
  (D T p h b c).sub ((D T p h b c).outside (fun v => v=R T p c))

def threadLabel (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c b' : Bool) :
    {q // (D T p h b c).outside (fun v => v=R T p c) q} :=
  ⟨retainedLabel T p h b c b' (!c) (by cases c <;> simp),by
    change (capped T).outside (fun v => v=R T p c) (squareLabel T p h b' (!c))
    simp only [Network.outside,label_src,label_dst]
    exact ⟨L_ne_R T p h b' c,fun he => by
      have hh := R_inj T p he
      cases c <;> contradiction⟩⟩

/-- The two surviving square labels form an actual degree-two thread. -/
theorem thread (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) : (M T p h b c).Thread
      (threadLabel T p h b c b) (threadLabel T p h b c (!b))
      (L T p b) (R T p (!c)) (L T p (!b)) := by
  refine ⟨label_joins T p h b (!c),(label_joins T p h (!b) (!c)).symm,?_,?_,?_⟩
  · intro he
    have hh := (label_inj T p h (congrArg (fun q => q.val.val.val) he)).1
    cases b <;> contradiction
  · intro he
    have hh := L_inj T p he
    cases b <;> contradiction
  · intro q hq
    obtain ⟨b',hb'⟩ := incident_right T p h (!c) q.val.val.val q.val.property hq
    have hcases : b'=b ∨ b'=!b := by cases b <;> cases b' <;> simp
    rcases hcases with he | he
    · left
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simpa [threadLabel,retainedLabel,he] using hb'
    · right
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simpa [threadLabel,retainedLabel,he] using hb'

theorem stem_inside (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (g : CappedEdge T) (hg : stem T p g) : (capped T).inside (after T p) g := by
  rcases g with (⟨i,e⟩ | ⟨i,b⟩) | (b | b)
  · have hh : i.val<p.val := hg
    exact ⟨hh.le,hh.le⟩
  · have hh : i.val<p.val := hg
    exact ⟨hh.le,by change i.val+1≤p.val; omega⟩
  · exact ⟨rfl,by change 0≤p.val; omega⟩
  · exact False.elim hg

/-- Inside the cut, each label belongs to the stem or to this square. -/
theorem inside_cases (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (g : CappedEdge T) (hg : (capped T).inside (after T p) g) :
    stem T p g ∨ ∃b c,g=squareLabel T p h b c := by
  rcases g with (⟨i,e⟩ | ⟨i,b⟩) | (b | b)
  · by_cases hip : i=p
    · subst i
      exact Or.inr (squareLabel_surjective T p h e)
    · left
      have hh : i.val≤p.val := hg.1
      have hne : i.val≠p.val := fun he => hip (Fin.ext he)
      change i.val<p.val
      omega
  · left
    have hh : i.val+1≤p.val := hg.2
    change i.val<p.val
    omega
  · exact Or.inl trivial
  · exact False.elim (Bool.false_ne_true hg.2.symm)

/-- Removing the two right vertices retains precisely the original stem labels. -/
theorem retained_iff (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) (g : CappedEdge T) :
    (((g≠squareLabel T p h b c ∧ (capped T).inside (after T p) g) ∧
      (capped T).outside (fun v => v=R T p c) g) ∧
      (capped T).outside (fun v => v=R T p (!c)) g) ↔ stem T p g := by
  constructor
  · rintro ⟨⟨⟨hne,hi⟩,hc⟩,hd⟩
    rcases inside_cases T p h g hi with hs | ⟨b',c',rfl⟩
    · exact hs
    · have hne₁ : c'≠c := fun he => hc.2 (by simp only [label_dst,he])
      have hne₂ : c'≠!c := fun he => hd.2 (by simp only [label_dst,he])
      cases c <;> cases c' <;> simp_all
  · intro hs
    have hi := stem_inside T p g hs
    have ho (d : Bool) : (capped T).outside (fun v => v=R T p d) g := by
      have hn : ¬((capped T).src g=R T p d ∨ (capped T).dst g=R T p d) := by
        intro ha
        obtain ⟨a,rfl⟩ := incident_right T p h d g hi ha
        exact Nat.lt_irrefl _ hs
      exact ⟨fun ha => hn (Or.inl ha),fun ha => hn (Or.inr ha)⟩
    have hn : g≠squareLabel T p h b c := by
      intro he
      subst g
      exact Nat.lt_irrefl _ hs
    exact ⟨⟨⟨hn,hi⟩,ho c⟩,ho (!c)⟩

/-- All old physical labels and vertices survive identically in the twice-deleted stem. -/
def stemIso (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square) (b c : Bool) :
    NetworkIso (PoleTerminalDeletion.deleted (M T p h b c) (R T p (!c)))
      ((capped T).sub (stem T p)) where
  vertices := Equiv.refl _
  edges :=
    { toFun := fun q => ⟨q.val.val.val.val,(retained_iff T p h b c _).mp
        ⟨⟨⟨q.val.val.val.property,q.val.val.property⟩,q.val.property⟩,q.property⟩⟩
      invFun := fun q =>
        let hs := (retained_iff T p h b c q.val).mpr q.property
        ⟨⟨⟨⟨q.val,hs.1.1.1⟩,hs.1.1.2⟩,hs.1.2⟩,hs.2⟩
      left_inv := fun q => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun q => by apply Subtype.ext; rfl }
  joins _ := Or.inl ⟨rfl,rfl⟩

/-- The four local routes have the exact coefficient used in the square estimate. -/
theorem local_route_sum (T : Fin (k+1) → Kind) (p : Fin (k+1)) (h : T p=Kind.square)
    (b c : Bool) :
    (D T p h b c).numPaths (L T p b) (R T p c)+
    (D T p h b c).numPaths (L T p b) (R T p (!c))+1+
    (D T p h b c).numPaths (R T p c) (R T p (!c))=
    4+3*((capped T).sub (stem T p)).numPaths (L T p b) (L T p (!b)) := by
  have hd : R T p (!c)≠R T p c := fun he => by
    have hh := R_inj T p he
    cases c <;> contradiction
  have hh := MarkedSquareLocalCounts.route_sum (D T p h b c)
    (leaf_joins T p h b c) (leaf_only T p h b c) (L_ne_R T p h b c) hd
    (thread T p h b c)
  have hi := (stemIso T p h b c).numPaths_eq (L T p b) (L T p (!b))
  rw [←hi] at hh
  exact hh

end Erdos1016.ExactMaximumSupport.MixedCappedSquareGeometry

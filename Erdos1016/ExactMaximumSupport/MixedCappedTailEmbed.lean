import Erdos1016.ExactMaximumSupport.MixedCappedSuffixPaths
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A literal tail inside a capped ladder

The tail keeps all tiles from its cutoff onward and the original right cap.
Its physical label image is exactly the exterior of the earlier vertices.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedTailEmbed
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles

local instance tailDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {k : ℕ}

/-- The original index of a tail tile. -/
def tailIndex (p : Fin (k+1)) (i : Fin (k-p.val+1)) : Fin (k+1) :=
  ⟨p.val+i.val,by have hp := p.isLt; have hi := i.isLt; omega⟩

theorem tailIndex_injective (p : Fin (k+1)) : Function.Injective (tailIndex p) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  change p.val+i.val=p.val+j.val at h'
  omega

@[simp] theorem tailIndex_zero (p : Fin (k+1)) : tailIndex p 0=p := by
  apply Fin.ext
  simp [tailIndex]

@[simp] theorem tailIndex_last (p : Fin (k+1)) : tailIndex p (Fin.last (k-p.val))=Fin.last k := by
  apply Fin.ext
  have hp := p.isLt
  simp only [tailIndex,Fin.val_mk,Fin.val_last]
  omega

theorem tailIndex_range (p i : Fin (k+1)) :
    (∃j,tailIndex p j=i) ↔ p.val≤ i.val := by
  constructor
  · rintro ⟨j,rfl⟩
    simp [tailIndex]
  · intro h
    refine ⟨⟨i.val-p.val,by have hi := i.isLt; omega⟩,?_⟩
    apply Fin.ext
    change p.val+(i.val-p.val)=i.val
    omega

/-- The tile sequence starting at the chosen cutoff. -/
def tail (T : Fin (k+1) → Kind) (p : Fin (k+1)) : Fin (k-p.val+1) → Kind :=
  fun i => T (tailIndex p i)

/-- Offset physical tile coordinates without changing any local coordinate. -/
def tileEmbedding (T : Fin (k+1) → Kind) (p : Fin (k+1)) (F : Kind → Type*) :
    (Σi,F (tail T p i)) ↪ (Σi,F (T i)) where
  toFun v := ⟨tailIndex p v.1,v.2⟩
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij := tailIndex_injective p (congrArg Sigma.fst h)
    change i=j at hij
    subst j
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

theorem tileEmbedding_range (T : Fin (k+1) → Kind) (p : Fin (k+1)) (F : Kind → Type*)
    (v : Σi,F (T i)) : (∃u,tileEmbedding T p F u=v) ↔ p.val≤v.1.val := by
  constructor
  · rintro ⟨u,rfl⟩
    simp [tileEmbedding,tailIndex]
  · intro h
    rcases v with ⟨i,v⟩
    obtain ⟨j,hj⟩ := (tailIndex_range p i).mpr h
    subst i
    exact ⟨⟨j,v⟩,rfl⟩

/-- The original index of an internal tail interface. -/
def linkIndex (p : Fin (k+1)) : Fin (k-p.val) ↪ Fin k where
  toFun i := ⟨p.val+i.val,by have hi := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change p.val+i.val=p.val+j.val at h'
    omega

theorem linkIndex_range (p : Fin (k+1)) (i : Fin k) :
    (∃j,linkIndex p j=i) ↔ p.val≤ i.val := by
  constructor
  · rintro ⟨j,rfl⟩
    simp [linkIndex]
  · intro h
    refine ⟨⟨i.val-p.val,by have hi := i.isLt; omega⟩,?_⟩
    apply Fin.ext
    change p.val+(i.val-p.val)=i.val
    omega

/-- The original left cap and all tiles strictly before the cutoff. -/
def before (T : Fin (k+1) → Kind) (p : Fin (k+1)) : CappedVertex T → Prop
  | Sum.inl v => v.1.val<p.val
  | Sum.inr b => b=false

/-- Embed the actual one-cap tail into the original capped ladder. -/
def embed (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    Network.Embed (MixedCappedSuffix.network (tail T p)) (capped T) where
  φ := Sum.map (tileEmbedding T p Kind.Vertex) (fun _ => true)
  ψ := Sum.map
    (Sum.map (tileEmbedding T p Kind.Edge) (Prod.map (linkIndex p) id)) Sum.inr
  φ_inj := Sum.map_injective.mpr ⟨(tileEmbedding T p Kind.Vertex).injective,
    fun _ _ _ => Subsingleton.elim _ _⟩
  ψ_inj := Sum.map_injective.mpr ⟨Sum.map_injective.mpr
    ⟨(tileEmbedding T p Kind.Edge).injective,
      fun x y h => Prod.ext ((linkIndex p).injective (congrArg Prod.fst h))
        (congrArg (fun z : Fin k × Bool => z.2) h)⟩,Sum.inr_injective⟩
  src e := by
    rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
    · rfl
    · rfl
    · change Sum.inl (right T (Fin.last k) b)=Sum.inl (right T (tailIndex p (Fin.last (k-p.val))) b)
      rw [tailIndex_last]
  dst e := by
    rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
    · rfl
    · rfl
    · rfl

@[simp] theorem embed_entry (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    (embed T p).φ (MixedCappedSuffix.entry (tail T p) b)=Sum.inl (left T p b) := by
  change Sum.inl (left T (tailIndex p 0) b)=_
  rw [tailIndex_zero]

@[simp] theorem embed_cap (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    (embed T p).φ (MixedCappedSuffix.cap (tail T p))=Sum.inr true := rfl

/-- The image is precisely the literal exterior label set, including the original right cap. -/
theorem embed_image (T : Fin (k+1) → Kind) (p : Fin (k+1)) (e : CappedEdge T) :
    (embed T p).image e ↔ (capped T).outside (before T p) e := by
  rcases e with (e | ⟨i,b⟩) | (b | b)
  · simpa [Network.Embed.image,embed,Network.outside,capped,cappedSrc,cappedDst,
      chain,chainSrc,chainDst,before] using tileEmbedding_range T p Kind.Edge e
  · simpa [Network.Embed.image,embed,Network.outside,capped,cappedSrc,cappedDst,
      chain,chainSrc,chainDst,before,right,left,Prod.exists,Prod.map,Prod.mk.injEq,
      Fin.coe_castSucc,Fin.val_succ,Nat.le_add_right] using (show (∃j,linkIndex p j=i) ↔
        p.val≤ i.val ∧ p.val≤ i.val+1 from by rw [linkIndex_range]; omega)
  · simp [Network.Embed.image,embed,Network.outside,capped,cappedSrc,cappedDst,before]
  · have hp := p.isLt
    simp [Network.Embed.image,embed,Network.outside,capped,cappedSrc,cappedDst,before,right]
    omega

/-- The actual exterior rank is exactly the weight of the retained tail. -/
theorem exterior_rank (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    networkRank ((capped T).sub ((capped T).outside (before T p)))=weight (tail T p) := by
  have h := (embed T p).networkRank_eq_sub
  have hp : (embed T p).image=(capped T).outside (before T p) :=
    funext fun e => propext (embed_image T p e)
  rw [hp] at h
  exact h.symm.trans (MixedCappedSuffix.rank (tail T p))

/-- Either entry has the exact full path count in the original exterior. -/
theorem exterior_entry_count (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    ((capped T).sub ((capped T).outside (before T p))).numPaths
      (Sum.inl (left T p b)) (Sum.inr true)=2^weight (tail T p) := by
  have h := (embed T p).numPaths_eq (MixedCappedSuffix.entry (tail T p) b)
    (MixedCappedSuffix.cap (tail T p))
  have hp : (embed T p).image=(capped T).outside (before T p) :=
    funext fun e => propext (embed_image T p e)
  rw [embed_entry,embed_cap,hp] at h
  rw [(capped T).numPaths_sub]
  exact h.symm.trans (MixedCappedSuffix.numPaths_entry_cap (tail T p) b)

/-- Tail weight is the sum over the original indices at or after the cutoff. -/
theorem tail_weight (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    weight (tail T p)=∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => p.val≤ i.val),
      (T i).weight := by
  classical
  unfold weight
  apply Finset.sum_bij (fun i _ => tailIndex p i)
  · intro i _
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by change p.val≤ p.val+i.val; omega⟩
  · intro i _ j _ hij
    exact tailIndex_injective p hij
  · intro i hi
    obtain ⟨j,hj⟩ := (tailIndex_range p i).mpr (Finset.mem_filter.mp hi).2
    exact ⟨j,Finset.mem_univ _,hj⟩
  · intro i _
    rfl

/-- The exterior rank is the sum of the retained original tile weights. -/
theorem exterior_rank_sum (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    networkRank ((capped T).sub ((capped T).outside (before T p)))=
      ∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => p.val≤ i.val), (T i).weight := by
  rw [exterior_rank,tail_weight]

/-- The exact exterior path count uses the retained original tile weights. -/
theorem exterior_entry_count_sum (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    ((capped T).sub ((capped T).outside (before T p))).numPaths
      (Sum.inl (left T p b)) (Sum.inr true)=
      2^(∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => p.val≤ i.val), (T i).weight) := by
  rw [exterior_entry_count,tail_weight]

end Erdos1016.ExactMaximumSupport.MixedCappedTailEmbed

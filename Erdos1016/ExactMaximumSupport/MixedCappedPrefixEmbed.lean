import Erdos1016.ExactMaximumSupport.MixedCappedPrefix
import Erdos1016.ExactMaximumSupport.MixedCappedTailEmbed
import Erdos1016.ExactMaximum.NetCircuits

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The literal prefix of a capped ladder

A nonempty prefix has its original left cap and forward physical orientations.
The empty prefix contains only the left cap and has rank zero.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedPrefixEmbed
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
open MixedCappedTailEmbed (before)

local instance prefixDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {k : ℕ}

/-- The original index of a retained prefix tile. -/
def prefixIndex (p : Fin (k+1)) (hp : 0<p.val) (i : Fin (p.val-1+1)) : Fin (k+1) :=
  ⟨i.val,by have hi := i.isLt; have hpk := p.isLt; omega⟩

theorem prefixIndex_injective (p : Fin (k+1)) (hp : 0<p.val) :
    Function.Injective (prefixIndex p hp) :=
  fun _ _ h => Fin.ext (congrArg (fun i : Fin (k+1) => i.val) h)

theorem prefixIndex_range (p i : Fin (k+1)) (hp : 0<p.val) :
    (∃j,prefixIndex p hp j=i) ↔ i.val<p.val := by
  constructor
  · rintro ⟨j,rfl⟩
    have hj := j.isLt
    change j.val<p.val
    omega
  · intro h
    exact ⟨⟨i.val,by omega⟩,rfl⟩

/-- The tile sequence strictly before the cutoff. -/
def prefixTiles (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) :
    Fin (p.val-1+1) → Kind := fun i => T (prefixIndex p hp i)

def tileEmbedding (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) (F : Kind → Type*) :
    (Σi,F (prefixTiles T p hp i)) ↪ (Σi,F (T i)) where
  toFun v := ⟨prefixIndex p hp v.1,v.2⟩
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i=j := prefixIndex_injective p hp (congrArg Sigma.fst h)
    subst j
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

theorem tileEmbedding_range (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val)
    (F : Kind → Type*) (v : Σi,F (T i)) :
    (∃u,tileEmbedding T p hp F u=v) ↔ v.1.val<p.val := by
  constructor
  · rintro ⟨u,rfl⟩
    have hi := u.1.isLt
    change u.1.val<p.val
    omega
  · intro h
    rcases v with ⟨i,v⟩
    obtain ⟨j,hj⟩ := (prefixIndex_range p i hp).mpr h
    subst i
    exact ⟨⟨j,v⟩,rfl⟩

def linkIndex (p : Fin (k+1)) : Fin (p.val-1) ↪ Fin k where
  toFun i := ⟨i.val,by have hi := i.isLt; have hp := p.isLt; omega⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun i : Fin k => i.val) h)

theorem linkIndex_range (p : Fin (k+1)) (i : Fin k) :
    (∃j,linkIndex p j=i) ↔ i.val+1<p.val := by
  constructor
  · rintro ⟨j,rfl⟩
    have hj := j.isLt
    change j.val+1<p.val
    omega
  · intro h
    exact ⟨⟨i.val,by omega⟩,rfl⟩

/-- Embed the forward one-left-cap prefix on its original physical labels. -/
def embed (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) :
    Network.Embed (MixedCappedPrefix.network (prefixTiles T p hp)) (capped T) where
  φ := Sum.map (tileEmbedding T p hp Kind.Vertex) (fun _ => false)
  ψ := Sum.map (Sum.map (tileEmbedding T p hp Kind.Edge) (Prod.map (linkIndex p) id)) Sum.inl
  φ_inj := Sum.map_injective.mpr ⟨(tileEmbedding T p hp Kind.Vertex).injective,
    fun _ _ _ => Subsingleton.elim _ _⟩
  ψ_inj := Sum.map_injective.mpr ⟨Sum.map_injective.mpr
    ⟨(tileEmbedding T p hp Kind.Edge).injective,fun x y h =>
      Prod.ext ((linkIndex p).injective (congrArg Prod.fst h))
        (congrArg (fun z : Fin k × Bool => z.2) h)⟩,Sum.inl_injective⟩
  src e := by rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b <;> rfl
  dst e := by rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b <;> rfl

/-- The image is the literal inside label set, with all other vertices left as ambient isolates. -/
theorem embed_image (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) (e : CappedEdge T) :
    (embed T p hp).image e ↔ (capped T).inside (before T p) e := by
  rcases e with (e | ⟨i,b⟩) | (b | b)
  · simpa [Network.Embed.image,embed,Network.inside,capped,cappedSrc,cappedDst,
      chain,chainSrc,chainDst,before] using tileEmbedding_range T p hp Kind.Edge e
  · simpa [Network.Embed.image,embed,Network.inside,capped,cappedSrc,cappedDst,
      chain,chainSrc,chainDst,before,right,left,Prod.exists,Prod.map,Prod.mk.injEq,
      Fin.coe_castSucc,Fin.val_succ] using (show (∃j,linkIndex p j=i) ↔
        i.val<p.val ∧ i.val+1<p.val from by rw [linkIndex_range]; omega)
  · simp [Network.Embed.image,embed,Network.inside,capped,cappedSrc,cappedDst,before,left,hp]
  · simp [Network.Embed.image,embed,Network.inside,capped,cappedSrc,cappedDst,before]

/-- The nonempty literal prefix has exactly its tile weight as rank. -/
theorem inside_rank (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) :
    networkRank ((capped T).sub ((capped T).inside (before T p)))=weight (prefixTiles T p hp) := by
  have h := (embed T p hp).networkRank_eq_sub
  have he : (embed T p hp).image=(capped T).inside (before T p) :=
    funext fun e => propext (embed_image T p hp e)
  rw [he] at h
  exact h.symm.trans (MixedCappedPrefix.rank (prefixTiles T p hp))

theorem prefix_weight (T : Fin (k+1) → Kind) (p : Fin (k+1)) (hp : 0<p.val) :
    weight (prefixTiles T p hp)=∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => i.val<p.val),
      (T i).weight := by
  classical
  unfold weight
  apply Finset.sum_bij (fun i _ => prefixIndex p hp i)
  · intro i _
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by have hi := i.isLt; change i.val<p.val; omega⟩
  · intro i _ j _ hij
    exact prefixIndex_injective p hp hij
  · intro i hi
    obtain ⟨j,hj⟩ := (prefixIndex_range p i hp).mpr (Finset.mem_filter.mp hi).2
    exact ⟨j,Finset.mem_univ _,hj⟩
  · intro i _
    rfl

/-- Before the first tile, the literal prefix has no physical labels and rank zero. -/
theorem empty_inside_rank (T : Fin (k+1) → Kind) :
    networkRank ((capped T).sub ((capped T).inside (before T 0)))=0 := by
  by_contra h
  obtain ⟨z,hz⟩ := ((capped T).sub ((capped T).inside (before T 0))).exists_isCycleWord_of_rank_pos
    (Nat.pos_of_ne_zero h)
  apply hz.1
  funext ⟨e,he⟩
  exfalso
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | (b | b) <;>
    simp [Network.inside,before,capped,cappedSrc,cappedDst,chain,chainSrc,chainDst,left,right] at he

/-- The literal prefix rank is the preceding weight, including the empty prefix. -/
theorem inside_rank_sum (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    networkRank ((capped T).sub ((capped T).inside (before T p)))=
      ∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => i.val<p.val), (T i).weight := by
  by_cases hp : p.val=0
  · have h : p=0 := Fin.ext hp
    subst p
    rw [empty_inside_rank]
    simp
  · rw [inside_rank T p (Nat.pos_of_ne_zero hp),prefix_weight]

/-- Every original pair of prefix endpoints obeys the preceding-weight bound. -/
theorem inside_numPaths_le (T : Fin (k+1) → Kind) (p : Fin (k+1)) (s t : CappedVertex T) :
    ((capped T).sub ((capped T).inside (before T p))).numPaths s t≤
      2^(∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => i.val<p.val), (T i).weight) := by
  have h := ((capped T).sub ((capped T).inside (before T p))).numPaths_le_two_pow s t
  rw [inside_rank_sum] at h
  exact h

/-- The same bound permits the single zero-length route when the endpoints coincide. -/
theorem inside_route_le (T : Fin (k+1) → Kind) (p : Fin (k+1)) (s t : CappedVertex T) :
    (if s=t then 1 else ((capped T).sub ((capped T).inside (before T p))).numPaths s t)≤
      2^(∑ i ∈ Finset.univ.filter (fun i : Fin (k+1) => i.val<p.val), (T i).weight) := by
  split
  · have h : 0<(2 : ℕ)^(∑ i ∈ Finset.univ.filter
        (fun i : Fin (k+1) => i.val<p.val), (T i).weight) := pow_pos (by decide) _
    omega
  · exact inside_numPaths_le T p s t

end Erdos1016.ExactMaximumSupport.MixedCappedPrefixEmbed

import Erdos1016.Cleanup.Root.ProtectedExteriorComponents

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ProtectedComponentGrowth

open SimpleGraph
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ProtectedExteriorComponents

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adding vertices to an induced subgraph increases its component count by
at most the number of added vertices. Components that already meet the old
set inject into its component set; every other component can be charged to a
new vertex. -/
theorem inducedComponentCount_le_old_plus_new
    (J : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S) :
    Fintype.card (J.induce (↑S : Set V)).ConnectedComponent ≤
      Fintype.card (J.induce (↑A : Set V)).ConnectedComponent + (S \ A).card := by
  classical
  let KS := J.induce (↑S : Set V)
  let KA := J.induce (↑A : Set V)
  letI : Fintype KS.ConnectedComponent := SetLike.instFintype
  letI : Fintype KA.ConnectedComponent := SetLike.instFintype
  let incl : KA →g KS := {
    toFun := fun v => ⟨v.1, hAS v.2⟩
    map_rel' := by intro _ _ hadj; exact hadj }
  let hasOld (c : KS.ConnectedComponent) : Prop :=
    ∃ v : {x : V // x ∈ (↑S : Set V)}, v ∈ c.supp ∧ v.1 ∈ A
  let oldVertex (c : KS.ConnectedComponent) : {x : V // x ∈ (↑S : Set V)} :=
    if h : hasOld c then Classical.choose h else Classical.choose c.nonempty_supp
  have oldVertex_mem (c : KS.ConnectedComponent) : oldVertex c ∈ c.supp := by
    dsimp [oldVertex]
    split
    · exact (Classical.choose_spec (show hasOld c from by assumption)).1
    · exact Classical.choose_spec c.nonempty_supp
  let code (c : KS.ConnectedComponent) :
      KA.ConnectedComponent ⊕ {v : V // v ∈ S \ A} := by
    by_cases h : hasOld c
    · let v := Classical.choose h
      let a : {x : V // x ∈ (↑A : Set V)} := ⟨v.1, (Classical.choose_spec h).2⟩
      exact Sum.inl (KA.connectedComponentMk a)
    · let v := Classical.choose c.nonempty_supp
      have hvA : v.1 ∉ A := by
        intro hvA
        apply h
        exact ⟨v, Classical.choose_spec c.nonempty_supp, hvA⟩
      exact Sum.inr ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hvA⟩⟩
  have hcode_inj : Function.Injective code := by
    intro c d hcd
    by_cases hc : hasOld c <;> by_cases hd : hasOld d
    · have hsum :
        (KA.connectedComponentMk
          ⟨(Classical.choose hc).1, (Classical.choose_spec hc).2⟩ :
            KA.ConnectedComponent) =
        KA.connectedComponentMk
          ⟨(Classical.choose hd).1, (Classical.choose_spec hd).2⟩ := by
        simpa [code, hc, hd] using hcd
      have hreachA : KA.Reachable
          ⟨(Classical.choose hc).1, (Classical.choose_spec hc).2⟩
          ⟨(Classical.choose hd).1, (Classical.choose_spec hd).2⟩ :=
        SimpleGraph.ConnectedComponent.exact hsum
      obtain ⟨p⟩ := hreachA
      let ac : {x : V // x ∈ (↑A : Set V)} :=
        ⟨(Classical.choose hc).1, (Classical.choose_spec hc).2⟩
      let ad : {x : V // x ∈ (↑A : Set V)} :=
        ⟨(Classical.choose hd).1, (Classical.choose_spec hd).2⟩
      have hreachS : KS.Reachable (incl ac) (incl ad) := (p.map incl).reachable
      have hcv : KS.connectedComponentMk (oldVertex c) = c :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c (oldVertex c)).mp
          (oldVertex_mem c)
      have hdv : KS.connectedComponentMk (oldVertex d) = d :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff d (oldVertex d)).mp
          (oldVertex_mem d)
      have hcx : oldVertex c = incl ac := by
        apply Subtype.ext
        change (oldVertex c).1 = (incl ac).1
        unfold oldVertex
        rw [dif_pos hc]
        rfl
      have hdx : oldVertex d = incl ad := by
        apply Subtype.ext
        change (oldVertex d).1 = (incl ad).1
        unfold oldVertex
        rw [dif_pos hd]
        rfl
      have hcc : KS.connectedComponentMk (oldVertex c) =
          KS.connectedComponentMk (oldVertex d) := by
        rw [hcx, hdx]
        exact SimpleGraph.ConnectedComponent.sound hreachS
      exact hcv.symm.trans (hcc.trans hdv)
    · have : False := by
        have hsum := congrArg (fun x => x.isLeft) hcd
        simpa [code, hc, hd] using hsum
      exact this.elim
    · have : False := by
        have hsum := congrArg (fun x => x.isLeft) hcd
        simpa [code, hc, hd] using hsum
      exact this.elim
    · have hval := congrArg (fun x => x.getRight?) hcd
      have hv :
        Classical.choose c.nonempty_supp = Classical.choose d.nonempty_supp := by
        apply Subtype.ext
        simpa [code, hc, hd] using hval
      have hcv : KS.connectedComponentMk (Classical.choose c.nonempty_supp) = c :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c
          (Classical.choose c.nonempty_supp)).mp (Classical.choose_spec c.nonempty_supp)
      have hdv : KS.connectedComponentMk (Classical.choose d.nonempty_supp) = d :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff d
          (Classical.choose d.nonempty_supp)).mp (Classical.choose_spec d.nonempty_supp)
      rw [← hcv, ← hdv, hv]
  have hcard := Fintype.card_le_of_injective code hcode_inj
  have hsum : Fintype.card (KA.ConnectedComponent ⊕ {v : V // v ∈ S \ A}) =
      Fintype.card KA.ConnectedComponent + (S \ A).card := by
    have hnew : Fintype.card {v : V // v ∈ S \ A} = (S \ A).card := by
      simpa [Finset.mem_sdiff] using (Fintype.card_coe (S \ A))
    rw [Fintype.card_sum]
    rw [hnew]
  calc
    Fintype.card (J.induce (↑S : Set V)).ConnectedComponent ≤
        Fintype.card (KA.ConnectedComponent ⊕ {v : V // v ∈ S \ A}) := by
      simpa [KS] using hcard
    _ = Fintype.card (J.induce (↑A : Set V)).ConnectedComponent + (S \ A).card := by
      simpa [KA] using hsum

/-- Adding edges to a graph cannot increase the number of components on a
fixed vertex set. -/
theorem inducedComponentCount_le_of_adjacency_mono
    (J K : SimpleGraph V) (S : Finset V)
    (hAdj : ∀ u v, K.Adj u v → J.Adj u v) :
    Fintype.card (J.induce (↑S : Set V)).ConnectedComponent ≤
      Fintype.card (K.induce (↑S : Set V)).ConnectedComponent := by
  classical
  let JJ := J.induce (↑S : Set V)
  let KK := K.induce (↑S : Set V)
  letI : Fintype JJ.ConnectedComponent := SetLike.instFintype
  letI : Fintype KK.ConnectedComponent := SetLike.instFintype
  let incl : KK →g JJ := {
    toFun := fun v => v
    map_rel' := by
      intro u v hadj
      exact hAdj u.1 v.1 hadj }
  let rep (c : JJ.ConnectedComponent) : {v : V // v ∈ (↑S : Set V)} :=
    Classical.choose c.nonempty_supp
  have hrep (c : JJ.ConnectedComponent) : rep c ∈ c.supp :=
    Classical.choose_spec c.nonempty_supp
  let f (c : JJ.ConnectedComponent) : KK.ConnectedComponent :=
    KK.connectedComponentMk (rep c)
  have hf : Function.Injective f := by
    intro c d hcd
    have hreachK : KK.Reachable (rep c) (rep d) :=
      SimpleGraph.ConnectedComponent.exact (by simpa [f] using hcd)
    obtain ⟨p⟩ := hreachK
    have hreachJ : JJ.Reachable (incl (rep c)) (incl (rep d)) :=
      (p.map incl).reachable
    have hceq : JJ.connectedComponentMk (rep c) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (rep c)).mp (hrep c)
    have hdeq : JJ.connectedComponentMk (rep d) = d :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff d (rep d)).mp (hrep d)
    have hcd' : JJ.connectedComponentMk (rep c) = JJ.connectedComponentMk (rep d) :=
      SimpleGraph.ConnectedComponent.sound (by simpa [incl] using hreachJ)
    exact hceq.symm.trans (hcd'.trans hdeq)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [JJ, KK] using hcard

/-- Combining the two monotonicity principles: adding new vertices and then
adding edges increases the component count by at most the number of new
vertices. -/
theorem inducedComponentCount_le_subgraph_plus_new
    (J K : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S)
    (hAdj : ∀ u v, K.Adj u v → J.Adj u v) :
    Fintype.card (J.induce (↑S : Set V)).ConnectedComponent ≤
      Fintype.card (K.induce (↑A : Set V)).ConnectedComponent + (S \ A).card := by
  calc
    Fintype.card (J.induce (↑S : Set V)).ConnectedComponent ≤
        Fintype.card (J.induce (↑A : Set V)).ConnectedComponent + (S \ A).card :=
      inducedComponentCount_le_old_plus_new J A S hAS
    _ ≤ Fintype.card (K.induce (↑A : Set V)).ConnectedComponent + (S \ A).card := by
      exact Nat.add_le_add_right
        (inducedComponentCount_le_of_adjacency_mono J K A hAdj) _

/-- Section 10's component-count mechanism in one theorem. If the root is one
whole component outside a protected set P, then the actual exterior has at
most the number of old-subgraph components on A plus one for every added
protected vertex. -/
theorem exteriorComponentCount_le_subgraph_plus_new_of_outside_component
    (Γ : Erdos1016.FiniteMultiGraph)
    (K : SimpleGraph Γ.Vertex) (A P : Finset Γ.Vertex)
    (hAP : A ⊆ P) (hAdj : ∀ u v, K.Adj u v → Γ.toSimpleGraph.Adj u v)
    (hconn : Γ.toSimpleGraph.Connected)
    (c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent) :
    exteriorComponentCount Γ (componentVertexSet Γ.toSimpleGraph P c) ≤
      Fintype.card (K.induce (↑A : Set Γ.Vertex)).ConnectedComponent + (P \ A).card := by
  calc
    exteriorComponentCount Γ (componentVertexSet Γ.toSimpleGraph P c) ≤
        Fintype.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent := by
      exact exteriorComponentCount_le_protected_of_outside_component Γ P hconn c
    _ ≤ Fintype.card (K.induce (↑A : Set Γ.Vertex)).ConnectedComponent + (P \ A).card :=
      inducedComponentCount_le_subgraph_plus_new Γ.toSimpleGraph K A P hAP hAdj

/-- If every protected vertex not already in A belongs to B or C, their
number is at most `|B| + |C|`. -/
theorem sdiff_card_le_two_sets
    (A P B C : Finset V) (hP : P ⊆ A ∪ B ∪ C) :
    (P \ A).card ≤ B.card + C.card := by
  have hsub : P \ A ⊆ B ∪ C := by
    intro v hv
    have hvP := (Finset.mem_sdiff.mp hv).1
    have hvA := (Finset.mem_sdiff.mp hv).2
    rcases Finset.mem_union.mp (hP hvP) with h | h
    · rcases Finset.mem_union.mp h with hA | hB
      · exact (hvA hA).elim
      · exact Finset.mem_union.mpr (Or.inl hB)
    · exact Finset.mem_union.mpr (Or.inr h)
  calc
    (P \ A).card ≤ (B ∪ C).card := Finset.card_le_card hsub
    _ ≤ B.card + C.card := Finset.card_union_le B C

/-- A quantitative form of the Section 10 exterior-component estimate. The
old protected set A is counted by a subgraph component bound; each additional
vertex is charged to B or C. -/
theorem exteriorComponentCount_le_core_plus_two_sets_of_outside_component
    (Γ : Erdos1016.FiniteMultiGraph) (K : SimpleGraph Γ.Vertex)
    (A P B C : Finset Γ.Vertex) (hAP : A ⊆ P)
    (hP : P ⊆ A ∪ B ∪ C)
    (hAdj : ∀ u v, K.Adj u v → Γ.toSimpleGraph.Adj u v)
    {n : ℕ}
    (hcore : Fintype.card (K.induce (↑A : Set Γ.Vertex)).ConnectedComponent ≤ n)
    (hconn : Γ.toSimpleGraph.Connected)
    (c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent) :
    exteriorComponentCount Γ (componentVertexSet Γ.toSimpleGraph P c) ≤
      n + B.card + C.card := by
  have hdiff := sdiff_card_le_two_sets A P B C hP
  calc
    exteriorComponentCount Γ (componentVertexSet Γ.toSimpleGraph P c) ≤
        Fintype.card (K.induce (↑A : Set Γ.Vertex)).ConnectedComponent + (P \ A).card :=
      exteriorComponentCount_le_subgraph_plus_new_of_outside_component
        Γ K A P hAP hAdj hconn c
    _ ≤ n + B.card + C.card := by omega

/-- The cardinality bookkeeping in the final cleanup paragraph turns the
linear witness/bad-vertex counts and the quadratic paired-vertex count into
the stated quadratic exterior bound. -/
theorem cleanupExteriorCount_le_quadratic
    (R B₃ m₂ Cext n b p c : ℕ)
    (hR : 1 ≤ R) (hC : 5 + B₃ + 2 * m₂ ≤ Cext)
    (hn : n < 5 * R) (hb : b < B₃ * R)
    (hp : p < 2 * m₂ * R ^ 2)
    (hc : c ≤ n + b + p) :
    c ≤ Cext * R ^ 2 := by
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have hn' : n ≤ 5 * R ^ 2 := by
    have hmul := Nat.mul_le_mul_left 5 hR2
    omega
  have hb' : b ≤ B₃ * R ^ 2 := by
    have hmul := Nat.mul_le_mul_left B₃ hR2
    omega
  have hp' : p ≤ 2 * m₂ * R ^ 2 := by omega
  have htotal : n + b + p ≤ (5 + B₃ + 2 * m₂) * R ^ 2 := by
    calc
      n + b + p ≤ 5 * R ^ 2 + B₃ * R ^ 2 + 2 * m₂ * R ^ 2 := by omega
      _ = (5 + B₃ + 2 * m₂) * R ^ 2 := by ring
  exact hc.trans (htotal.trans (Nat.mul_le_mul_right _ hC))

end Erdos1016.Proof.ProtectedComponentGrowth

end

import Erdos1016.Cleanup.Root.PortExpansion
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpansionDegree

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PortExpansion

abbrev SourceIncidence (M : FiniteMultiGraph) (v : M.Vertex) :=
  {e : M.Edge // M.src e = v}
abbrev TargetIncidence (M : FiniteMultiGraph) (v : M.Vertex) :=
  {e : M.Edge // M.dst e = v}
abbrev Incidence (M : FiniteMultiGraph) (v : M.Vertex) :=
  SourceIncidence M v ⊕ TargetIncidence M v

private def sourceTag (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S)
    (e : SourceIncidence M v) : PortEdgeType M S := by
  classical
  have hs : M.src e.1 ∈ S := by rw [e.2]; exact hv
  by_cases hd : M.dst e.1 ∈ S
  · exact .inl ⟨e.1, hs, hd⟩
  · have hne : M.src e.1 ≠ M.dst e.1 := by
      intro h
      exact hd (h ▸ hs)
    have hnot : ¬ (M.src e.1 ∈ S ∧ M.dst e.1 ∈ S) := fun h => hd h.2
    exact .inr (.inl (⟨e.1, hne, hnot⟩, false))

private def targetTag (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S)
    (e : TargetIncidence M v) : PortEdgeType M S := by
  classical
  have hd : M.dst e.1 ∈ S := by rw [e.2]; exact hv
  by_cases hs : M.src e.1 ∈ S
  · exact .inl ⟨e.1, hs, hd⟩
  · have hne : M.src e.1 ≠ M.dst e.1 := by
      intro h
      exact hs (h.symm ▸ hd)
    have hnot : ¬ (M.src e.1 ∈ S ∧ M.dst e.1 ∈ S) := fun h => hs h.1
    exact .inr (.inl (⟨e.1, hne, hnot⟩, true))

private def incidenceTag (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    Incidence M v → PortEdgeType M S
  | .inl e => sourceTag M S hroot hv e
  | .inr e => targetTag M S hroot hv e

theorem incidenceTag_incident (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S)
    (a : Incidence M v) :
    (graph M S hroot).src (edgeEquiv M S (incidenceTag M S hroot hv a)) = oldVertex M S v ∨
    (graph M S hroot).dst (edgeEquiv M S (incidenceTag M S hroot hv a)) = oldVertex M S v := by
  cases a with
  | inl e =>
    have hs : M.src e.1 ∈ S := by rw [e.2]; exact hv
    by_cases hd : M.dst e.1 ∈ S
    · left
      simp only [incidenceTag, sourceTag, dif_pos hd]
      rw [src_internalEdge]
      exact congrArg (oldVertex M S) e.2
    · left
      simp only [incidenceTag, sourceTag, dif_neg hd]
      rw [src_portEdge_false]
      exact congrArg (oldVertex M S) e.2
  | inr e =>
    have hd : M.dst e.1 ∈ S := by rw [e.2]; exact hv
    by_cases hs : M.src e.1 ∈ S
    · right
      simp only [incidenceTag, targetTag, dif_pos hs]
      rw [dst_internalEdge]
      exact congrArg (oldVertex M S) e.2
    · left
      simp only [incidenceTag, targetTag, dif_neg hs]
      rw [src_portEdge_true]
      exact congrArg (oldVertex M S) e.2

def incidenceMap (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    Incidence M v → {i : (graph M S hroot).Edge //
      (graph M S hroot).incident i (oldVertex M S v)} := by
  intro a
  refine ⟨edgeEquiv M S (incidenceTag M S hroot hv a), ?_⟩
  rcases incidenceTag_incident M S hroot hv a with hs | hd
  · exact Or.inl hs
  · exact Or.inr hd


theorem incidenceTag_injective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    Function.Injective (incidenceTag M S hroot hv) := by
  intro a b hab
  cases a with
  | inl e =>
    cases b with
    | inl f =>
      by_cases hd₁ : M.dst e.1 ∈ S <;> by_cases hd₂ : M.dst f.1 ∈ S <;>
        simp_all [incidenceTag, sourceTag, Subtype.ext_iff]
    | inr f =>
      by_cases hd₁ : M.dst e.1 ∈ S
      · by_cases hs₂ : M.src f.1 ∈ S
        · simp only [incidenceTag, sourceTag, targetTag, dif_pos hd₁, dif_pos hs₂] at hab
          have hsrc : M.src e.1 ∈ S := by rw [e.2]; exact hv
          have hdstF : M.dst f.1 ∈ S := by rw [f.2]; exact hv
          have hp : (⟨e.1, hsrc, hd₁⟩ : InternalEdge M S) =
              ⟨f.1, hs₂, hdstF⟩ := Sum.inl.inj hab
          have hval : e.1 = f.1 := congrArg Subtype.val hp
          have hdstEq : M.dst e.1 = v := by
            calc M.dst e.1 = M.dst f.1 := congrArg M.dst hval
              _ = v := f.2
          have hdst : M.dst e.1 ∈ S := by rw [hdstEq]; exact hv
          have hloop : M.src e.1 = M.dst e.1 := e.2.trans hdstEq.symm
          exact (hroot.2.1 e.1 hsrc hdst hloop).elim
        · simp [incidenceTag, sourceTag, targetTag, hd₁, hs₂] at hab
      · by_cases hs₂ : M.src f.1 ∈ S <;>
          simp [incidenceTag, sourceTag, targetTag, hd₁, hs₂] at hab
  | inr e =>
    cases b with
    | inl f =>
      by_cases hs₁ : M.src e.1 ∈ S
      · by_cases hd₂ : M.dst f.1 ∈ S
        · simp only [incidenceTag, sourceTag, targetTag, dif_pos hs₁, dif_pos hd₂] at hab
          have hsrcF : M.src f.1 ∈ S := by rw [f.2]; exact hv
          have hdst : M.dst e.1 ∈ S := by rw [e.2]; exact hv
          have hp : (⟨e.1, hs₁, hdst⟩ : InternalEdge M S) =
              ⟨f.1, hsrcF, hd₂⟩ := Sum.inl.inj hab
          have hval : e.1 = f.1 := congrArg Subtype.val hp
          have hsrcEq : M.src e.1 = v := by
            calc M.src e.1 = M.src f.1 := congrArg M.src hval
              _ = v := f.2
          have hsrc : M.src e.1 ∈ S := by rw [hsrcEq]; exact hv
          have hloop : M.src e.1 = M.dst e.1 := hsrcEq.trans e.2.symm
          exact (hroot.2.1 e.1 hsrc hdst hloop).elim
        · simp [incidenceTag, sourceTag, targetTag, hs₁, hd₂] at hab
      · by_cases hd₂ : M.dst f.1 ∈ S <;>
          simp [incidenceTag, sourceTag, targetTag, hs₁, hd₂] at hab
    | inr f =>
      by_cases hs₁ : M.src e.1 ∈ S <;> by_cases hs₂ : M.src f.1 ∈ S <;>
        simp_all [incidenceTag, targetTag, Subtype.ext_iff]

theorem incidenceMap_injective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    Function.Injective (incidenceMap M S hroot hv) := by
  intro a b hab
  apply incidenceTag_injective M S hroot hv
  apply (edgeEquiv M S).injective
  exact congrArg Subtype.val hab

private theorem oldVertex_eq_iff (M : FiniteMultiGraph) (S : Finset M.Vertex)
    {u v : M.Vertex} : oldVertex M S u = oldVertex M S v ↔ u = v := by
  constructor
  · intro h
    have ht := (vertexEquiv M S).injective h
    exact Sum.inl.inj ht
  · intro h
    cases h
    rfl

private theorem port_ne_oldVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) (p : PortEdge M S) :
    portVertex M S p ≠ oldVertex M S v := by
  intro h
  have ht := (vertexEquiv M S).injective h
  cases ht

private theorem loopVertex_ne_oldVertex (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S)
    (l : ExteriorLoop M S) (j : Fin 2) :
    loopVertex M S l j ≠ oldVertex M S v := by
  intro h
  have ht := (vertexEquiv M S).injective h
  cases ht

theorem incidenceMap_surjective (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    Function.Surjective (incidenceMap M S hroot hv) := by
  classical
  intro z
  rcases z with ⟨i, hi⟩
  cases hdecode : (edgeEquiv M S).symm i with
  | inl e =>
      have hlabel : edgeEquiv M S (.inl e) = i := by
        have h := (edgeEquiv M S).apply_symm_apply i
        simpa [hdecode] using h
      rw [← hlabel] at hi
      rcases hi with hs | hd
      · have hs' : (graph M S hroot).src (edgeEquiv M S (.inl e)) =
            oldVertex M S (M.src e.1) := src_internalEdge M S hroot e
        rw [hs'] at hs
        have he : M.src e.1 = v := (oldVertex_eq_iff M S).mp hs
        let a : Incidence M v := .inl ⟨e.1, he⟩
        have htag : incidenceTag M S hroot hv a = .inl e := by
          simp [a, incidenceTag, sourceTag, he, e.2.2]
        refine ⟨a, ?_⟩
        apply Subtype.ext
        change edgeEquiv M S (incidenceTag M S hroot hv a) = i
        rw [← hlabel, htag]
      · have hd' : (graph M S hroot).dst (edgeEquiv M S (.inl e)) =
            oldVertex M S (M.dst e.1) := dst_internalEdge M S hroot e
        rw [hd'] at hd
        have he : M.dst e.1 = v := (oldVertex_eq_iff M S).mp hd
        let a : Incidence M v := .inr ⟨e.1, he⟩
        have htag : incidenceTag M S hroot hv a = .inl e := by
          simp [a, incidenceTag, targetTag, he, e.2.1]
        refine ⟨a, ?_⟩
        apply Subtype.ext
        change edgeEquiv M S (incidenceTag M S hroot hv a) = i
        rw [← hlabel, htag]
  | inr e =>
      cases e with
      | inl e =>
          rcases e with ⟨p, side⟩
          have hlabel : edgeEquiv M S (.inr (.inl (p, side))) = i := by
            have h := (edgeEquiv M S).apply_symm_apply i
            simpa [hdecode] using h
          rw [← hlabel] at hi
          have hport : portVertex M S p ≠ oldVertex M S v :=
            port_ne_oldVertex M S hroot hv p
          cases side with
          | false =>
              rcases hi with hs | hd
              · have hs' : (graph M S hroot).src
                    (edgeEquiv M S (.inr (.inl (p, false)))) =
                    oldVertex M S (M.src p.1) := src_portEdge_false M S hroot p
                rw [hs'] at hs
                have he : M.src p.1 = v := (oldVertex_eq_iff M S).mp hs
                have hsrc : M.src p.1 ∈ S := by rw [he]; exact hv
                have hout : M.dst p.1 ∉ S := by
                  intro hdst
                  exact p.2.2 ⟨hsrc, hdst⟩
                let a : Incidence M v := .inl ⟨p.1, he⟩
                have htag : incidenceTag M S hroot hv a = .inr (.inl (p, false)) := by
                  simp [a, incidenceTag, sourceTag, hsrc, hout]
                refine ⟨a, ?_⟩
                apply Subtype.ext
                change edgeEquiv M S (incidenceTag M S hroot hv a) = i
                rw [← hlabel, htag]
              · have hd' : (graph M S hroot).dst
                    (edgeEquiv M S (.inr (.inl (p, false)))) = portVertex M S p :=
                    dst_portEdge M S hroot p false
                rw [hd'] at hd
                exact (hport hd).elim
          | true =>
              rcases hi with hs | hd
              · have hs' : (graph M S hroot).src
                    (edgeEquiv M S (.inr (.inl (p, true)))) =
                    oldVertex M S (M.dst p.1) := src_portEdge_true M S hroot p
                rw [hs'] at hs
                have he : M.dst p.1 = v := (oldVertex_eq_iff M S).mp hs
                have hdst : M.dst p.1 ∈ S := by rw [he]; exact hv
                have hout : M.src p.1 ∉ S := by
                  intro hsrc
                  exact p.2.2 ⟨hsrc, hdst⟩
                let a : Incidence M v := .inr ⟨p.1, he⟩
                have htag : incidenceTag M S hroot hv a = .inr (.inl (p, true)) := by
                  simp [a, incidenceTag, targetTag, hdst, hout]
                refine ⟨a, ?_⟩
                apply Subtype.ext
                change edgeEquiv M S (incidenceTag M S hroot hv a) = i
                rw [← hlabel, htag]
              · have hd' : (graph M S hroot).dst
                    (edgeEquiv M S (.inr (.inl (p, true)))) = portVertex M S p :=
                    dst_portEdge M S hroot p true
                rw [hd'] at hd
                exact (hport hd).elim
      | inr e =>
          rcases e with ⟨l, k⟩
          have hlabel : edgeEquiv M S (.inr (.inr (l, k))) = i := by
            have h := (edgeEquiv M S).apply_symm_apply i
            simpa [hdecode] using h
          rw [← hlabel] at hi
          fin_cases k
          · rcases hi with hs | hd
            · have hs' : oldVertex M S (M.src l.1) = oldVertex M S v := by
                exact (src_exteriorLoop_zero M S hroot l).symm.trans hs
              have he := (oldVertex_eq_iff M S).mp hs'
              have hsrc : M.src l.1 ∈ S := by rw [he]; exact hv
              exact (l.2.2 hsrc).elim
            · have hd' : loopVertex M S l 0 = oldVertex M S v := by
                exact (dst_exteriorLoop_zero M S hroot l).symm.trans hd
              exact (loopVertex_ne_oldVertex M S hroot hv l 0 hd').elim
          · rcases hi with hs | hd
            · have hs' : loopVertex M S l 0 = oldVertex M S v := by
                exact (src_exteriorLoop_one M S hroot l).symm.trans hs
              exact (loopVertex_ne_oldVertex M S hroot hv l 0 hs').elim
            · have hd' : loopVertex M S l 1 = oldVertex M S v := by
                exact (dst_exteriorLoop_one M S hroot l).symm.trans hd
              exact (loopVertex_ne_oldVertex M S hroot hv l 1 hd').elim
          · rcases hi with hs | hd
            · have hs' : loopVertex M S l 1 = oldVertex M S v := by
                exact (src_exteriorLoop_two M S hroot l).symm.trans hs
              exact (loopVertex_ne_oldVertex M S hroot hv l 1 hs').elim
            · have hd' : oldVertex M S (M.dst l.1) = oldVertex M S v := by
                exact (dst_exteriorLoop_two M S hroot l).symm.trans hd
              have he := (oldVertex_eq_iff M S).mp hd'
              have hsrc : M.src l.1 ∈ S := by
                rw [l.2.1, he]
                exact hv
              exact (l.2.2 hsrc).elim

theorem incidence_card_eq_ambientDegree (M : FiniteMultiGraph) (v : M.Vertex) :
    Fintype.card (Incidence M v) = ambientDegree M v := by
  classical
  unfold ambientDegree
  simp only [Incidence, Fintype.card_sum]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun e : M.Edge => M.src e = v)
      (by intro e; simp)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun e : M.Edge => M.dst e = v)
      (by intro e; simp)]




/-- At an old root vertex, the port expansion introduces neither extra
incidences nor fewer incidences: every physical edge at the vertex has one
unique labelled source/target incidence. -/
theorem ambientDegree_eq_expanded_degree (M : FiniteMultiGraph) (S : Finset M.Vertex)
    (hroot : IsCleanupRoot M S) {v : M.Vertex} (hv : v ∈ S) :
    ambientDegree M v = (graph M S hroot).degree (oldVertex M S v) := by
  classical
  let I := {i : (graph M S hroot).Edge //
    (graph M S hroot).incident i (oldVertex M S v)}
  have hbij : Function.Bijective (incidenceMap M S hroot hv) :=
    ⟨incidenceMap_injective M S hroot hv, incidenceMap_surjective M S hroot hv⟩
  have hequiv : Incidence M v ≃ I := Equiv.ofBijective _ hbij
  have hcard : Fintype.card I =
      (Finset.univ.filter fun i : (graph M S hroot).Edge =>
        (graph M S hroot).incident i (oldVertex M S v)).card :=
    Fintype.card_of_subtype _ (by intro i; simp)
  calc
    ambientDegree M v = Fintype.card (Incidence M v) :=
      (incidence_card_eq_ambientDegree M v).symm
    _ = Fintype.card I := Fintype.card_congr hequiv
    _ = (Finset.univ.filter fun i : (graph M S hroot).Edge =>
        (graph M S hroot).incident i (oldVertex M S v)).card := hcard
    _ = (graph M S hroot).degree (oldVertex M S v) := by
      symm
      simp [PhysicalGraph.degree, PhysicalGraph.selectedDegree]

theorem cleanup_expanded_root_degree_eq_three {G : PhysicalGraph}
    {I : CleanupInput G} (O : CleanupOutput I) {v : O.Γ.Vertex} (hv : v ∈ O.root) :
    (graph O.Γ O.root O.root_structure).degree (oldVertex O.Γ O.root v) = 3 := by
  rw [← ambientDegree_eq_expanded_degree O.Γ O.root O.root_structure hv]
  exact O.root_cubic_ambient_degree v hv



end Erdos1016.Proof.PortExpansionDegree
end

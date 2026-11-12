import Erdos1016.ExactMaximumSupport.LargeGirth.DartWords
import Erdos1016.ExactMaximumSupport.LargeGirth.MultigraphDarts
import Erdos1016.Cleanup.Compression.EndpointIncidenceBijection

set_option autoImplicit false

/-!
# Oriented dart codes of the actual corridor partition

Each oriented compressed edge expands to its recorded physical darts.
The first physical dart determines the compressed dart, including the two
orientations of a returning corridor. This is proved from disjoint supports
and edge-distinct corridor lists, not assumed as a decoding hypothesis.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.CorridorDarts

open FiniteMultiGraph Proof.PhysicalPartition Proof.SingleCorridorRoute
open Proof.CompressedRouteDecomposition Proof.PartitionRouteDecomposition
open Proof.EndpointIncidenceBijection Nonbacktracking
open Proof.PhysicalDegreeTwoCoreComponents

variable (G : PhysicalGraph)

def stepDart (s : CorridorWalks.Step G) : Dart G :=
  dartOfAdj G (CorridorWalks.adjacent G s)

@[simp] theorem stepDart_tail (s : CorridorWalks.Step G) :
    tail G (stepDart G s) = s.startVertex := tail_dartOfAdj G _

@[simp] theorem stepDart_head (s : CorridorWalks.Step G) :
    head G (stepDart G s) = s.endVertex := head_dartOfAdj G _

@[simp] theorem stepDart_edge (s : CorridorWalks.Step G) : (stepDart G s).1 = s.edge := by
  rcases s.endpoints with hs | hs
  · have he : stepDart G s = (s.edge, true) := dart_eq_of_endpoints G
      (by simpa [tail, routeGraph] using (stepDart_tail G s).trans hs.1.symm)
      (by simpa [head, routeGraph] using (stepDart_head G s).trans hs.2.symm)
    exact congrArg Prod.fst he
  · have he : stepDart G s = (s.edge, false) := dart_eq_of_endpoints G
      (by simpa [tail, routeGraph] using (stepDart_tail G s).trans hs.1.symm)
      (by simpa [head, routeGraph] using (stepDart_head G s).trans hs.2.symm)
    exact congrArg Prod.fst he

theorem stepDart_next (s t : CorridorWalks.Step G)
    (hlink : s.endVertex = t.startVertex) (hne : s.edge ≠ t.edge) :
    Next G (stepDart G s) (stepDart G t) := by
  refine ⟨by simpa using hlink, ?_⟩
  intro he
  have hh := congrArg Prod.fst he
  simp only [stepDart_edge, reverse] at hh
  exact hne hh.symm

def forward (C : PhysicalCorridor G) : List (Dart G) :=
  (corridorSteps C).map (stepDart G)

@[simp] theorem forward_edges (C : PhysicalCorridor G) :
    (forward G C).map Prod.fst = C.edges := by
  simp only [forward, List.map_map, Function.comp_def, stepDart_edge]
  exact corridorSteps_edges C

theorem forward_ne_nil (C : PhysicalCorridor G) (hne : C.edges ≠ []) : forward G C ≠ [] := by
  intro he
  have hh := forward_edges G C
  rw [he] at hh
  exact hne hh.symm

@[simp] theorem forward_length (C : PhysicalCorridor G) : (forward G C).length = C.edges.length := by
  simp [forward, corridorSteps_length]

theorem forward_first_tail (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    tail G ((forward G C).head (forward_ne_nil G C hne)) = corridorStart C := by
  simp only [forward, List.head_map, stepDart_tail]
  exact Proof.DegreeTwoCorridorRoutes.corridorSteps_head_start C hne

theorem forward_last_head (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    head G ((forward G C).getLast (forward_ne_nil G C hne)) = corridorFinish C := by
  simp only [forward, List.getLast_map, stepDart_head]
  exact Proof.DegreeTwoCorridorRoutes.corridorSteps_last_end C hne

theorem forward_first_edge (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    ((forward G C).head (forward_ne_nil G C hne)).1 = C.edges.head hne := by
  have hh := congrArg (fun l : List G.Edge => l.head?) (forward_edges G C)
  simpa only [List.head?_map, List.head?_eq_head (forward_ne_nil G C hne),
    List.head?_eq_head hne, Option.map_some', Option.some.injEq] using hh

theorem forward_last_edge (C : PhysicalCorridor G) (hne : C.edges ≠ []) :
    ((forward G C).getLast (forward_ne_nil G C hne)).1 = C.edges.getLast hne := by
  have hh := congrArg (fun l : List G.Edge => l.getLast?) (forward_edges G C)
  simpa only [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (forward_ne_nil G C hne),
    List.getLast?_eq_getLast_of_ne_nil hne, Option.map_some', Option.some.injEq] using hh

theorem forward_chain (C : PhysicalCorridor G)
    (hc : List.Chain' (CorridorWalks.linked G) (corridorSteps C)) :
    List.Chain' (Next G) (forward G C) := by
  have hn : ((corridorSteps C).map PathStep.edge).Nodup := by
    rw [corridorSteps_edges]
    exact C.edges_nodup
  have hneq : List.Chain' (fun s t : CorridorWalks.Step G => s.edge ≠ t.edge)
      (corridorSteps C) := by
    apply (List.chain'_map _).1
    exact hn.chain'
  apply (List.chain'_map _).2
  rw [List.chain'_iff_get] at hc hneq ⊢
  intro i hi
  exact stepDart_next G _ _ (hc i hi) (hneq i hi)

variable {G} {P : Finset G.Vertex} {W : Finset G.Edge}
  (D : CorridorPartition G P W)
  (hne : ∀ C ∈ D.corridors, C.edges ≠ [])
  (hend : ∀ C ∈ D.corridors,
    corridorStart C ∈ protectedOrBranch G P ∧ corridorFinish C ∈ protectedOrBranch G P)

abbrev Core := compressedCorridorGraph D hend

def code (d : MultigraphDarts.Dart (Core D hend)) : List (Dart G) :=
  if d.2 then forward G (corridorAt D d.1)
  else (forward G (corridorAt D d.1)).reverse.map (reverse G)

include hne in
theorem code_ne_nil (d : MultigraphDarts.Dart (Core D hend)) : code D hend d ≠ [] := by
  have hh := forward_ne_nil G (corridorAt D d.1) (hne _ (corridorAt_mem D d.1))
  unfold code
  split <;> simp_all

@[simp] theorem code_length (d : MultigraphDarts.Dart (Core D hend)) :
    (code D hend d).length = (corridorAt D d.1).edges.length := by
  unfold code
  split <;> simp

include hne in
theorem code_chain (d : MultigraphDarts.Dart (Core D hend)) :
    List.Chain' (Next G) (code D hend d) := by
  have hc := (compressedCorridorPaths D hne hend).chain d.1
  have hf := forward_chain G (corridorAt D d.1) (hc.imp (fun _ _ h => h.1))
  unfold code
  split
  · exact hf
  · apply (List.chain'_map _).2
    apply List.chain'_reverse.2
    exact hf.imp (fun x y h => (next_reverse G x y).1 h)

theorem code_first_tail (d : MultigraphDarts.Dart (Core D hend)) :
    tail G ((code D hend d).head (code_ne_nil D hne hend d)) =
      compressedCorridorVertexMap D hend (MultigraphDarts.tail _ d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp only [code, Bool.false_eq_true, if_false, if_true,
    List.head_map, List.head_reverse, tail_reverse, MultigraphDarts.tail,
    compressedCorridor_src_image, compressedCorridor_dst_image]
  · exact forward_last_head G _ (hne _ (corridorAt_mem D e))
  · exact forward_first_tail G _ (hne _ (corridorAt_mem D e))

theorem code_last_head (d : MultigraphDarts.Dart (Core D hend)) :
    head G ((code D hend d).getLast (code_ne_nil D hne hend d)) =
      compressedCorridorVertexMap D hend (MultigraphDarts.head _ d) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp only [code, Bool.false_eq_true, if_false, if_true,
    List.getLast_map, List.getLast_reverse, head_reverse, MultigraphDarts.head,
    compressedCorridor_src_image, compressedCorridor_dst_image]
  · exact forward_first_tail G _ (hne _ (corridorAt_mem D e))
  · exact forward_last_head G _ (hne _ (corridorAt_mem D e))

theorem code_first_edge (d : MultigraphDarts.Dart (Core D hend)) :
    ((code D hend d).head (code_ne_nil D hne hend d)).1 =
      if d.2 then (corridorAt D d.1).edges.head (hne _ (corridorAt_mem D d.1))
      else (corridorAt D d.1).edges.getLast (hne _ (corridorAt_mem D d.1)) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp only [code, Bool.false_eq_true, if_false, if_true,
    List.head_map, List.head_reverse, reverse]
  · exact forward_last_edge G _ (hne _ (corridorAt_mem D e))
  · exact forward_first_edge G _ (hne _ (corridorAt_mem D e))

theorem code_first_mem (d : MultigraphDarts.Dart (Core D hend)) :
    ((code D hend d).head (code_ne_nil D hne hend d)).1 ∈
      (corridorAt D d.1).support := by
  rw [code_first_edge D hne hend d, PhysicalCorridor.support]
  apply List.mem_toFinset.mpr
  split
  · exact List.head_mem _
  · exact List.getLast_mem _

/-- Even the two orientations of a compressed loop have different first
physical darts: otherwise its edge-distinct corridor would have length one. -/
theorem code_first_injective : Function.Injective
    (fun d : MultigraphDarts.Dart (Core D hend) =>
      (code D hend d).head (code_ne_nil D hne hend d)) := by
  intro d e heq
  dsimp only at heq
  have hedge : d.1 = e.1 := by
    by_contra hn
    have hd := code_first_mem D hne hend d
    have he := code_first_mem D hne hend e
    have hdisj := (compressedCorridorRouteSystem D hne hend).disjoint hn
    exact Finset.disjoint_left.mp hdisj hd (by rw [heq]; exact he)
  have htail := congrArg (tail G) heq
  rw [code_first_tail D hne hend d, code_first_tail D hne hend e] at htail
  have hlabel := congrArg Prod.fst heq
  rw [code_first_edge D hne hend d, code_first_edge D hne hend e] at hlabel
  rcases d with ⟨d, b⟩
  rcases e with ⟨e, c⟩
  dsimp only at hedge
  subst e
  cases b <;> cases c
  · rfl
  · have hclosed : corridorStart (corridorAt D d) = corridorFinish (corridorAt D d) := by
      simpa only [MultigraphDarts.tail, Bool.false_eq_true, if_false, if_true,
        compressedCorridor_src_image, compressedCorridor_dst_image] using htail.symm
    have hfl : corridorFirstEdge (corridorAt D d) (hne _ (corridorAt_mem D d)) =
        corridorLastEdge (corridorAt D d) (hne _ (corridorAt_mem D d)) := by
      simpa only [Bool.false_eq_true, if_false, if_true, corridorFirstEdge_eq_head,
        corridorLastEdge_eq_getLast] using hlabel.symm
    exact (corridor_start_ne_finish_of_length_one _
      (corridor_first_eq_last_length_one _ _ hfl) hclosed).elim
  · have hclosed : corridorStart (corridorAt D d) = corridorFinish (corridorAt D d) := by
      simpa only [MultigraphDarts.tail, Bool.false_eq_true, if_false, if_true,
        compressedCorridor_src_image, compressedCorridor_dst_image] using htail
    have hfl : corridorFirstEdge (corridorAt D d) (hne _ (corridorAt_mem D d)) =
        corridorLastEdge (corridorAt D d) (hne _ (corridorAt_mem D d)) := by
      simpa only [Bool.false_eq_true, if_false, if_true, corridorFirstEdge_eq_head,
        corridorLastEdge_eq_getLast] using hlabel
    exact (corridor_start_ne_finish_of_length_one _
      (corridor_first_eq_last_length_one _ _ hfl) hclosed).elim
  · rfl

theorem code_reverse_first (d : MultigraphDarts.Dart (Core D hend)) :
    (code D hend (MultigraphDarts.reverse _ d)).head
        (code_ne_nil D hne hend (MultigraphDarts.reverse _ d)) =
      reverse G ((code D hend d).getLast (code_ne_nil D hne hend d)) := by
  rcases d with ⟨e, b⟩
  cases b <;> simp [code, MultigraphDarts.reverse]

theorem code_seam (d e : MultigraphDarts.Dart (Core D hend))
    (h : MultigraphDarts.Next _ d e) :
    Next G ((code D hend d).getLast (code_ne_nil D hne hend d))
      ((code D hend e).head (code_ne_nil D hne hend e)) := by
  refine ⟨?_, ?_⟩
  · rw [code_last_head D hne hend d, code_first_tail D hne hend e, h.1]
  · intro he
    rw [← code_reverse_first D hne hend d] at he
    exact h.2 (code_first_injective D hne hend he)

include hne in
/-- Concatenating actual corridor codes preserves nonbacktracking. -/
theorem codes_chain (l : List (MultigraphDarts.Dart (Core D hend)))
    (hl : List.Chain' (MultigraphDarts.Next _) l) :
    List.Chain' (Next G) (l.flatMap (code D hend)) := by
  apply DartWords.chain_flatMap (code D hend) (code_ne_nil D hne hend)
    (MultigraphDarts.Next _) (Next G) (code_chain D hne hend) ?_ l hl
  intro d e h x hx y hy
  have hxx : x = (code D hend d).getLast (code_ne_nil D hne hend d) := by
    simpa only [List.getLast?_eq_getLast_of_ne_nil (code_ne_nil D hne hend d),
      Option.mem_def, Option.some.injEq] using hx.symm
  have hyy : y = (code D hend e).head (code_ne_nil D hne hend e) := by
    simpa only [List.head?_eq_head (code_ne_nil D hne hend e),
      Option.mem_def, Option.some.injEq] using hy.symm
  subst x
  subst y
  exact code_seam D hne hend d e h

include hne in
theorem codes_injective : Function.Injective
    (List.flatMap (code D hend)) :=
  DartWords.flatMap_injective_of_head _ (code_ne_nil D hne hend)
    (code_first_injective D hne hend)

end Erdos1016.ExactMaximumSupport.LargeGirth.CorridorDarts

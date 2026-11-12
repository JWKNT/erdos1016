import Erdos1016.ExactMaximumSupport.LargeGirth.CorridorWalks

set_option autoImplicit false

/-!
# Nonbacktracking dart words and nonempty route codes

An actual physical dart word with consecutive nonbacktracking transitions
gives a reduced ordinary walk with exactly that serialization. Distinct
nonempty codes with distinct first letters remain distinct under concatenation.
These elementary adapters will be applied to oriented corridor routes.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.DartWords

open Nonbacktracking

theorem flatMap_injective_of_head {ι α : Type*} (code : ι → List α)
    (hne : ∀ i, code i ≠ [])
    (hhead : Function.Injective (fun i => (code i).head (hne i))) :
    Function.Injective (List.flatMap code) := by
  intro l
  induction l with
  | nil =>
    intro m hm
    cases m with
    | nil => rfl
    | cons i m =>
      have h : code i ++ m.flatMap code = [] := hm.symm
      exact (hne i (List.append_eq_nil_iff.mp h).1).elim
  | cons i l ih =>
    intro m hm
    cases m with
    | nil =>
      have h : code i ++ l.flatMap code = [] := hm
      exact (hne i (List.append_eq_nil_iff.mp h).1).elim
    | cons j m =>
      have hh := congrArg List.head? hm
      have hij : i = j := by
        apply hhead
        have hopt : (code i).head? = (code j).head? := by
          simpa only [List.flatMap_cons, List.head?_append_of_ne_nil _ (hne i),
            List.head?_append_of_ne_nil _ (hne j)] using hh
        simpa only [List.head?_eq_head (hne i), List.head?_eq_head (hne j),
          Option.some.injEq] using hopt
      subst j
      have htail : l.flatMap code = m.flatMap code := List.append_cancel_left hm
      exact congrArg (List.cons i) (ih htail)

theorem chain_flatMap {ι α : Type*} (code : ι → List α)
    (hne : ∀ i, code i ≠ []) (R : ι → ι → Prop) (S : α → α → Prop)
    (hinside : ∀ i, List.Chain' S (code i))
    (hseam : ∀ i j, R i j → ∀ x ∈ (code i).getLast?, ∀ y ∈ (code j).head?, S x y)
    (l : List ι) (hl : List.Chain' R l) : List.Chain' S (l.flatMap code) := by
  rw [List.flatMap_def]
  apply (List.chain'_flatten ?_).2
  · refine ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      exact hinside i
    · apply (List.chain'_map _).2
      exact hl.imp (fun i j hij => hseam i j hij)
  · intro h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp h
    exact hne i hi

variable (G : PhysicalGraph)

def finish : Dart G → List (Dart G) → G.Vertex
  | d, [] => head G d
  | _, e :: l => finish e l

def walk : (d : Dart G) → (l : List (Dart G)) → List.Chain' (Next G) (d :: l) →
    G.toSimpleGraph.Walk (tail G d) (finish G d l)
  | d, [], _ => .cons (dart_adj G d) .nil
  | d, e :: l, h => .cons (dart_adj G d)
      ((walk e l (List.chain'_cons.mp h).2).copy (List.chain'_cons.mp h).1.1.symm rfl)

@[simp] theorem walk_length (d : Dart G) (l : List (Dart G))
    (h : List.Chain' (Next G) (d :: l)) : (walk G d l h).length = l.length + 1 := by
  induction l generalizing d with
  | nil => rfl
  | cons e l ih => simp [walk, ih, Nat.add_assoc]

@[simp] theorem walk_snd (d : Dart G) (l : List (Dart G))
    (h : List.Chain' (Next G) (d :: l)) : (walk G d l h).snd = head G d := by
  cases l with
  | nil => rfl
  | cons e l => exact SimpleGraph.Walk.snd_cons _ _

@[simp] theorem walk_darts (d : Dart G) (l : List (Dart G))
    (h : List.Chain' (Next G) (d :: l)) : walkDarts G (walk G d l h) = d :: l := by
  induction l generalizing d with
  | nil => simp [walk, walkDarts]
  | cons e l ih =>
    change dartOfAdj G (dart_adj G d) ::
      walkDarts G ((walk G e l (List.chain'_cons.mp h).2).copy
        (List.chain'_cons.mp h).1.1.symm rfl) = d :: e :: l
    rw [dartOfAdj_dart_adj, walkDarts_copy, ih]

theorem walk_reduced (d : Dart G) (l : List (Dart G))
    (h : List.Chain' (Next G) (d :: l)) : ShortWalks.Reduced (walk G d l h) := by
  induction l generalizing d with
  | nil => simp [walk, ShortWalks.Reduced]
  | cons e l ih =>
    have he := (List.chain'_cons.mp h).1
    have ht := (List.chain'_cons.mp h).2
    refine ⟨(ShortWalks.reduced_copy _ _ _).2 (ih e ht), ?_⟩
    intro _ hh
    change ((walk G e l ht).copy he.1.symm rfl).snd = tail G d at hh
    rw [ShortWalks.snd_copy, walk_snd] at hh
    exact next_no_return G he hh

theorem finish_eq (d : Dart G) (l : List (Dart G)) :
    finish G d l = head G ((d :: l).getLast (List.cons_ne_nil _ _)) := by
  induction l generalizing d with
  | nil => rfl
  | cons e l ih => simpa only [finish, List.getLast_cons] using ih e

/-- A nonempty physical dart chain has an exact reduced-walk realization. -/
theorem exists_walk (l : List (Dart G)) (hne : l ≠ [])
    (hchain : List.Chain' (Next G) l) :
    ∃ p : G.toSimpleGraph.Walk (tail G (l.head hne)) (head G (l.getLast hne)),
      walkDarts G p = l ∧ p.length = l.length ∧ ShortWalks.Reduced p := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons d l =>
    refine ⟨(walk G d l hchain).copy rfl (finish_eq G d l), ?_, ?_, ?_⟩
    · simp only [walkDarts_copy, walk_darts]
    · simp
    · exact (ShortWalks.reduced_copy _ _ _).2 (walk_reduced G d l hchain)

end Erdos1016.ExactMaximumSupport.LargeGirth.DartWords

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false

namespace Erdos1016.Proof.FiniteAcyclicPathExtraction

open SimpleGraph

variable {V : Type*}

/-- In a connected acyclic finite graph, any two vertices have a unique path.
This is the path-uniqueness input for extracting a spanning path in the
maximum-degree-two case. -/
theorem existsUnique_path_of_connected_acyclic
    (H : SimpleGraph V) (hconn : H.Connected) (hacyc : H.IsAcyclic)
    (a b : V) : ∃! p : H.Walk a b, p.IsPath := by
  have htree : H.IsTree := ⟨hconn, hacyc⟩
  exact htree.existsUnique_path a b

/-- A path supplied by the tree API automatically has support in the graph's
vertex type; this packages the canonical endpoint-to-endpoint extraction. -/
theorem exists_path_of_connected_acyclic
    (H : SimpleGraph V) (hconn : H.Connected) (hacyc : H.IsAcyclic)
    (a b : V) : ∃ p : H.Walk a b, p.IsPath := by
  obtain ⟨p, hp, _⟩ := existsUnique_path_of_connected_acyclic H hconn hacyc a b
  exact ⟨p, hp⟩

end Erdos1016.Proof.FiniteAcyclicPathExtraction

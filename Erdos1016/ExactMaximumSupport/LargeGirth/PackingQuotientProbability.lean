import Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingIndependence
import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! The packing product is transported to the actual connected-fiber quotient. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient
open FiniteMultiGraph ConnectedContraction BoundaryDecay PackingLocalSpaces
local instance packingQuotientProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : FiniteMultiGraph) {ι : Type*} [Fintype ι] (X : ι → Finset G.Vertex)

def marks : Finset (graph G X).Vertex := Finset.univ.image (mark G X)

theorem marks_card : (marks G X).card=Fintype.card ι := by
  rw [marks,Finset.card_image_of_injective _ (mark_injective G X),Finset.card_univ]

theorem average_project (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected)
    (f : (graph G X).CycleSpace → ℝ) :
    average (fun x : G.CycleSpace => f (project G (label G X) x))=average f :=
  PackingIndependence.average_surjective_linear (project G (label G X))
    (project_surjective G (label G X) (connectedFibers G X hdisj hconn)) f

theorem zeroCut_iff_project_zeroStar
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (i : ι) (x : G.CycleSpace) :
    DisjointRegionCuts.ZeroCut G (X i) x ↔
      ZeroStar (graph G X) (mark G X i) (project G (label G X) x) := by
  rw [zeroStar_iff_zeroCutAt _ _ (graph_noLoops G X)]
  rw [← fiberZeroCut_eq G X hdisj i]
  exact fiberZeroCut_iff G (label G X) (Sum.inl i) x

theorem product_marks (f : (graph G X).Vertex → ℝ) :
    (∏v∈marks G X,f v)=∏i,f (mark G X i) := by
  rw [marks,Finset.prod_image]
  intro i _ j _ h
  exact mark_injective G X h

/-- The full original uniform average becomes the full quotient average. -/
theorem average_cut_product (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected) :
    average (fun x : G.CycleSpace => ∏i,PackingProduct.cutFactor G (X i) x)=
      average (fun y : (graph G X).CycleSpace =>
        ∏v∈marks G X,(1-indicator (ZeroStar (graph G X) v) y/2)) := by
  have he (x : G.CycleSpace) :
      (∏i,PackingProduct.cutFactor G (X i) x)=
      ∏v∈marks G X,(1-indicator (ZeroStar (graph G X) v) (project G (label G X) x)/2) := by
    rw [product_marks]
    apply Finset.prod_congr rfl
    intro i _
    unfold PackingProduct.cutFactor indicator
    rw [zeroCut_iff_project_zeroStar G X hdisj i x]
  simp_rw [he]
  exact average_project G X hdisj hconn (fun y : (graph G X).CycleSpace =>
    ∏v∈marks G X,(1-indicator (ZeroStar (graph G X) v) y/2))

/-- Actual cyclic regions provide the quotient product bound used in selection. -/
theorem forest_density_le_mark_product
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected)
    (hcyc : ∀i,∃z:G.internalCycleSpace (X i),z≠0)
    (E : Finset G.Edge) (hE : ∀i,G.internalEdges (X i)⊆E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1))≤
      average (fun y : (graph G X).CycleSpace =>
        ∏v∈marks G X,(1-indicator (ZeroStar (graph G X) v) y/2)) := by
  rw [← average_cut_product G X hdisj hconn]
  exact PackingProduct.forest_density_le_cut_product G X hdisj hcyc E hE

theorem region_forest_le_mark_product
    (hdisj : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hconn : ∀i,(G.toSimpleGraph.induce (↑(X i):Set G.Vertex)).Connected)
    (hcyc : ∀i,∃z:G.internalCycleSpace (X i),z≠0)
    (R : Finset G.Vertex) (hXR : ∀i,X i⊆R) :
    G.regionForestProbability R≤
      average (fun y : (graph G X).CycleSpace =>
        ∏v∈marks G X,(1-indicator (ZeroStar (graph G X) v) y/2)) := by
  rw [PoleProduct.region_density_eq]
  apply forest_density_le_mark_product G X hdisj hconn hcyc
  intro i e he
  have hh := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hXR i hh.1,hXR i hh.2⟩⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingQuotient

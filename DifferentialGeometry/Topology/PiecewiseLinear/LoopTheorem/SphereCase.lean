import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary_map
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M BdM B : Set E} (ι : X → E)
    (hB : IsPLSphere 2 B) (hBBdM : B ⊆ BdM) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N)
    (hpush : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ →
        Δ ⊆ BdM →
        ∃ D₁ : SingularTwoCell X,
          D₁.IsNonsingular ∧
          ι '' (D₁ '' D₁.domain) ⊆ M ∧
          Set.range (fun x => ι (D₁.boundary x)) = r '' stdSimplexBoundary 2 ∧
          ι '' (D₁ '' D₁.domain) ∩ BdM = r '' stdSimplexBoundary 2) :
    ∃ (D₁ : SingularTwoCell X)
        (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
      D₁.IsNonsingular ∧
      ι '' (D₁ '' D₁.domain) ⊆ M ∧
      Set.range (fun x => ι (D₁.boundary x)) =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ι '' (D₁ '' D₁.domain) ∩ BdM =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ¬loopClassMeets L₁ P₀ N := by
  have hNne : N ≠ ⊤ := by
    intro hN
    apply hL
    apply (loopClassMeets_iff_carrier_subset L P₀ N).2
    intro g hg
    rw [hN]
    exact Subgroup.mem_top g
  have hi : ∃ i, ¬loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N := by
    by_contra hi
    have hall : ∀ i,
        loopClassMeets (sphereBoundaryLoop q hB hq hDB hdisj i) P₀ N := by
      intro i
      by_contra hmeet
      exact hi ⟨i, hmeet⟩
    exact hNne (eq_top_of_boundaryLoops_mem_normal hB D q hq hDB hdisj P₀ N hall)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨D₁, hD₁, hD₁M, hD₁boundary, hD₁intersection⟩ :=
    hpush (D i) (q i) (hq i) ((hDB i).trans hBBdM)
  let L₁ := sphereBoundaryLoop q hB hq hDB hdisj i
  have hL₁range : Set.range (fun θ => (L₁ θ : E)) =
      q i '' stdSimplexBoundary 2 :=
    sphereBoundaryLoop_range q hB hq hDB hdisj i
  refine ⟨D₁, L₁, hD₁, hD₁M, ?_, ?_, hi⟩
  · exact hD₁boundary.trans hL₁range.symm
  · exact hD₁intersection.trans hL₁range.symm

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E)
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.space]
    {B : Set E} (hB : IsPLSphere 2 B)
    (hBBdM : B ⊆ (boundaryComplex 3 K).space) {k : ℕ}
    (D : Fin k → Set E) (q : Fin k → (Fin 3 → ℝ) → E)
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N)
    (hpush : ∀ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ →
        Δ ⊆ (boundaryComplex 3 K).space →
        ∃ D₁ : SingularTwoCell K.space,
          D₁.IsNonsingular ∧
          Subtype.val '' (D₁ '' D₁.domain) ⊆ K.space ∧
          Set.range (fun x => (D₁.boundary x : E)) = r '' stdSimplexBoundary 2 ∧
          Subtype.val '' (D₁ '' D₁.domain) ∩ (boundaryComplex 3 K).space =
            r '' stdSimplexBoundary 2) :
    ∃ (D₁ : SingularTwoCell K.space)
        (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
      D₁.IsNonsingular ∧
      Subtype.val '' (D₁ '' D₁.domain) ⊆ K.space ∧
      Set.range (fun x => (D₁.boundary x : E)) =
        Set.range (fun θ => (L₁ θ : E)) ∧
      Subtype.val '' (D₁ '' D₁.domain) ∩ (boundaryComplex 3 K).space =
        Set.range (fun θ => (L₁ θ : E)) ∧
      ¬loopClassMeets L₁ P₀ N :=
  exists_nonsingular_two_cell_of_sphere_boundary_map
    (M := K.space) (BdM := (boundaryComplex 3 K).space)
    (ι := (Subtype.val : K.space → E)) hB hBBdM D q hq hDB hdisj P₀ N L hL hpush

end DifferentialGeometry.Topology.PiecewiseLinear

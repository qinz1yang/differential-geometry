import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_nonsingular_two_cell_of_sphere_boundary
    {M B : Set (EuclideanSpace ℝ (Fin 3))}
    (hM : IsPolyhedralManifoldWithBoundary (n := 3) 3 M)
    (hB : IsPLSphere 2 B) (hBBdM : B ⊆ polyhedralBoundary 3 M hM) {k : ℕ}
    (D : Fin k → Set (EuclideanSpace ℝ (Fin 3)))
    (q : Fin k → (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
    (hq : ∀ i, IsPLHomeomorphOn (q i) (stdSimplex ℝ (Fin 3)) (D i))
    (hDB : ∀ i, D i ⊆ B)
    (hdisj : Pairwise (Function.onFun Disjoint D))
    [PathConnectedSpace (sphereWithDiskInteriorsRemoved B D)]
    (P₀ : sphereWithDiskInteriorsRemoved B D)
    (N : Subgroup (FundamentalGroup (sphereWithDiskInteriorsRemoved B D) P₀))
    [N.Normal]
    (L : freeLoop (sphereWithDiskInteriorsRemoved B D))
    (hL : ¬loopClassMeets L P₀ N)
    (hpush : ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3)))
        (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ →
        Δ ⊆ polyhedralBoundary 3 M hM →
        ∃ D₁ : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
          D₁.IsNonsingular ∧
          D₁ '' D₁.domain ⊆ M ∧
          Set.range D₁.boundary = r '' stdSimplexBoundary 2 ∧
          D₁ '' D₁.domain ∩ polyhedralBoundary 3 M hM = r '' stdSimplexBoundary 2) :
    ∃ (D₁ : SingularTwoCell (EuclideanSpace ℝ (Fin 3)))
        (L₁ : freeLoop (sphereWithDiskInteriorsRemoved B D)),
      D₁.IsNonsingular ∧
      D₁ '' D₁.domain ⊆ M ∧
      Set.range D₁.boundary =
        Set.range (fun θ => (L₁ θ : EuclideanSpace ℝ (Fin 3))) ∧
      D₁ '' D₁.domain ∩ polyhedralBoundary 3 M hM =
        Set.range (fun θ => (L₁ θ : EuclideanSpace ℝ (Fin 3))) ∧
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
  have hL₁range : Set.range
      (fun θ => (L₁ θ : EuclideanSpace ℝ (Fin 3))) =
        q i '' stdSimplexBoundary 2 :=
    sphereBoundaryLoop_range q hB hq hDB hdisj i
  refine ⟨D₁, L₁, hD₁, hD₁M, ?_, ?_, hi⟩
  · exact hD₁boundary.trans hL₁range.symm
  · exact hD₁intersection.trans hL₁range.symm

end DifferentialGeometry.Topology.PiecewiseLinear

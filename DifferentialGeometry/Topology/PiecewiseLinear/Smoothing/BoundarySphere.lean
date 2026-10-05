import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySphereComponent
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySurfaceEmbedding
import DifferentialGeometry.Topology.Manifold.SphereDiffeomorph

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_isSmoothEmbedding_sphere_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ d : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
      IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ d ∧ range d = range ψ := by
  obtain ⟨W, -, hWc, hWimg, ⟨h⟩⟩ := exists_opens_boundaryManifold_homeomorph_sphere ψ hψ hψbd
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.chartedSpace (I := 𝓡∂ 3)
  let _ : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
    BoundaryManifold.isManifold (I := 𝓡∂ 3)
  obtain ⟨D⟩ := h.nonempty_diffeomorph_sphere
  have _ : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  refine ⟨fun x => ((D x : BoundaryManifold (𝓡∂ 3) M) : M),
    isSmoothEmbedding_coe_of_diffeomorph_boundary_opens W D, ?_⟩
  rw [← hWimg]
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨D x, (D x).2, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨D.symm ⟨q, hq⟩, ?_⟩
    change (((D (D.symm ⟨q, hq⟩)) : BoundaryManifold (𝓡∂ 3) M) : M) = q
    rw [D.apply_symm_apply]

end DifferentialGeometry.Topology.PiecewiseLinear

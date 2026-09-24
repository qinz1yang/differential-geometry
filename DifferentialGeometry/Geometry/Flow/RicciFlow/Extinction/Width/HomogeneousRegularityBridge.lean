import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassical
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem homogeneouslyRegularMetric_of_homogeneousCoordinates
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (h : HomogeneousCoordinates (I := 𝓘(ℝ, E)) (Q := M) g 3) :
    HomogeneouslyRegularMetric g := by
  refine ⟨h.lowerBound, h.upperBound, h.lower_pos, h.lower_le_upper,
    fun p => (h.atPoint p).chart, ?_, ?_⟩
  · intro p
    exact ⟨(h.atPoint p).closedCube_subset_source, h.centered p, (h.atPoint p).smooth,
      (h.atPoint p).smooth_inverse, fun y hy ξ => h.ellipticity p y hy ξ⟩
  · intro k
    obtain ⟨C, hC0, hC⟩ := h.derivative_bounds k
    exact ⟨C, hC0, fun p i j y hy => hC p y (fun i => (hy i).le) i j⟩

end DifferentialGeometry.Geometry

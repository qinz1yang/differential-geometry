import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.HomogeneousRegularityBridge
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence

noncomputable section

open Bundle Manifold Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.PDE.RicciFlow.Extinction.Width
open DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_morrey_disk_of_homogeneousCoordinates
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hcomplete : RiemannianMetricComplete g)
    (hcoords : HomogeneousCoordinates (I := 𝓘(ℝ, E)) (Q := M) g 3)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hfinite : (spanningDiskCompetitors g γ).Nonempty) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u :=
  exists_morrey_disk g hcomplete
    (homogeneouslyRegularMetric_of_homogeneousCoordinates g hcoords) γ hγ hfinite

end DifferentialGeometry.Geometry

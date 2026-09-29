import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry (SmoothRiemannianMetric)

universe u

noncomputable def riemannianBallVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (p : M) (r : ℝ) : ℝ :=
  ((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) (M := M) g)
    (DifferentialGeometry.riemannianBallOf (I := (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))) g p r)).toReal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

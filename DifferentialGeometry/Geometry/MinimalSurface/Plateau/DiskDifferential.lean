import DifferentialGeometry.Geometry.Measure.Area.Manifold
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong










noncomputable section

open Bundle Manifold DifferentialGeometry MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def diskMapPartial (U : ℂ → M) (z v : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v



def DiskMapConformalAt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : Prop :=
  g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) = 0 ∧
    g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) =
      g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)



def diskMapCovariantPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z v w : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  covDerivAlong g (fun t : ℝ => U (z + t • v))
    (fun t : ℝ => diskMapPartial U (z + t • v) w) 0



def diskMapTension (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  diskMapCovariantPartial g U z 1 1 + diskMapCovariantPartial g U z Complex.I Complex.I


def diskMapEnergyDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : ℝ :=
  (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
    g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) / 2


def DiskSmoothInterior (u : C(closedDisk, M)) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.ball 0 1)



def DiskSmoothUpToBoundary (u : C(closedDisk, M)) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.closedBall 0 1)

end DifferentialGeometry.Geometry

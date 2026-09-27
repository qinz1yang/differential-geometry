import DifferentialGeometry.Geometry.Measure.Area.Manifold
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling



noncomputable section

open Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]



def standardEuclideanMetric (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    SmoothRiemannianMetric 𝓘(ℝ, F) F where
  inner := (riemannianMetricVectorSpace F).inner
  symm := (riemannianMetricVectorSpace F).symm
  pos := (riemannianMetricVectorSpace F).pos
  isVonNBounded := (riemannianMetricVectorSpace F).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top

theorem riemannianAreaDensity_standardEuclideanMetric (u : ℂ → F) (z : ℂ) :
    riemannianAreaDensity (standardEuclideanMetric F) u z = euclideanAreaDensity u z := by
  simp only [riemannianAreaDensity, mfderiv_eq_fderiv]
  rfl

theorem riemannianArea_standardEuclideanMetric (u : ℂ → F) (s : Set ℂ) :
    riemannianArea (standardEuclideanMetric F) u s = euclideanArea u s := by
  simp only [riemannianArea, riemannianAreaDensity_standardEuclideanMetric, euclideanArea]

theorem riemannianDiskArea_standardEuclideanMetric (u : closedDisk → F) :
    riemannianDiskArea (standardEuclideanMetric F) u = euclideanDiskArea u :=
  riemannianArea_standardEuclideanMetric _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_standardEuclideanMetric (x y : F) :
    DifferentialGeometry.riemannianEDistOf
      (standardEuclideanMetric F) x y = edist x y := by
  change Manifold.riemannianEDist 𝓘(ℝ, F) x y = edist x y
  exact (IsRiemannianManifold.out x y).symm

end DifferentialGeometry.Geometry

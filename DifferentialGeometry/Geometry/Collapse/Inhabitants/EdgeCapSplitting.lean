import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapCarrier
/-! Genuine physical L2 distance and actual complete capped surface factor. -/

set_option autoImplicit false
noncomputable section
open Bundle
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open scoped Manifold ContDiff Topology
attribute [local instance] capExampleSigma capExampleMetricSpace capExampleEDist
  capExampleDist capExampleUniform capExampleEMetric capExamplePseudo capExampleBundle
  capExampleRiemannian capExampleContinuous capExampleComplete capExampleProper capExampleDimension

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapSplitting

def physicalLine (y : E2) (t : ℝ) : E3 := capProductCoordinates (t, y)
theorem physicalLine_isometry (y : E2) : Isometry (physicalLine y) := by
  intro s t
  change riemannianEDistOf capExampleMetric (physicalLine y s) (physicalLine y t) = edist s t
  simp only [capExampleMetric, capThreeMetric, physicalLine,
    riemannianEDistOf_pullbackMetricCross, Diffeomorph.symm_apply_apply]
  rw [capProductMetric, riemannianEDistOf_prod_left]
  rw [show euclideanMetric (E := ℝ) = standardEuclideanMetric ℝ from rfl,
    riemannianEDistOf_standardEuclideanMetric]

theorem physicalLine_calibrated (y : E2) (t : ℝ) :
    Comparison.Toponogov.lineCoordinate capExampleAxis (physicalLine y t) =
      Comparison.Toponogov.lineCoordinate capExampleAxis (physicalLine y 0) + t := by
  rw [← capExample_canonical_coord, ← capExample_canonical_coord]
  simp [physicalLine, capThreeCoord]

theorem physical_squared_distance (y z : E2) (s t : ℝ) :
    dist (physicalLine y s) (physicalLine z t) ^ 2 = (s - t) ^ 2 +
      dist (physicalLine y 0) (physicalLine z 0) ^ 2 := by
  have h := Comparison.Toponogov.sq_dist_calibrated_lines capExample_fourPoint
    capExample_axis_isometry (physicalLine_isometry y) (physicalLine_isometry z)
    (physicalLine_calibrated y) (physicalLine_calibrated z) s t
  simpa [← capExample_canonical_coord, physicalLine, capThreeCoord] using h

local instance capSurfaceSigma : SigmaCompactSpace E2 := inferInstance
local instance capSurfaceMetricSpace : MetricSpace E2 :=
  inducedMetricSpace (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
local instance capSurfaceEDist : EDist E2 := capSurfaceMetricSpace.toEDist
local instance capSurfaceDist : Dist E2 := capSurfaceMetricSpace.toDist
local instance capSurfaceUniform : UniformSpace E2 := capSurfaceMetricSpace.toUniformSpace
local instance capSurfaceEMetric : PseudoEMetricSpace E2 :=
  capSurfaceMetricSpace.toPseudoEMetricSpace
local instance capSurfacePseudo : PseudoMetricSpace E2 := capSurfaceMetricSpace.toPseudoMetricSpace

theorem physical_zero_distance (y z : E2) :
    dist (physicalLine y 0) (physicalLine z 0) = dist y z := by
  have he : edist (physicalLine y 0) (physicalLine z 0) = edist y z := by
    change riemannianEDistOf capExampleMetric (physicalLine y 0) (physicalLine z 0) =
      riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) y z
    simp only [capExampleMetric, capThreeMetric, physicalLine,
      riemannianEDistOf_pullbackMetricCross, Diffeomorph.symm_apply_apply]
    exact riemannianEDistOf_prod_right _ _ 0 y z
  have hr := congrArg ENNReal.toReal he
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hr

theorem physical_L2_distance (a b : ℝ × E2) :
    dist (capProductCoordinates a) (capProductCoordinates b) =
      dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) := by
  have h := physical_squared_distance a.2 b.2 a.1 b.1
  rw [physical_zero_distance] at h
  have hp : dist (WithLp.toLp 2 a) (WithLp.toLp 2 b) =
      Real.sqrt (dist a.1 b.1 ^ 2 + dist a.2 b.2 ^ 2) := by
    rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  rw [hp, Real.dist_eq, sq_abs]
  apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  exact h

local instance capSurfaceBundle : RiemannianBundle (TangentSpace (𝓡 2) : E2 → Type _) :=
  ⟨(scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).toRiemannianMetric⟩
local instance capSurfaceRiemannian : IsRiemannianManifold (𝓡 2) E2 :=
  inducedMetricSpace_isRiemannianManifold (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
local instance capSurfaceContinuous :
    IsContinuousRiemannianBundle E2 (TangentSpace (𝓡 2) : E2 → Type _) :=
  isContinuousRiemannianBundle_of_smoothRiemannianMetric
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
local instance capSurfaceComplete : CompleteSpace E2 :=
  (scaledCapComplete capExampleEpsilon capExampleEpsilon_pos).complete
local instance capSurfaceProper : ProperSpace E2 :=
  inducedMetricSpace_properSpace_of_riemannianMetricComplete
    (scaledCapComplete capExampleEpsilon capExampleEpsilon_pos)

theorem capSurfaceMetricNorm : IsMetricNorm
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) :=
  isMetricNorm_of_smoothRiemannianMetric _

theorem capSurface_sectional (x : E2) :
    SectionalBoundedBelowAt (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) x 0 := by
  intro u v
  simpa only [zero_mul] using scaledCapRm capExampleEpsilon capExampleEpsilon_pos x u v

theorem capSurface_orientation : Nonempty (ManifoldOrientation (𝓡 2) E2 2) := surfaceOrientation

end DifferentialGeometry.Geometry.Collapse.EdgeCapSplitting

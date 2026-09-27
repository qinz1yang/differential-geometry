import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open scoped Bundle

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance cylinderSphereTwoFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

def cylinderReferenceMetric (s : ℝ) : SmoothRiemannianMetric IC Cylinder :=
  cylinderMetric (I := I2)
    (scaleMetric (I := I2) (max (2 * (1 - s)) 1)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))

theorem cylinderReferenceMetric_inner (s : ℝ) (hs : s ≤ 0) (y : Cylinder)
    (v w : TangentSpace IC y) :
    (cylinderReferenceMetric s).inner y v w =
      2 * (1 - s) *
        inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 v.1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 w.1)
      + v.2 * w.2 := by
  have hmax : max (2 * (1 - s)) 1 = 2 * (1 - s) := by
    apply max_eq_left
    linarith
  simp only [cylinderReferenceMetric, cylinderMetric_inner, hmax]
  congr 1

theorem cylinderReferenceMetric_zero_inner (y : Cylinder) (v w : TangentSpace IC y) :
    (cylinderReferenceMetric 0).inner y v w =
      2 * inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 v.1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 w.1)
      + v.2 * w.2 := by
  simpa using cylinderReferenceMetric_inner 0 le_rfl y v w

theorem CylinderReference.metric_zero_eq_roundCylinder (C : CylinderReference) :
    C.metric 0 = DifferentialGeometry.Geometry.Metric.roundCylinderMetric
      (E := ThreeSpace) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [C.inner_eq 0 le_rfl, DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner]
  norm_num
  rfl


theorem cylinderReferenceMetric_scalar (s : ℝ) (hs : s ≤ 0) (y : Cylinder) :
    metricScalarAt (cylinderReferenceMetric s) y = (1 - s)⁻¹ := by
  have hmax : max (2 * (1 - s)) 1 = 2 * (1 - s) := by
    apply max_eq_left
    linarith
  have hround : metricScalarAt (I := I2)
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) y.1 = 2 := by
    have h := metricScalarAt_of_constant_sectional
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) y.1 1
      (fun u v => by
        rw [roundMetric_sec_value (E := EuclideanSpace ℝ (Fin 3)) (n := 2) y.1 u v, one_mul]
        ring)
    rw [h, finrank_euclideanSpace_fin]
    norm_num
  rw [cylinderReferenceMetric, cylinderMetric, metricScalarAt_productMetric,
    metricScalarAt_scaleMetric, hmax, hround,
    metricScalarAt_eq_zero_of_finrank_le_one _ (by simp) y.2, add_zero]
  field_simp

theorem cylinderReferenceMetric_zero_scalar (y : Cylinder) :
    metricScalarAt (cylinderReferenceMetric 0) y = 1 := by
  simpa using cylinderReferenceMetric_scalar 0 le_rfl y

def cylinderReference : CylinderReference where
  metric := cylinderReferenceMetric
  inner_eq := fun s hs y v w => cylinderReferenceMetric_inner s hs y v w

theorem nonempty_cylinderReference : Nonempty CylinderReference :=
  ⟨cylinderReference⟩

theorem cylinderReferenceMetric_scalar_pos (s : ℝ) (hs : s ≤ 0) (y : Cylinder) :
    0 < metricScalarAt (cylinderReferenceMetric s) y := by
  rw [cylinderReferenceMetric_scalar s hs y]
  exact inv_pos.mpr (by linarith)

theorem cylinderReferenceMetric_zero_ne_neg_one (y : Cylinder) :
    cylinderReferenceMetric 0 ≠ cylinderReferenceMetric (-1) := by
  intro h
  have h1 : metricScalarAt (cylinderReferenceMetric 0) y = 1 :=
    cylinderReferenceMetric_zero_scalar y
  have h2 : metricScalarAt (cylinderReferenceMetric (-1)) y = 1 / 2 := by
    rw [cylinderReferenceMetric_scalar (-1) (by norm_num) y]
    norm_num
  rw [h] at h1
  rw [h1] at h2
  norm_num at h2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

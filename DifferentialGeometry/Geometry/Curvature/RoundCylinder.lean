import DifferentialGeometry.Geometry.Curvature.Cylinder
import DifferentialGeometry.Geometry.Curvature.RoundSphere
import DifferentialGeometry.Geometry.Curvature.ScalarTrace
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem ricciTensor_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    ricciTensor (roundCylinderMetric (E := E) (n := n)) x v w =
      ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 := by
  exact (ricciTensor_cylinderMetric _ x v w).trans
    ((congrArg (fun R ↦ R v.1 w.1) (ricciTensor_scaleMetric
      (roundMetric (E := E) (n := n)) 2 (by norm_num) x.1)).trans
        (ricciTensor_roundSphere x.1 v.1 w.1))

theorem ricciSharp_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    ricciSharp (roundCylinderMetric (E := E) (n := n)) x v =
      ((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ)) := by
  let g := roundCylinderMetric (E := E) (n := n)
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq g
  intro w
  rw [inner_ricciSharp, ricciTensor_roundCylinder]
  change _ = (cylinderMetric (scaleMetric 2 (by norm_num)
    (roundMetric (E := E) (n := n)))).inner x
      ((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ)) w
  have hi := cylinderMetric_inner
    (scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))) x
    (((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ))) w
  rw [hi]
  change ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 =
    2 * (roundMetric (E := E) (n := n)).inner x.1 ((((n : ℝ) - 1) / 2) • v.1) w.1 +
      0 * w.2
  have hs := congrArg
    (fun L : TangentSpace (𝓡 n) x.1 →L[ℝ] ℝ ↦ L w.1)
    (((roundMetric (E := E) (n := n)).inner x.1).map_smul (((n : ℝ) - 1) / 2) v.1)
  change (roundMetric (E := E) (n := n)).inner x.1
      ((((n : ℝ) - 1) / 2) • v.1) w.1 =
    (((n : ℝ) - 1) / 2) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 at hs
  linear_combination (norm := ring!) -2 * hs

theorem metricScalarAt_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricScalarAt (roundCylinderMetric (E := E) (n := n)) x =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) := ⟨by simp⟩
  have he : ((ricciSharp (roundCylinderMetric (E := E) (n := n)) x).toLinearMap :
      (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) =
      LinearMap.prodMap ((((n : ℝ) - 1) / 2) •
        (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
        (0 : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro v
    exact ricciSharp_roundCylinder x v
  have ht := congrArg (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) he
  refine (metricScalar_eq_trace_ricciSharp _ x).trans (ht.trans ?_)
  rw [LinearMap.trace_prodMap', map_smul, LinearMap.trace_id, map_zero]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, add_zero]
  ring

end Poincare.Geometry.Curvature

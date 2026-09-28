import DifferentialGeometry.Geometry.Metric.RestrictedCylinderAxis
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Geometry.Metric.LengthPerturbation

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Metric

theorem restricted_roundCylinder_height_differential_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (x : O) (w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
    |mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x w - 1| ≤
      Real.sqrt (((roundCylinderMetric (E := E) (n := 2)).restrictOpen O).inner x
        (w - restrictedCylinderAxis O x) (w - restrictedCylinderAxis O x)) := by
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen O
  let v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x := restrictedCylinderAxis O x
  have hv : gRef.inner x v v = 1 := restrictedCylinderAxis_unit gS O x
  have h := SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic gRef x v (w - v)
  rw [hv, Real.sqrt_one, one_mul, map_sub, hv] at h
  have he : gRef.inner x v w =
      mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x w :=
    restrictedCylinderAxis_inner gS O x w
  rwa [he] at h

end DifferentialGeometry.Geometry.Metric

import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.Scaling

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry

namespace Poincare.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def roundCylinderMetric :
    SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) :=
  cylinderMetric (scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n)))

@[simp] theorem roundCylinderMetric_inner (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    (roundCylinderMetric (E := E) (n := n)).inner x v w =
      2 * inner ℝ (dIncl x.1 v.1) (dIncl x.1 w.1) + v.2 * w.2 := by
  rw [roundCylinderMetric, cylinderMetric_inner]
  exact congrArg (fun a : ℝ ↦ 2 * a + v.2 * w.2) (roundMetric_inner x.1 v.1 w.1)

end Poincare.Geometry.Metric

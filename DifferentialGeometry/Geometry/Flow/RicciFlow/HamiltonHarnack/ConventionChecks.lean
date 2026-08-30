import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.CurvatureBlock

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry
open scoped Manifold ContDiff Matrix

private theorem normalizedWedge_fin_two :
    normalizedWedge
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 2 => Real) 0)
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 2 => Real) 1)
        ![![1, 0], ![0, 1]] = (1 / 2 : Real) := by
  rw [normalizedWedge_apply]
  change (1 / 2 : Real) * (1 * 1 - 0 * 0) = 1 / 2
  ring

private theorem normalizedWedge_fin_three :
    normalizedWedge
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 3 => Real) 0)
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin 3 => Real) 2)
        ![![1, 0, 0], ![0, 0, 1]] = (1 / 2 : Real) := by
  rw [normalizedWedge_apply]
  change (1 / 2 : Real) * (1 * 1 - 0 * 0) = 1 / 2
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

omit [FiniteDimensional Real E] in
private theorem roundMetric_curvature_pos_of_orthonormal
    (x : Metric.sphere (0 : E) 1)
    (X Y : TangentSpace (𝓡 n) x)
    (hXX : (roundMetric (E := E) (n := n)).inner x X X = 1)
    (hYY : (roundMetric (E := E) (n := n)).inner x Y Y = 1)
    (hXY : (roundMetric (E := E) (n := n)).inner x X Y = 0) :
    0 < Geometry.Curvature.metricRm04StdAt
      (roundMetric (E := E) (n := n)) x X Y Y X := by
  rw [roundMetric_sec_value, hXX, hYY, hXY]
  norm_num

end DifferentialGeometry.PDE.RicciFlow

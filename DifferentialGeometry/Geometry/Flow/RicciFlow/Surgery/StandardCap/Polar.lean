import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Metric.RoundCylinder

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Sphere2 := Metric.sphere (0 : E3) 1

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem metric_polar_pullback (q : Sphere2 × ℝ) (hq : 0 < q.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (euclideanPolarMap q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q w) =
      warpingFunction q.2 ^ 2 * (roundMetric (E := E3) (n := 2)).inner q.1 v.1 w.1 +
        v.2 * w.2 := by
  rw [euclideanPolarMap_mfderiv, euclideanPolarMap_mfderiv]
  change metric.inner (q.2 • (q.1 : E3))
    (v.2 • (q.1 : E3) + q.2 • dIncl q.1 v.1)
    (w.2 • (q.1 : E3) + q.2 • dIncl q.1 w.1) = _
  rw [metric_inner_polar (norm_eq_of_mem_sphere q.1)
    (dIncl_orth q.1 v.1) (dIncl_orth q.1 w.1) hq, add_comm]
  exact congrArg (fun t : ℝ => warpingFunction q.2 ^ 2 * t + v.2 * w.2)
    (roundMetric_inner q.1 v.1 w.1).symm

theorem metric_polar_pullback_cylindrical (q : Sphere2 × ℝ)
    (hq : transitionEnd ≤ q.2) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (euclideanPolarMap q)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [metric_polar_pullback q (transitionEnd_pos.trans_le hq),
    warpingFunction_eq_sqrt_two hq, Real.sq_sqrt (by norm_num),
    roundCylinderMetric_inner]
  exact congrArg (fun t : ℝ => 2 * t + v.2 * w.2) (roundMetric_inner q.1 v.1 w.1)

end DifferentialGeometry.PDE.RicciFlow.StandardCap

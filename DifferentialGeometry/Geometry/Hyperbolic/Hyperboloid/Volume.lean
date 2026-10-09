import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianIsometry
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Measure.LocalIsometry

open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : MeasurableSpace (Hyperboloid E) := borel (Hyperboloid E)
private local instance : BorelSpace (Hyperboloid E) := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_eq_of_center (x y : Hyperboloid E) (r : ℝ) :
    riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric (Metric.ball x r) =
      riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric (Metric.ball y r) := by
  let e : Hyperboloid E ≃ᵢ Hyperboloid E := (boost x).symm.trans (boost y)
  let D := isometryDiffeomorph e (n := ∞)
  have hmetric : ∀ z : Hyperboloid E, ∀ u v : TangentSpace 𝓘(ℝ, E) z,
      riemannianMetric.inner z u v =
        riemannianMetric.inner (D z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z u)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z v) := by
    intro z u v
    exact (riemannianMetric_inner_mfderiv_isometryEquiv e z u v).symm
  have hv := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S := Metric.ball x r) riemannianMetric riemannianMetric D D.isLocalDiffeomorph D.injective hmetric
    Metric.isOpen_ball.measurableSet
  have himage : D '' Metric.ball x r = Metric.ball y r := by
    change (e : Hyperboloid E → Hyperboloid E) '' Metric.ball x r = Metric.ball y r
    have hx : (boost x).symm x = origin := by
      simpa only [boost_origin] using (boost x).symm_apply_apply origin
    have he : e x = y := by
      change boost y ((boost x).symm x) = y
      rw [hx, boost_origin]
    rw [e.image_ball, he]
  rw [himage] at hv
  exact hv

theorem riemannianVolumeMeasure_ball_pos (x : Hyperboloid E) {r : ℝ} (hr : 0 < r) :
    0 < riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric (Metric.ball x r) := by
  let _ := Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure (riemannianMetric (E := E))
  exact Metric.measure_ball_pos
    (riemannianVolumeMeasure 𝓘(ℝ, E) (Hyperboloid E) riemannianMetric) x hr

end DifferentialGeometry.Hyperboloid

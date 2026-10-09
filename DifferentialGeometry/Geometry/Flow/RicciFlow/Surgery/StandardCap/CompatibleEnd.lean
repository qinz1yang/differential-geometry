import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis
open scoped Manifold

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

theorem sectionalCurvature_conformalChart_pos (q : S2 × ℝ) (hq : q.2 < 0)
    (u v : E3)
    (hplane : metric.inner (conformalChart q : E3) u u *
      metric.inner (conformalChart q : E3) v v -
      (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0) :
    0 < sectionalCurvature metric (conformalChart q : E3) u v := by
  apply sectionalCurvature_pos _ u v hplane
  rw [conformalChart_norm]
  exact conformalRadius_lt_transitionEnd hq

theorem exists_compatible_end_collar {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ 2 * A < 1 / 2 ∧
      (∀ q : S2 × ℝ, q.2 ∈ Ico (-2 * A) 0 → ∀ u v : E3,
        metric.inner (conformalChart q : E3) u u *
          metric.inner (conformalChart q : E3) v v -
          (metric.inner (conformalChart q : E3) u v) ^ 2 ≠ 0 →
        0 < sectionalCurvature metric (conformalChart q : E3) u v) ∧
      (∀ z ∈ Ioo (-A) 0,
        conformalFactor z < 0 ∧ 0 < deriv conformalFactor z ∧
          deriv (deriv conformalFactor) z < 0 ∧
          max |conformalFactor z| |deriv conformalFactor z| ≤
            ε * (-deriv (deriv conformalFactor) z)) ∧
      intervalDerivativeNorm contDiff_conformalFactor 2 (-A) 0 < ε := by
  obtain ⟨A, hA, hsmall, _, hsigns, hnorm⟩ := exists_conformal_collar hε
  exact ⟨A, hA, hsmall, fun q hq u v hp =>
    sectionalCurvature_conformalChart_pos q hq.2 u v hp, hsigns, hnorm⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap

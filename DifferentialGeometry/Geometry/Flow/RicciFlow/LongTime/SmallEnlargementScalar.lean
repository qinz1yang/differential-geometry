import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicCurvature
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Set
open scoped ENNReal

namespace GC.LongTime
universe u

theorem hasSmallParabolicCurvature.scalar_abs_le
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r : ℝ}
    (h : hasSmallParabolicCurvature H t p r)
    {q : (H.stageAt t).Carrier}
    (hq : q ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r) :
    |metricScalarAt (H.stageMetric (H.activeStage t) t) q| ≤ 3 * (r ^ 2)⁻¹ := by
  obtain ⟨hr, a, hat, _, htrace⟩ := h
  obtain ⟨B, hB⟩ := htrace q hq
  have hbound := hB.1 t hat le_rfl
  rw [B.endpoint_eq] at hbound
  have hscalar := sq_mul_scalar_abs_le_of_rm_bound
    (H.stageMetric (H.activeStage t) t) q hbound
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hscalar
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hscalar
  norm_num at hscalar
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

end GC.LongTime

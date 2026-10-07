import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X
import DifferentialGeometry.Geometry.Collapse.ScaleInvariance

/-!
# CX-SPINE G5: ball-volume lower bounds on the actual rescaled history

The same coefficient `κ` controls the ball of radius `r` at the original time
and the ball of radius `r / sqrt c` at `rescaleTime_P6X`, with center transported
by `castRescale_P6X`. The proof uses the actual stage metric rescaling and the
active-stage/point equalities, followed by `le_ballVolume_scaleMetric_iff`.
There is no positivity assumption on `r` or `κ`, and no new noncollapsing supply.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

/-- The lower ball-volume bound is equivalent at the actual corresponding times
and centers of a history and its parabolic rescaling, with the same coefficient. -/
theorem le_ballVolume_castRescale_iff_CXSP {H : RetainedCoreHistory.{u}}
    {c : ℝ} (hc : 0 < c) {v : Icc (0 : ℝ) H.toHistory.horizon}
    {p : (H.toHistory.stageAt v).Carrier} {κ r : ℝ} :
    ENNReal.ofReal (κ * (r / Real.sqrt c) ^ 3) ≤
        ballVolume ((H.rescale_P6N c hc).toHistory.stageMetric
          ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
          (H.rescaleTime_P6X hc v)) (H.castRescale_P6X hc v p) (r / Real.sqrt c) ↔
      ENNReal.ofReal (κ * r ^ 3) ≤
        ballVolume (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p r := by
  have hmetric := (H.rescale_P6N_stageMetric c hc
    ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
    (H.rescaleTime_P6X hc v)).trans
    (congrArg (fun t => scaleMetric c⁻¹ (inv_pos.mpr hc)
      (H.toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v)) t))
      (H.mul_rescaleTime_P6X hc v))
  rw [hmetric]
  have hradius : r / Real.sqrt c = Real.sqrt c⁻¹ * r := by
    rw [Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hradius]
  refine (le_ballVolume_scaleMetric_iff hdim c⁻¹ (inv_pos.mpr hc)
    (g := H.toHistory.stageMetric
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v)) v)
    (p := H.castRescale_P6X hc v p) (w := κ) (t := r)).trans ?_
  exact carrier_transfer_P6X (S := H.stage)
    (Pr := fun j z => ENNReal.ofReal (κ * r ^ 3) ≤
      ballVolume (H.toHistory.stageMetric j v) z r)
    (H.activeStage_rescaleTime_P6X hc v) (H.heq_castRescale_P6X hc v p)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

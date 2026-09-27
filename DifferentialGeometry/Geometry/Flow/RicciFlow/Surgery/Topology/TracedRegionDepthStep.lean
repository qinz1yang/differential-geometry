import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionBackwardStep

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature (metricScalarAt)
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)

theorem scalar_le_two_mul_along_backward_traces_of_depth_step
    {Ctime : ℝ≥0} {qcan M : ℝ} {u' u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 0 < M) (hqcan : qcan ≤ M) (htime : Ctime * M * ((u : ℝ) - u') ≤ 1 / 2)
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hU : ∀ x ∈ U, ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
        (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
        (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
            (H.toHistory.activeStage_mono hvt)) ≤ M) :
    ∀ x ∈ U, ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u' ≤ w) (hwt : w ≤ t)
      (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
      (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * M := by
  intro x hx w hu'w hwt B v hwv hvt
  by_cases huw : u ≤ w
  · exact (hU x hx w huw hwt B v hwv hvt).trans (by linarith)
  have hwu : w ≤ u := (lt_of_not_ge huw).le
  have hdepth : Ctime * M * ((u : ℝ) - w) ≤ 1 / 2 := by
    have hw : (u' : ℝ) ≤ w := hu'w
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg hM.le
    nlinarith
  exact H.scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_above hwu hut B hslabs hcurrent
    hfinal hM hqcan (fun v' hwv' hv't huv' => hU x hx u le_rfl hut
      (B.restrictFirst (H.toHistory.activeStage_mono hwu) (H.toHistory.activeStage_mono hut))
      v' huv' hv't) hdepth v hwv hvt

theorem scalar_le_along_backward_traces_at_scale_of_depth_step
    {Ctime : ℝ≥0} {qcan R Q T T' : ℝ} {u' u t : Icc (0 : ℝ) H.toHistory.horizon}
    (hR : 0 < R) (hQ : 0 < Q) (hstep : 4 * Ctime * Q * (T' - T) ≤ 1)
    (hu : (u : ℝ) = t - T / R) (hu' : (u' : ℝ) = t - T' / R) (hut : u ≤ t)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hqcan : qcan ≤ 2 * (Q * R))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hU : ∀ x ∈ U, ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
        (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
        (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R)) :
    ∀ x ∈ U, ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u' ≤ w) (hwt : w ≤ t)
      (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
      (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
          (H.toHistory.activeStage_mono hvt)) ≤ 2 * ((2 * Q) * R) := by
  have hgap : (u : ℝ) - u' = (T' - T) / R := by
    rw [hu, hu']
    ring
  have htime : Ctime * (2 * (Q * R)) * ((u : ℝ) - u') ≤ 1 / 2 := by
    rw [hgap]
    have heq : (Ctime : ℝ) * (2 * (Q * R)) * ((T' - T) / R) = (4 * Ctime * Q * (T' - T)) / 2 := by
      field_simp
      ring
    rw [heq]
    linarith
  have h := H.scalar_le_two_mul_along_backward_traces_of_depth_step hut hslabs hcurrent
    hfinal (by positivity) hqcan htime U hU
  intro x hx w hu'w hwt B v hwv hvt
  have hb := h x hx w hu'w hwt B v hwv hvt
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

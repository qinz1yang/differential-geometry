import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BallRescaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP

set_option autoImplicit false

/-!
# CX-SPINE G5：实际受控球测试的 κ 下界重标度

固定切片与中心上，所有测试半径及其完整抛物受控球一起搬运。
κ 原样保留，测试上限 σ 除以 √c；此处不制造新的非塌缩供给。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

/-- 实际历史测试球的 κ 下界与缩放后的全部测试严格等价。 -/
theorem tested_kappa_rescale_iff_CXSP {H : RetainedCoreHistory.{u}}
    {c : ℝ} (hc : 0 < c) {t : Icc (0 : ℝ) H.toHistory.horizon}
    {p : (H.toHistory.stageAt t).Carrier} {κ σ : ℝ} :
    (∀ b : ℝ, 0 < b → b ≤ σ / Real.sqrt c →
      (H.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall
        (H.rescaleTime_P6X hc t) (H.castRescale_P6X hc t p) b →
      ENNReal.ofReal (κ * b ^ 3) ≤
        ballVolume ((H.rescale_P6N c hc).toHistory.stageMetric
          ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t))
          (H.rescaleTime_P6X hc t)) (H.castRescale_P6X hc t p) b) ↔
    (∀ r : ℝ, 0 < r → r ≤ σ → H.toHistory.isParabolicallyRmControlledBall t p r →
      ENNReal.ofReal (κ * r ^ 3) ≤
        ballVolume (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  constructor
  · intro hN r hr hrσ hball
    apply (le_ballVolume_castRescale_iff_CXSP (H := H) hc (v := t) (p := p) (κ := κ) (r := r)).mp
    exact hN (r / Real.sqrt c) (div_pos hr hs)
      ((div_le_div_iff_of_pos_right hs).mpr hrσ)
      ((isParabolicallyRmControlledBall_rescale_iff_CXSP hc).mpr hball)
  · intro hO b hb hbσ hball
    have hradius : b * Real.sqrt c / Real.sqrt c = b :=
      mul_div_cancel_right₀ b hs.ne'
    have hOcontrol : H.toHistory.isParabolicallyRmControlledBall t p
        (b * Real.sqrt c) :=
      (isParabolicallyRmControlledBall_rescale_iff_CXSP hc).mp
        (by simpa only [hradius] using hball)
    have hv := hO (b * Real.sqrt c) (mul_pos hb hs) ((le_div_iff₀ hs).mp hbσ) hOcontrol
    have hN := (le_ballVolume_castRescale_iff_CXSP (H := H) hc (v := t)
      (p := p) (κ := κ) (r := b * Real.sqrt c)).mpr hv
    simpa only [hradius] using hN

/-- P6AnchorKappaP6M 所需的真实 trace-local κ 供给随整史重标度搬运。 -/
theorem traced_kappa_rescale_CXSP (H : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier)
    {κ ρ Rad θ : ℝ}
    (hK : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p Rad,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hvt : v ≤ t), (t : ℝ) - θ ≤ v →
      ∀ A : BackwardPointTrace H.toHistory (H.toHistory.activeStage v)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hvt) x,
      ∀ r : ℝ, 0 < r → r ≤ ρ → H.toHistory.isParabolicallyRmControlledBall v
        (A.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)) r →
      ENNReal.ofReal (κ * r ^ 3) ≤
        ballVolume (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) le_rfl (H.toHistory.activeStage_mono hvt)) r) :
    let H' := (H.rescale_P6N c hc).toHistory
    let t' := H.rescaleTime_P6X hc t
    ∀ x ∈ riemannianBallOf (H'.stageMetric (H'.activeStage t') t')
      (H.castRescale_P6X hc t p) (Rad / Real.sqrt c),
      ∀ (v : Icc (0 : ℝ) H'.horizon) (hvt : v ≤ t'), (t' : ℝ) - θ / c ≤ v →
      ∀ B : BackwardPointTrace H' (H'.activeStage v) (H'.activeStage t')
        (H'.activeStage_mono hvt) x,
      ∀ r : ℝ, 0 < r → r ≤ ρ / Real.sqrt c → H'.isParabolicallyRmControlledBall v
        (B.point (H'.activeStage v) le_rfl (H'.activeStage_mono hvt)) r →
      ENNReal.ofReal (κ * r ^ 3) ≤ ballVolume (H'.stageMetric (H'.activeStage v) v)
        (B.point (H'.activeStage v) le_rfl (H'.activeStage_mono hvt)) r := by
  intro H' t' x' hx' v' hvt' htime' B
  obtain ⟨x, rfl⟩ := H.castRescale_surjective_CXSP hc t x'
  obtain ⟨v, rfl⟩ : ∃ v, H.rescaleTime_P6X hc v = v' :=
    ⟨H.unscaleTime_P6X hc v', H.rescale_unscaleTime_P6X hc v'⟩
  have hvt : v ≤ t := (div_le_div_iff_of_pos_right hc).mp
    (show (v : ℝ) / c ≤ (t : ℝ) / c from hvt')
  have htime : (t : ℝ) - θ ≤ v := (div_le_div_iff_of_pos_right hc).mp (by
    rw [sub_div]
    exact htime')
  let A := H.unscaleTrace_CXSP hc hvt B
  have hpoint : B.point (H'.activeStage (H.rescaleTime_P6X hc v)) le_rfl
      (H'.activeStage_mono hvt') =
      H.castRescale_P6X hc v (A.point (H.toHistory.activeStage v) le_rfl
        (H.toHistory.activeStage_mono hvt)) := by
    rw [← H.rescaleTrace_unscaleTrace_CXSP hc hvt B]
    exact H.rescaleTrace_point_at_time_CXSP hc hvt A v le_rfl hvt
  rw [hpoint]
  exact (tested_kappa_rescale_iff_CXSP hc).mpr
    (hK x ((ball_castRescale_iff_CXSP hc).mp hx') v hvt htime A)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

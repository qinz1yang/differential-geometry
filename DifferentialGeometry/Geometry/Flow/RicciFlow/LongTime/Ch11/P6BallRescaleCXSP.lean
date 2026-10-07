import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ControlledRescaleCXSP

set_option autoImplicit false

/-!
# CX-SPINE G5：实际历史抛物受控球的双向重标度

球中所有点、完整 backward trace、时间深度与 crossed-terminal 曲率同时搬运。
仅需正缩放因子；半径的正性由既有受控球谓词自身要求。
-/

noncomputable section

open Set DifferentialGeometry
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

variable (H : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- 对应切片的 canonical point cast 是满射，故不会漏掉重标度球中的测试点。 -/
theorem castRescale_surjective_CXSP (t : Icc (0 : ℝ) H.toHistory.horizon) :
    Function.Surjective (H.castRescale_P6X hc t) := by
  intro y
  let x : (H.toHistory.stageAt t).Carrier :=
    cast (congrArg (fun j => (H.stage j).Carrier)
      (H.activeStage_rescaleTime_P6X hc t)) y
  refine ⟨x, eq_of_heq ?_⟩
  exact (H.heq_castRescale_P6X hc t x).trans (cast_heq _ _)

variable {H} in
/-- 对应球的精确双向成员关系；无须额外半径正性假设。 -/
theorem ball_castRescale_iff_CXSP {t : Icc (0 : ℝ) H.toHistory.horizon}
    {p x : (H.toHistory.stageAt t).Carrier} {r : ℝ} :
    H.castRescale_P6X hc t x ∈ riemannianBallOf
      ((H.rescale_P6N c hc).toHistory.stageMetric
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t))
        (H.rescaleTime_P6X hc t)) (H.castRescale_P6X hc t p) (r / Real.sqrt c) ↔
      x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r := by
  change riemannianEDistOf _ _ _ < _ ↔ riemannianEDistOf _ _ _ < _
  rw [H.edist_castRescale_P6X hc t p x]
  have hs : 0 < Real.sqrt c⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hc)
  have heq : ENNReal.ofReal (r / Real.sqrt c) =
      ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul hs.le, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hs).ne'
    ENNReal.ofReal_ne_top

private theorem radius_clock_rescale_CXSP {a t r c : ℝ} (hc : 0 < c) :
    a / c = t / c - (r / Real.sqrt c) ^ 2 ↔ a = t - r ^ 2 := by
  rw [div_pow, Real.sq_sqrt hc.le, ← sub_div]
  exact div_left_inj' hc.ne'

variable {H} in
/-- 完整抛物受控球在时间除以 c、半径除以 √c 下严格等价。 -/
theorem isParabolicallyRmControlledBall_rescale_iff_CXSP
    {t : Icc (0 : ℝ) H.toHistory.horizon} {p : (H.toHistory.stageAt t).Carrier} {r : ℝ} :
    (H.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall
      (H.rescaleTime_P6X hc t) (H.castRescale_P6X hc t p) (r / Real.sqrt c) ↔
      H.toHistory.isParabolicallyRmControlledBall t p r := by
  constructor
  · rintro ⟨hr, a', hat', hclock', htrace'⟩
    obtain ⟨a, rfl⟩ : ∃ a, H.rescaleTime_P6X hc a = a' :=
      ⟨H.unscaleTime_P6X hc a', H.rescale_unscaleTime_P6X hc a'⟩
    have hat : a ≤ t := (div_le_div_iff_of_pos_right hc).mp
      (show (a : ℝ) / c ≤ (t : ℝ) / c from hat')
    have hclock : (a : ℝ) = (t : ℝ) - r ^ 2 :=
      (radius_clock_rescale_CXSP hc).mp hclock'
    refine ⟨(div_pos_iff_of_pos_right (Real.sqrt_pos.mpr hc)).mp hr, a, hat, hclock, ?_⟩
    intro x hx
    obtain ⟨B, hB⟩ := htrace' (H.castRescale_P6X hc t x)
      ((ball_castRescale_iff_CXSP hc).mpr hx)
    let A := H.unscaleTrace_CXSP hc hat B
    refine ⟨A, (isRmControlled_rescaleTrace_iff_CXSP (H := H) hc (A := A) (r := r)).mp ?_⟩
    have hAB : H.rescaleTrace_CXSP hc hat A = B := H.rescaleTrace_unscaleTrace_CXSP hc hat B
    simpa only [hAB] using hB
  · rintro ⟨hr, a, hat, hclock, htrace⟩
    refine ⟨div_pos hr (Real.sqrt_pos.mpr hc), H.rescaleTime_P6X hc a,
      H.rescaleTime_mono_P6X hc hat, (radius_clock_rescale_CXSP hc).mpr hclock, ?_⟩
    intro x' hx'
    obtain ⟨x, rfl⟩ := H.castRescale_surjective_CXSP hc t x'
    obtain ⟨A, hA⟩ := htrace x ((ball_castRescale_iff_CXSP hc).mp hx')
    exact ⟨H.rescaleTrace_CXSP hc hat A,
      (isRmControlled_rescaleTrace_iff_CXSP (H := H) hc (A := A) (r := r)).mpr hA⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
